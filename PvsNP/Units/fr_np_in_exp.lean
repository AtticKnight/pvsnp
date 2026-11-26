import Mathlib
import PvsNP.Defs
import CookLevin

/-
Adapted from github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Universal/IM.lean,
  lean/PEqualNP/Library/Universal/Pair.lean,
  lean/PEqualNP/Library/Universal/Strings.lean,
  lean/PEqualNP/Library/Universal/SStep.lean,
  lean/PEqualNP/Library/Universal/Verify.lean,
  lean/PEqualNP/Defs/Base.lean,
  lean/PEqualNP/Defs/Classes.lean,
  lean/PEqualNP/Defs/ProofComplexity.lean,
  lean/PEqualNP/Defs/Search.lean,
  lean/PEqualNP/Library/Machines/Run.lean,
  lean/PEqualNP/Library/Machines/Transducer.lean,
  lean/PEqualNP/Library/Universal/LazyDefs.lean,
  lean/PEqualNP/Library/Universal/Compile.lean,
  lean/PEqualNP/Library/Machines/Compose.lean,
  lean/PEqualNP/Library/Machines/ComposeRun.lean,
  lean/PEqualNP/Library/Machines/FilterMap.lean,
  lean/PEqualNP/Library/Machines/TwoPass.lean,
  lean/PEqualNP/Library/Machines/First.lean,
  lean/PEqualNP/Library/Machines/FirstRun.lean,
  lean/PEqualNP/Library/Machines/FirstPoly.lean,
  lean/PEqualNP/Library/Machines/Pairing.lean,
  lean/PEqualNP/Library/Machines/AllTrue.lean,
  lean/PEqualNP/Library/Machines/LenLE.lean,
  lean/PEqualNP/Library/Machines/FirstG.lean,
  lean/PEqualNP/Library/Machines/FirstGRun.lean,
  lean/PEqualNP/Library/Machines/Mul.lean,
  lean/PEqualNP/Library/Machines/Clock.lean,
  lean/PEqualNP/Library/Machines/ConstList.lean,
  lean/PEqualNP/Library/L055.lean,
  lean/PEqualNP/Library/Machines/NormalForm.lean,
  lean/PEqualNP/Library/L045.lean,
  lean/PEqualNP/Library/Helpers/PolyExp.lean,
  lean/PEqualNP/Library/L048.lean,
  lean/PEqualNP/Library/Universal/Lazy.lean,
  lean/PEqualNP/Library/Machines/Iter.lean,
  lean/PEqualNP/Library/Machines/IterRun.lean,
  lean/PEqualNP/Library/Machines/IterMeasure.lean,
  lean/PEqualNP/Library/Universal/Prims.lean,
  lean/PEqualNP/Library/Universal/PrimsCPT.lean,
  lean/PEqualNP/Library/Universal/VerifyCPT.lean,
  lean/PEqualNP/Library/Universal/SStepCPT.lean,
  lean/PEqualNP/Library/Universal/LazyCPT.lean,
  lean/PEqualNP/Library/Universal/CompileBool.lean,
  lean/PEqualNP/Library/Machines/ExpPad.lean,
  lean/PEqualNP/Library/Machines/ComposeTime.lean,
  lean/PEqualNP/Library/Helpers/OutputLength.lean,
  lean/PEqualNP/Library/Universal/ExpHierarchy.lean,
  lean/PEqualNP/Library/Machines/ReduceNP.lean,
  lean/PEqualNP/Library/Universal/BruteForce.lean,
  lean/PEqualNP/Library/L014.lean.
MODIFIED from those files: joined here in that order, each in a section of its own, inside the
namespace PvsNP.Units.fr_np_in_exp (so every upstream name PEqualNP.X is PvsNP.Units.fr_np_in_exp.PEqualNP.X here);
the module header lines are dropped, the umbrella module PEqualNP.Defs is read as PEqualNP.Defs.Base and
PEqualNP.Defs.Classes, and the closing theorem after the namespace carries the upstream result
over to the campaign's definitions in PvsNP.Defs. Every upstream proof is as written upstream, except
mechanical rewrites the desk's file rules and the joining ask for: a reducible def is an abbrev,
each local notation is written out in full where it is used, a term line that opens with
add_le_add is put in parentheses, and a private name that another joined file also declares
carries the suffix _u<n> in its own file.
-/

namespace PvsNP.Units.fr_np_in_exp

-- upstream PEqualNP.Library.Universal.IM
section

namespace PEqualNP.Library.Universal

inductive Instr
  | push (k : ℕ) (tbl : List ℕ) (next : ℕ)
  | pop (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | peek (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | load (tbl : List ℕ) (next : ℕ)
  | branch (tbl : List ℕ) (next₁ next₂ : ℕ)
  | goto (tbl : List ℕ)
  | halt
  deriving DecidableEq, Repr

structure Cfg where
  pc : Option ℕ
  state : ℕ
  stk : List (List ℕ)
  deriving DecidableEq, Repr

def topIndex (st : List ℕ) : ℕ :=
  match st with
  | [] => 0
  | s :: _ => s + 1

def exec (i : Instr) (v : ℕ) (S : List (List ℕ)) : Cfg :=
  match i with
  | .push k tbl next => ⟨some next, v, S.set k (tbl.getD v 0 :: S.getD k [])⟩
  | .pop k tbl w next =>
    ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S.set k (S.getD k []).tail⟩
  | .peek k tbl w next => ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S⟩
  | .load tbl next => ⟨some next, tbl.getD v 0, S⟩
  | .branch tbl next₁ next₂ => ⟨some (if tbl.getD v 0 ≠ 0 then next₁ else next₂), v, S⟩
  | .goto tbl => ⟨some (tbl.getD v 0), v, S⟩
  | .halt => ⟨none, v, S⟩

def step (P : List Instr) (c : Cfg) : Cfg :=
  match c.pc with
  | none => c
  | some n =>
    match P[n]? with
    | none => ⟨none, c.state, c.stk⟩
    | some i => exec i c.state c.stk

structure Code where
  prog : List Instr
  nstk : ℕ
  pc₀ : ℕ
  state₀ : ℕ
  kin : ℕ
  kout : ℕ
  deriving DecidableEq, Repr

def Code.init (c : Code) (input : List ℕ) : Cfg :=
  ⟨some c.pc₀, c.state₀, (List.replicate c.nstk []).set c.kin input⟩

def Code.run (c : Code) (input : List ℕ) (t : ℕ) : Cfg :=
  (step c.prog)^[t] (c.init input)

def Code.outputsWithin (c : Code) (input : List ℕ) (t : ℕ) (out : List ℕ) : Prop :=
  (c.run input t).pc = none ∧ (c.run input t).stk.getD c.kout [] = out

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.Pair
section

namespace PEqualNP.Library.Universal

def un (n : ℕ) : List Bool := List.replicate n true

def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)

def unpairB (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a, b) := by
  have h1 : (pairB a b).takeWhile id = un a.length := by
    simp [pairB, un]
  have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
    simp [pairB, un]
  simp [unpairB, h1, h2, un]

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.Strings
section

namespace PEqualNP.Library.Universal

theorem un_succ (n : ℕ) : un (n + 1) = true :: un n := rfl

@[simp] theorem un_zero : un 0 = [] := rfl

@[simp] theorem un_length (n : ℕ) : (un n).length = n := by simp [un]

theorem un_inj {a b : ℕ} (h : un a = un b) : a = b := by
  have := congrArg List.length h
  simpa using this

def encN (n : ℕ) : List Bool := un (n + 1) ++ [false]

def encNs (l : List ℕ) : List Bool := l.flatMap encN

def encL (l : List ℕ) : List Bool := encNs l ++ [false]

def encLL (S : List (List ℕ)) : List Bool := S.flatMap encL

@[simp] theorem encNs_nil : encNs [] = [] := rfl

theorem encNs_cons (a : ℕ) (l : List ℕ) : encNs (a :: l) = encN a ++ encNs l := rfl

theorem encNs_append (l m : List ℕ) : encNs (l ++ m) = encNs l ++ encNs m := by
  simp [encNs]

@[simp] theorem encLL_nil : encLL [] = [] := rfl

theorem encLL_cons (a : List ℕ) (S : List (List ℕ)) :
    encLL (a :: S) = encNs a ++ false :: encLL S := by
  simp [encLL, encL]

theorem encLL_append (S T : List (List ℕ)) : encLL (S ++ T) = encLL S ++ encLL T := by
  simp [encLL]

def instrNs : Instr → List ℕ
  | .push k tbl next => [0, k, 0, next, 0] ++ tbl
  | .pop k tbl w next => [1, k, w, next, 0] ++ tbl
  | .peek k tbl w next => [2, k, w, next, 0] ++ tbl
  | .load tbl next => [3, 0, 0, next, 0] ++ tbl
  | .branch tbl next₁ next₂ => [4, 0, 0, next₁, next₂] ++ tbl
  | .goto tbl => [5, 0, 0, 0, 0] ++ tbl
  | .halt => [6, 0, 0, 0, 0]

def encP (P : List Instr) : List Bool := encLL (P.map instrNs)

def encPc : Option ℕ → List Bool
  | none => []
  | some n => un (n + 1)

def encCfg (P : List Instr) (c : Cfg) : List Bool :=
  pairB (encP P) (pairB (encPc c.pc) (pairB (un c.state) (encLL c.stk)))

def encCode (c : Code) : List Bool :=
  pairB (encP c.prog) (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout])

def hd (s : List Bool) : List Bool := s.takeWhile id

def dropN (s : List Bool) : List Bool := (s.dropWhile id).tail

def sel (f a b : List Bool) : List Bool := if f = [] then a else b

def mulU (u v : List Bool) : List Bool := un (u.length * v.length)

def takeLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: takeLA true r
  | true, false :: r => false :: takeLA false r
  | false, false :: _ => []

def dropLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => dropLA true r
  | true, false :: r => dropLA false r
  | false, false :: r => r

def headLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: headLA true r
  | true, false :: r => false :: headLA false r
  | false, false :: _ => [false]

def takeL (s : List Bool) : List Bool := takeLA false s

def dropL (s : List Bool) : List Bool := dropLA false s

def headL (s : List Bool) : List Bool := headLA false s

def move (y : List Bool) : List Bool :=
  pairB (dropL (unpairB y).1) ((unpairB y).2 ++ headL (unpairB y).1)

def popT : List Bool → List Bool
  | true :: r => dropN (true :: r)
  | s => s

def spread (s : List Bool) : List Bool := s.flatMap fun b => if b then [true, false] else [false]

def bump (s : List Bool) : List Bool := s.flatMap fun b => if b then [true] else [true, false]

def blank (s : List Bool) : List Bool := s.map fun _ => false

@[simp] theorem sel_nil (a b : List Bool) : sel [] a b = a := rfl

@[simp] theorem sel_cons (x : Bool) (f a b : List Bool) : sel (x :: f) a b = b := by
  simp [sel]

theorem sel_append_left (f p a b : List Bool) : sel f (p ++ a) (p ++ b) = p ++ sel f a b := by
  unfold sel; split <;> rfl

@[simp] theorem hd_nil : hd [] = [] := rfl

@[simp] theorem dropN_nil : dropN [] = [] := rfl

theorem hd_un (n : ℕ) (r : List Bool) : hd (un n ++ false :: r) = un n := by
  induction n with
  | zero => simp [hd]
  | succ n ih => simpa [hd, un_succ] using ih

theorem dropN_un (n : ℕ) (r : List Bool) : dropN (un n ++ false :: r) = r := by
  induction n with
  | zero => simp [dropN]
  | succ n ih => simpa [dropN, un_succ] using ih

@[simp] theorem hd_encNs_cons (a : ℕ) (l : List ℕ) : hd (encNs (a :: l)) = un (a + 1) := by
  rw [encNs_cons, encN, List.append_assoc]; exact hd_un _ _

@[simp] theorem dropN_encNs_cons (a : ℕ) (l : List ℕ) : dropN (encNs (a :: l)) = encNs l := by
  rw [encNs_cons, encN, List.append_assoc]; exact dropN_un _ _

theorem dropN_iter_encNs (i : ℕ) (l : List ℕ) : dropN^[i] (encNs l) = encNs (l.drop i) := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simpa using ih []
    | cons a l => simpa using ih l

theorem lookup_spec (i : ℕ) (l : List ℕ) :
    (hd (dropN^[i] (encNs l))).tail = un (l.getD i 0) := by
  rw [dropN_iter_encNs]
  induction i generalizing l with
  | zero => cases l <;> simp [un_succ]
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a l => simpa using ih l

theorem takeLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    takeLA b (un n ++ true :: false :: r) = un n ++ true :: false :: takeLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [takeLA]
  | succ n ih => cases b <;> simp [un_succ, takeLA, ih]

theorem dropLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    dropLA b (un n ++ true :: false :: r) = dropLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [dropLA]
  | succ n ih => cases b <;> simp [un_succ, dropLA, ih]

theorem headLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    headLA b (un n ++ true :: false :: r) = un n ++ true :: false :: headLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [headLA]
  | succ n ih => cases b <;> simp [un_succ, headLA, ih]

theorem encN_eq (a : ℕ) : encN a = un a ++ [true, false] := by
  induction a with
  | zero => rfl
  | succ a ih => rw [encN, un_succ, List.cons_append, ← encN, ih, un_succ]; rfl

theorem takeL_encNs (l : List ℕ) (r : List Bool) : takeL (encNs l ++ false :: r) = encNs l := by
  induction l with
  | nil => simp [takeL, takeLA]
  | cons a l ih =>
    rw [takeL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [takeLA_un, ih]

theorem dropL_encNs (l : List ℕ) (r : List Bool) : dropL (encNs l ++ false :: r) = r := by
  induction l with
  | nil => simp [dropL, dropLA]
  | cons a l ih =>
    rw [dropL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [dropLA_un, ih]

theorem headL_encNs (l : List ℕ) (r : List Bool) :
    headL (encNs l ++ false :: r) = encNs l ++ [false] := by
  induction l with
  | nil => simp [headL, headLA]
  | cons a l ih =>
    rw [headL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [headLA_un, ih]

@[simp] theorem takeL_nil : takeL [] = [] := rfl

@[simp] theorem dropL_nil : dropL [] = [] := rfl

@[simp] theorem headL_nil : headL [] = [] := rfl

theorem dropL_iter_nil (k : ℕ) : dropL^[k] [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

theorem dropL_iter_encLL (k : ℕ) (S : List (List ℕ)) :
    dropL^[k] (encLL S) = encLL (S.drop k) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases S with
    | nil => simpa using ih []
    | cons a S => rw [encLL_cons, dropL_encNs]; simpa using ih S

theorem fetch_spec (P : List Instr) (n : ℕ) :
    takeL (dropL^[n] (encP P)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [encP, dropL_iter_encLL]
  induction P generalizing n with
  | nil => simp
  | cons i P ih =>
    cases n with
    | zero => simp [encLL_cons, takeL_encNs]
    | succ n => simpa using ih n

theorem move_pairB (r d : List Bool) : move (pairB r d) = pairB (dropL r) (d ++ headL r) := by
  simp [move, unpairB_pairB]

theorem move_iter_encLL (k : ℕ) (S : List (List ℕ)) (d : List Bool) :
    move^[k] (pairB (encLL S) d) = pairB (encLL (S.drop k)) (d ++ encLL (S.take k)) := by
  induction k generalizing S d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, move_pairB]
    cases S with
    | nil => simpa using ih [] d
    | cons a S =>
      rw [encLL_cons, dropL_encNs, headL_encNs, ih]
      simp [encLL_cons]

theorem hd_drop_encLL (S : List (List ℕ)) (k : ℕ) :
    hd (encLL (S.drop k)) = un (topIndex (S.getD k [])) := by
  induction S generalizing k with
  | nil => simp [topIndex]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, hd, topIndex]
      | cons s a =>
        simp only [List.drop_zero, encLL_cons, encNs_cons, encN, List.append_assoc,
          List.cons_append, List.nil_append]
        rw [hd_un]; simp [topIndex]
    | succ k => simpa using ih k

theorem ins_spec (l : List ℕ) (S : List (List ℕ)) (k : ℕ) :
    sel (encLL (S.drop k)) (encLL (S.take k))
        (encLL (S.take k) ++ (encNs l ++ encLL (S.drop k))) =
      encLL (S.set k (l ++ S.getD k [])) := by
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      simp [encLL_cons, encNs_append]
      cases h : encNs a <;> simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [← this]
      unfold sel; split <;> simp

theorem pop_spec (S : List (List ℕ)) (k : ℕ) :
    encLL (S.take k) ++ popT (encLL (S.drop k)) = encLL (S.set k (S.getD k []).tail) := by
  induction S generalizing k with
  | nil => simp [popT]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, popT]
      | cons s a =>
        simp only [List.take_zero, encLL_nil, List.nil_append, List.drop_zero, List.set_cons_zero,
          List.getD_cons_zero, List.tail_cons]
        rw [encLL_cons, encLL_cons, encNs_cons, encN, un_succ]
        simp only [List.cons_append, List.append_assoc, popT]
        rw [← List.cons_append, ← un_succ, dropN_un]
        simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [this]

theorem bump_append (a b : List Bool) : bump (a ++ b) = bump a ++ bump b := by
  simp [bump]

theorem inX_spec (x : List Bool) :
    bump (spread x) = encNs (x.map fun b => cond b 1 0) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h : spread (b :: x) = (if b then [true, false] else [false]) ++ spread x := by
      simp [spread]
    rw [h, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem inW_spec (w : List Bool) :
    bump (bump (bump (spread w))) = encNs (w.map fun b => cond b 3 2) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h : spread (b :: w) = (if b then [true, false] else [false]) ++ spread w := by
      simp [spread]
    rw [h, bump_append, bump_append, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem blank_un (n : ℕ) : blank (un n) = encLL (List.replicate n []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [un_succ, List.replicate_succ, encLL_cons, ← ih]; rfl

theorem hd_length (s : List Bool) : (hd s).length ≤ s.length :=
  (List.takeWhile_prefix _).length_le

theorem dropN_length (s : List Bool) : (dropN s).length ≤ s.length := by
  have := (List.dropWhile_suffix (l := s) id).length_le
  simp only [dropN, List.length_tail]
  omega

theorem iter_length (g : List Bool → List Bool) (hg : ∀ s, (g s).length ≤ s.length) (k : ℕ)
    (s : List Bool) : (g^[k] s).length ≤ s.length := by
  induction k generalizing s with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (hg s)

theorem takeLA_length (b : Bool) (s : List Bool) : (takeLA b s).length ≤ s.length := by
  induction s generalizing b with
  | nil => simp [takeLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [takeLA] <;> exact ih _

theorem head_drop_LA (b : Bool) (s : List Bool) : headLA b s ++ dropLA b s = s := by
  induction s generalizing b with
  | nil => simp [headLA, dropLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [headLA, dropLA] <;> exact ih _

theorem headL_dropL (s : List Bool) : headL s ++ dropL s = s := head_drop_LA false s

theorem headL_dropL_length (s : List Bool) : (headL s).length + (dropL s).length = s.length := by
  have := congrArg List.length (headL_dropL s)
  simpa using this

theorem takeL_length (s : List Bool) : (takeL s).length ≤ s.length := takeLA_length false s

theorem dropL_length (s : List Bool) : (dropL s).length ≤ s.length := by
  have := headL_dropL_length s; omega

theorem popT_length (s : List Bool) : (popT s).length ≤ s.length := by
  unfold popT
  split
  · exact dropN_length _
  · exact le_rfl

theorem sel_length (f a b : List Bool) (B : ℕ) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (sel f a b).length ≤ B := by
  unfold sel; split <;> assumption

theorem unpairB_length (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have h := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
  simp only [List.length_append] at h
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  omega

theorem pairB_length (a b : List Bool) : (pairB a b).length = 2 * a.length + b.length + 1 := by
  simp [pairB]; omega

theorem move_length (y : List Bool) : (move y).length ≤ y.length + 1 := by
  have h := unpairB_length y
  have h2 := headL_dropL_length (unpairB y).1
  simp only [move, pairB_length, List.length_append]
  omega

theorem move_iter (k : ℕ) (r d : List Bool) :
    ∃ d', move^[k] (pairB r d) = pairB (dropL^[k] r) d' ∧
      (dropL^[k] r).length + d'.length ≤ r.length + d.length := by
  induction k generalizing r d with
  | zero => exact ⟨d, rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨d', h1, h2⟩ := ih (dropL r) (d ++ headL r)
    refine ⟨d', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, move_pairB, h1, Function.iterate_succ_apply]
    · have := headL_dropL_length r
      rw [Function.iterate_succ_apply]
      simp only [List.length_append] at h2
      omega

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.SStep
section

namespace PEqualNP.Library.Universal

def fetch (ps pc : List Bool) : List Bool := takeL (dropL^[pc.tail.length] ps)

def fOp (I : List Bool) : List Bool := hd I

def fK (I : List Bool) : List Bool := (hd (dropN I)).tail

def fW (I : List Bool) : List Bool := (hd (dropN (dropN I))).tail

def fN1 (I : List Bool) : List Bool := hd (dropN (dropN (dropN I)))

def fN2 (I : List Bool) : List Bool := hd (dropN (dropN (dropN (dropN I))))

def fTb (I : List Bool) : List Bool := dropN (dropN (dropN (dropN (dropN I))))

def lookup (tb idx : List Bool) : List Bool := (hd (dropN^[idx.length] tb)).tail

def splitK (kf sk : List Bool) : List Bool := move^[kf.length] (pairB sk [])

def pcSel (pc o n1 n2 valS : List Bool) : List Bool :=
  sel pc pc (sel o [] (sel o.tail n1 (sel o.tail.tail n1 (sel o.tail.tail.tail n1
    (sel o.tail.tail.tail.tail n1 (sel o.tail.tail.tail.tail.tail (sel valS n2 n1)
      (sel o.tail.tail.tail.tail.tail.tail (true :: valS) [])))))))

def stSel (pc o st valS valT : List Bool) : List Bool :=
  sel pc st (sel o st (sel o.tail st (sel o.tail.tail valT (sel o.tail.tail.tail valT
    (sel o.tail.tail.tail.tail valS st)))))

def skSel (pc o sk r d pushed : List Bool) : List Bool :=
  sel pc sk (sel o sk (sel o.tail (sel r d (d ++ (pushed ++ r)))
    (sel o.tail.tail (d ++ popT r) sk)))

def pcOut (ps pc st : List Bool) : List Bool :=
  pcSel pc (fOp (fetch ps pc)) (fN1 (fetch ps pc)) (fN2 (fetch ps pc))
    (lookup (fTb (fetch ps pc)) st)

def stOut (ps pc st sk : List Bool) : List Bool :=
  stSel pc (fOp (fetch ps pc)) st (lookup (fTb (fetch ps pc)) st)
    (lookup (fTb (fetch ps pc))
      (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1))

def skOut (ps pc st sk : List Bool) : List Bool :=
  skSel pc (fOp (fetch ps pc)) sk (unpairB (splitK (fK (fetch ps pc)) sk)).1
    (unpairB (splitK (fK (fetch ps pc)) sk)).2
    (true :: lookup (fTb (fetch ps pc)) st ++ [false])

def sstepParts (ps pc st sk : List Bool) : List Bool :=
  pairB ps (pairB (pcOut ps pc st) (pairB (stOut ps pc st sk) (skOut ps pc st sk)))

def sstep (y : List Bool) : List Bool :=
  sstepParts (unpairB y).1 (unpairB (unpairB y).2).1 (unpairB (unpairB (unpairB y).2).2).1
    (unpairB (unpairB (unpairB y).2).2).2

theorem fetch_encP (P : List Instr) (n : ℕ) :
    fetch (encP P) (un (n + 1)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [fetch, un_succ, List.tail_cons, un_length]
  exact fetch_spec P n

theorem lookup_encNs (tbl : List ℕ) (i : List Bool) :
    lookup (encNs tbl) i = un (tbl.getD i.length 0) := lookup_spec _ _

theorem splitK_encLL (k : ℕ) (S : List (List ℕ)) :
    unpairB (splitK (un k) (encLL S)) = (encLL (S.drop k), encLL (S.take k)) := by
  rw [splitK, un_length, move_iter_encLL, unpairB_pairB, List.nil_append]

section fields

variable (a b c d e : ℕ) (tbl : List ℕ)

theorem fOp_enc : fOp (encNs (a :: b :: c :: d :: e :: tbl)) = un (a + 1) := by simp [fOp]

theorem fK_enc : fK (encNs (a :: b :: c :: d :: e :: tbl)) = un b := by simp [fK, un_succ]

theorem fW_enc : fW (encNs (a :: b :: c :: d :: e :: tbl)) = un c := by simp [fW, un_succ]

theorem fN1_enc : fN1 (encNs (a :: b :: c :: d :: e :: tbl)) = un (d + 1) := by simp [fN1]

theorem fN2_enc : fN2 (encNs (a :: b :: c :: d :: e :: tbl)) = un (e + 1) := by simp [fN2]

theorem fTb_enc : fTb (encNs (a :: b :: c :: d :: e :: tbl)) = encNs tbl := by simp [fTb]

end fields

theorem un_one : un 1 = [true] := rfl
theorem un_two : un 2 = [true, true] := rfl
theorem un_three : un 3 = [true, true, true] := rfl
theorem un_four : un 4 = [true, true, true, true] := rfl
theorem un_five : un 5 = [true, true, true, true, true] := rfl
theorem un_six : un 6 = [true, true, true, true, true, true] := rfl
theorem un_seven : un 7 = [true, true, true, true, true, true, true] := rfl

theorem sel_un (n : ℕ) (a b : List Bool) : sel (un n) a b = if n = 0 then a else b := by
  cases n <;> simp [un_succ]

theorem out_spec (P : List Instr) (pc : Option ℕ) (v : ℕ) (S : List (List ℕ)) :
    pcOut (encP P) (encPc pc) (un v) = encPc (step P ⟨pc, v, S⟩).pc ∧
    stOut (encP P) (encPc pc) (un v) (encLL S) = un (step P ⟨pc, v, S⟩).state ∧
    skOut (encP P) (encPc pc) (un v) (encLL S) = encLL (step P ⟨pc, v, S⟩).stk := by
  cases pc with
  | none => simp [pcOut, stOut, skOut, pcSel, stSel, skSel, encPc, step]
  | some n =>
    have hf := fetch_encP P n
    simp only [pcOut, stOut, skOut, encPc, step]
    cases h : P[n]? with
    | none =>
      rw [h] at hf
      simp only [hf]
      simp [pcSel, stSel, skSel, fOp, un_succ]
    | some i =>
      rw [h] at hf
      simp only [hf]
      cases i with
      | push k tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · have := ins_spec [tbl.getD v 0] S k
          simp only [encNs_cons, encN, encNs_nil, List.append_nil,
            un_succ, List.cons_append] at this
          simpa [skSel, un_succ] using this
      | pop k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ, pop_spec]
      | peek k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | load tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | branch tbl next₁ next₂ =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp only [pcSel, sel_un]
          by_cases hz : tbl[v]?.getD 0 = 0 <;> simp [hz, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | goto tbl =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | halt =>
        simp only [instrNs, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]

theorem sstep_encCfg (P : List Instr) (cfg : Cfg) :
    sstep (encCfg P cfg) = encCfg P (step P cfg) := by
  obtain ⟨pc, v, S⟩ := cfg
  obtain ⟨h1, h2, h3⟩ := out_spec P pc v S
  simp only [sstep, encCfg, unpairB_pairB, sstepParts, h1, h2, h3]

theorem sstep_iter (P : List Instr) (cfg : Cfg) (t : ℕ) :
    sstep^[t] (encCfg P cfg) = encCfg P ((step P)^[t] cfg) := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sstep_encCfg, ih]

theorem tail_length_le (s : List Bool) : s.tail.length ≤ s.length := by simp

theorem fetch_length (ps pc : List Bool) : (fetch ps pc).length ≤ ps.length :=
  (takeL_length _).trans (iter_length dropL dropL_length _ _)

theorem lookup_length (tb idx : List Bool) : (lookup tb idx).length ≤ tb.length :=
  (tail_length_le _).trans ((hd_length _).trans (iter_length dropN dropN_length _ _))

theorem fN1_length (I : List Bool) : (fN1 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans (dropN_length _)))

theorem fN2_length (I : List Bool) : (fN2 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem fTb_length (I : List Bool) : (fTb I).length ≤ I.length :=
  (dropN_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem pcOut_length (ps pc st : List Bool) :
    (pcOut ps pc st).length ≤ pc.length + ps.length + 1 := by
  have h0 := fetch_length ps pc
  have h1 := fN1_length (fetch ps pc)
  have h2 := fN2_length (fetch ps pc)
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  unfold pcOut pcSel
  repeat' apply sel_length
  all_goals (try simp only [List.length_cons, List.length_nil]); omega

theorem stOut_length (ps pc st sk : List Bool) :
    (stOut ps pc st sk).length ≤ st.length + ps.length := by
  have h0 := fetch_length ps pc
  have h3 := fun idx => (lookup_length (fTb (fetch ps pc)) idx).trans (fTb_length _)
  have h4 := h3 st
  have h5 := h3 (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1)
  unfold stOut stSel
  repeat' apply sel_length
  all_goals omega

theorem skOut_length (ps pc st sk : List Bool) :
    (skOut ps pc st sk).length ≤ sk.length + ps.length + 2 := by
  have h0 := fetch_length ps pc
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  obtain ⟨d', e1, e2⟩ := move_iter (fK (fetch ps pc)).length sk []
  have e3 : unpairB (splitK (fK (fetch ps pc)) sk) = (dropL^[(fK (fetch ps pc)).length] sk, d') := by
    rw [splitK, e1, unpairB_pairB]
  have h6 := popT_length (dropL^[(fK (fetch ps pc)).length] sk)
  unfold skOut skSel
  rw [e3]
  repeat' apply sel_length
  all_goals simp only [List.length_cons, List.length_nil, List.length_append] at *; omega

def smeasure (y : List Bool) : ℕ := 5 * (unpairB y).1.length + 7

theorem smeasure_sstep (y : List Bool) : smeasure (sstep y) ≤ smeasure y := by
  simp [smeasure, sstep, sstepParts, unpairB_pairB]

theorem sstep_length (y : List Bool) : (sstep y).length ≤ y.length + smeasure y := by
  have a1 := unpairB_length y
  have a2 := unpairB_length (unpairB y).2
  have a3 := unpairB_length (unpairB (unpairB y).2).2
  have b1 := pcOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1
  have b2 := stOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  have b3 := skOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  simp only [sstep, sstepParts, pairB_length, smeasure]
  omega

theorem smeasure_le (y : List Bool) : smeasure y ≤ 7 * y.length + 7 := by
  have a1 := unpairB_length y
  simp only [smeasure]
  omega

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.Verify
section

namespace PEqualNP.Library.Universal

def hNst (h : List Bool) : List Bool := (hd h).tail

def hPc (h : List Bool) : List Bool := hd (dropN h)

def hSt (h : List Bool) : List Bool := (hd (dropN (dropN h))).tail

def hKin (h : List Bool) : List Bool := (hd (dropN (dropN (dropN h)))).tail

def hKout (h : List Bool) : List Bool := (hd (dropN (dropN (dropN (dropN h))))).tail

def insK (kf new sk : List Bool) : List Bool :=
  sel (unpairB (splitK kf sk)).1 (unpairB (splitK kf sk)).2
    ((unpairB (splitK kf sk)).2 ++ (new ++ (unpairB (splitK kf sk)).1))

def inSyms (x w : List Bool) : List Bool := bump (spread x) ++ bump (bump (bump (spread w)))

def initS (cs x w : List Bool) : List Bool :=
  pairB (unpairB cs).1 (pairB (hPc (unpairB cs).2) (pairB (hSt (unpairB cs).2)
    (insK (hKin (unpairB cs).2) (inSyms x w) (blank (hNst (unpairB cs).2)))))

def haltedS (y : List Bool) : Bool := (unpairB (unpairB y).2).1.isEmpty

def stkS (y : List Bool) : List Bool := (unpairB (unpairB (unpairB y).2).2).2

def outOne (kout sk : List Bool) : Bool :=
  decide ((dropL^[kout.length] sk).take 4 = [true, true, false, false])

def V (p : List Bool × List Bool) : Bool :=
  decide (p.2.length ≤ (unpairB (unpairB p.1).2).2.length) &&
    (haltedS (sstep^[(unpairB (unpairB p.1).2).2.length]
      (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2)) &&
    outOne (hKout (unpairB (unpairB p.1).1).2)
      (stkS (sstep^[(unpairB (unpairB p.1).2).2.length]
        (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2))))

theorem getD_replicate_nil (n k : ℕ) : (List.replicate n ([] : List ℕ)).getD k [] = [] := by
  induction n generalizing k with
  | zero => simp
  | succ n ih => cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ] using ih k

theorem insK_spec (k : ℕ) (l : List ℕ) (S : List (List ℕ)) :
    insK (un k) (encNs l) (encLL S) = encLL (S.set k (l ++ S.getD k [])) := by
  rw [insK, splitK_encLL, ins_spec]

theorem inSyms_spec (x w : List Bool) :
    inSyms x w = encNs ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2) := by
  rw [inSyms, inX_spec, inW_spec, encNs_append]

theorem initS_spec (c : Code) (x w : List Bool) :
    initS (encCode c) x w =
      encCfg c.prog (c.init ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2)) := by
  have h1 : hNst (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.nstk := by
    simp [hNst, un_succ]
  have h2 : hPc (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un (c.pc₀ + 1) := by
    simp [hPc]
  have h3 : hSt (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.state₀ := by
    simp [hSt, un_succ]
  have h4 : hKin (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.kin := by
    simp [hKin, un_succ]
  simp only [initS, encCode, unpairB_pairB, h1, h2, h3, h4, blank_un, inSyms_spec, insK_spec,
    getD_replicate_nil, List.append_nil, encCfg, Code.init, encPc]

theorem haltedS_encCfg (P : List Instr) (cfg : Cfg) :
    haltedS (encCfg P cfg) = true ↔ cfg.pc = none := by
  obtain ⟨pc, v, S⟩ := cfg
  cases pc <;> simp [haltedS, encCfg, unpairB_pairB, encPc, un_succ]

theorem stkS_encCfg (P : List Instr) (cfg : Cfg) : stkS (encCfg P cfg) = encLL cfg.stk := by
  simp [stkS, encCfg, unpairB_pairB]

theorem outOne_spec (k : ℕ) (S : List (List ℕ)) :
    outOne (un k) (encLL S) = true ↔ S.getD k [] = [1] := by
  rw [outOne, un_length, dropL_iter_encLL, decide_eq_true_eq]
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      rcases a with _ | ⟨s, a⟩
      · simp [encLL_cons]
      · rcases s with _ | _ | s
        · simp [encLL_cons, encNs_cons, encN, un_succ]
        · rcases a with _ | ⟨s', a⟩
          · simp [encLL_cons, encNs_cons, encN, un_succ]
          · simp [encLL_cons, encNs_cons, encN, un_succ]
        · simp [encLL_cons, encNs_cons, encN, un_succ]
    | succ k => simpa using ih k

theorem V_spec (c : Code) (x w : List Bool) (t : ℕ) :
    V (pairB (encCode c) (pairB x (un t)), w) = true ↔
      (w.length ≤ t ∧ c.outputsWithin
        (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2)) t [1]) := by
  have h5 : hKout (unpairB (encCode c)).2 = un c.kout := by
    simp [hKout, encCode, unpairB_pairB, un_succ]
  simp only [V, unpairB_pairB, un_length, initS_spec, sstep_iter, h5, Bool.and_eq_true,
    decide_eq_true_eq, haltedS_encCfg, stkS_encCfg, outOne_spec, Code.outputsWithin, Code.run]

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Defs.Base
section

namespace PEqualNP.Library

def ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (t : ℕ → ℕ) : Prop :=
  ∃ c : Turing.TM2ComputableInTime ea eb f, ∀ n, c.time n ≤ t n

def ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) :
    Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

def DecidableInTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) (t : ℕ → ℕ) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInTime ea Computability.encodeBool f t

def DecidableInPolyTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInPolyTime ea Computability.encodeBool f

def encodePair (p : List Bool × List Bool) : List (Bool ⊕ Bool) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

def DTIME (t : ℕ → ℕ) : Set (Language Bool) :=
  {L | DecidableInTime (fun x : List Bool => x) L t}

def P : Set (Language Bool) :=
  {L | DecidableInPolyTime (fun x : List Bool => x) L}

def NP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R}

def PolyTimeReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool,
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ x, x ∈ L₁ ↔ f x ∈ L₂

def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, PolyTimeReducible L' L

def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

end PEqualNP.Library
end

-- upstream PEqualNP.Defs.Classes
section

namespace PEqualNP.Library

def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

def EXP : Set (Language Bool) :=
  {L | ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)}

def NEXP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (k : ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ (x, w) ∈ R}

end PEqualNP.Library
end

-- upstream PEqualNP.Defs.ProofComplexity
section

namespace PEqualNP.ProofComplexity

abbrev Literal (V : Type) : Type := V × Bool

abbrev Clause (V : Type) : Type := Finset (Literal V)

def ClauseSat {V : Type} (a : V → Bool) (C : Clause V) : Prop :=
  ∃ l ∈ C, a l.1 = l.2

def Satisfies {V : Type} (a : V → Bool) (F : Set (Clause V)) : Prop :=
  ∀ C ∈ F, ClauseSat a C

def Satisfiable {V : Type} (F : Set (Clause V)) : Prop :=
  ∃ a : V → Bool, Satisfies a F

def IsResolvent {V : Type} [DecidableEq V] (C D R : Clause V) : Prop :=
  ∃ v : V, (v, true) ∈ C ∧ (v, false) ∈ D ∧ R = C.erase (v, true) ∪ D.erase (v, false)

inductive IsDerivation {V : Type} [DecidableEq V] (F : Set (Clause V)) :
    List (Clause V) → Prop
  | nil : IsDerivation F []
  | ax {π : List (Clause V)} {C : Clause V} :
      IsDerivation F π → C ∈ F → IsDerivation F (C :: π)
  | res {π : List (Clause V)} {C D R : Clause V} :
      IsDerivation F π → C ∈ π → D ∈ π → IsResolvent C D R → IsDerivation F (R :: π)

def IsRefutation {V : Type} [DecidableEq V] (F : Set (Clause V)) (π : List (Clause V)) : Prop :=
  IsDerivation F π ∧ (∅ : Clause V) ∈ π

def PHP (m n : ℕ) : Set (Clause (Fin m × Fin n)) :=
  {C | ∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))} ∪
  {C | ∃ (i i' : Fin m) (j : Fin n), i ≠ i' ∧ C = {((i, j), false), ((i', j), false)}}

end PEqualNP.ProofComplexity
end

-- upstream PEqualNP.Defs.Search
section

namespace PEqualNP.Search

abbrev Literal : Type := ℕ × Bool

abbrev Clause : Type := List Literal

abbrev CNF : Type := List Clause

abbrev Assignment : Type := ℕ → Bool

def Literal.eval (σ : Assignment) (l : Literal) : Bool :=
  σ l.1 == l.2

def Clause.eval (σ : Assignment) (c : Clause) : Bool :=
  c.any (Literal.eval σ)

def CNF.eval (σ : Assignment) (φ : CNF) : Bool :=
  φ.all (Clause.eval σ)

def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, CNF.eval σ φ = true

def IsKCNF (k : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, c.length ≤ k

def encodeLiteral (l : Literal) : List Bool :=
  [true, l.2] ++ (l.1.bits.flatMap fun d => [true, d]) ++ [false, true]

def encodeClause (c : Clause) : List Bool :=
  c.flatMap encodeLiteral ++ [false, false]

def encodeCNF (φ : CNF) : List Bool :=
  φ.flatMap encodeClause

def SAT : Language Bool :=
  {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ}

def KSAT (k : ℕ) : Language Bool :=
  {x | ∃ φ : CNF, IsKCNF k φ ∧ encodeCNF φ = x ∧ Satisfiable φ}

abbrev LinEq (n : ℕ) : Type := Finset (Fin n) × Bool

def LinEq.Holds {n : ℕ} (a : Fin n → Bool) (e : LinEq n) : Prop :=
  (e.1.filter fun i => a i = true).card % 2 = 1 ↔ e.2 = true

abbrev LinClause (n : ℕ) : Type := List (LinEq n)

def LinClause.Holds {n : ℕ} (a : Fin n → Bool) (C : LinClause n) : Prop :=
  ∃ e ∈ C, LinEq.Holds a e

inductive IsResLinDerivation {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    List (LinClause n) → Prop
  | nil : IsResLinDerivation F []
  | ax {π : List (LinClause n)} {L : LinClause n} (C : PEqualNP.ProofComplexity.Clause (Fin n)) :
      IsResLinDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = ({l.1}, l.2)) →
      IsResLinDerivation F (L :: π)
  | res {π : List (LinClause n)} {e e' : LinEq n} {C D : LinClause n} :
      IsResLinDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π → e.1 = e'.1 → e.2 ≠ e'.2 →
      IsResLinDerivation F ((C ++ D) :: π)
  | weaken {π : List (LinClause n)} {C D : LinClause n} :
      IsResLinDerivation F π → C ∈ π → (∀ a : Fin n → Bool, LinClause.Holds a C → LinClause.Holds a D) →
      IsResLinDerivation F (D :: π)

def IsResLinRefutation {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (π : List (LinClause n)) : Prop :=
  IsResLinDerivation F π ∧ ([] : LinClause n) ∈ π

end PEqualNP.Search
end

-- upstream PEqualNP.Library.Machines.Run
section

namespace PEqualNP.Library.Machines

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Transducer
section

namespace PEqualNP.Library.Machines

open Turing

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq

instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Universal.LazyDefs
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library.Machines

def halfD (q : Bool) (_ : Bool) : Bool × Option Bool := (!q, if q then some true else none)

def half (u : List Bool) : List Bool := fstRun halfD (fun _ => none) false u

theorem halfD_run (q : Bool) (u : List Bool) :
    fstRun halfD (fun _ => none) q u = un ((u.length + (if q then 1 else 0)) / 2) := by
  induction u generalizing q with
  | nil => cases q <;> rfl
  | cons b l ih =>
    cases q
    · simp [fstRun, halfD, ih]
    · have e : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
      simp [fstRun, halfD, ih, e, un_succ]

theorem half_eq (u : List Bool) : half u = un (u.length / 2) := by
  simp [half, halfD_run]

def lgStep (s : List Bool) : List Bool :=
  sel (unpairB s).2 s (pairB (true :: (unpairB s).1) (half (unpairB s).2))

def lgU (u : List Bool) : List Bool := (unpairB (lgStep^[u.length] (pairB [] u))).1

theorem size_half {r : ℕ} (hr : r ≠ 0) : Nat.size r = Nat.size (r / 2) + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (r / 2)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (Nat.size (r / 2)) with h | h
    · rw [h]; simp; omega
    · have h1 : Nat.size (r / 2) - 1 < Nat.size (r / 2) := by omega
      rw [Nat.lt_size] at h1
      have h2 : 2 ^ Nat.size (r / 2) = 2 ^ (Nat.size (r / 2) - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      omega

theorem lgStep_zero (c : ℕ) : lgStep (pairB (un c) (un 0)) = pairB (un c) (un 0) := by
  simp [lgStep, unpairB_pairB, sel]

theorem lgStep_pos (c r : ℕ) (hr : r ≠ 0) :
    lgStep (pairB (un c) (un r)) = pairB (un (c + 1)) (un (r / 2)) := by
  have h : un r ≠ [] := by
    intro h
    exact hr (by simpa using congrArg List.length h)
  simp [lgStep, unpairB_pairB, sel, h, half_eq, un_succ]

theorem lgStep_iter (k : ℕ) : ∀ r c : ℕ, r < 2 ^ k →
    lgStep^[k] (pairB (un c) (un r)) = pairB (un (c + Nat.size r)) (un 0) := by
  induction k with
  | zero =>
    intro r c hr
    obtain rfl : r = 0 := by simpa using hr
    simp
  | succ k ih =>
    intro r c hr
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      rw [lgStep_zero]
      exact ih 0 c (Nat.pos_of_ne_zero (by positivity))
    · rw [lgStep_pos c r (by omega), ih (r / 2) (c + 1) (by rw [pow_succ] at hr; omega),
        size_half (by omega : r ≠ 0)]
      congr 2
      omega

theorem lgU_un (n : ℕ) : lgU (un n) = un (Nat.size n) := by
  have h := lgStep_iter n n 0 Nat.lt_two_pow_self
  rw [un_zero] at h
  simp [lgU, h, unpairB_pairB]

theorem un_length_eq (u : List Bool) (h : ∀ b ∈ u, b = true) : u = un u.length :=
  List.eq_replicate_iff.2 ⟨rfl, h⟩

theorem lgU_length (n : ℕ) : (lgU (un n)).length = Nat.size n := by
  rw [lgU_un, un_length]

def condC (y mu : List Bool) : Bool := decide (y.length ≤ (lgU (lgU mu)).length)

theorem condC_un (y : List Bool) (m : ℕ) :
    condC y (un m) = decide (y.length ≤ Nat.size (Nat.size m)) := by
  simp [condC, lgU_un]

def succD (carry : Bool) (b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

def succFin (carry : Bool) : Option Bool := if carry then some false else none

def succB (s : List Bool) : List Bool := fstRun succD succFin true s

def cand (j : ℕ) : List Bool := succB^[j] []

theorem succD_run_false (s : List Bool) : fstRun succD succFin false s = s := by
  induction s with
  | nil => rfl
  | cons b l ih => simp [fstRun, succD, ih]

theorem succB_nil : succB [] = [false] := rfl

theorem succB_false (r : List Bool) : succB (false :: r) = true :: r := by
  simp [succB, fstRun, succD, succD_run_false]

theorem succB_true (r : List Bool) : succB (true :: r) = false :: succB r := by
  simp [succB, fstRun, succD]

def idx : List Bool → ℕ
  | [] => 0
  | false :: r => 1 + 2 * idx r
  | true :: r => 2 + 2 * idx r

theorem idx_succB (s : List Bool) : idx (succB s) = idx s + 1 := by
  induction s with
  | nil => rfl
  | cons b r ih =>
    cases b
    · rw [succB_false]; simp [idx]; omega
    · rw [succB_true]; simp [idx, ih]; omega

theorem idx_cand (j : ℕ) : idx (cand j) = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cand, Function.iterate_succ_apply', ← cand, idx_succB, ih]

theorem idx_inj : ∀ s t : List Bool, idx s = idx t → s = t
  | [], [], _ => rfl
  | [], false :: _, h => by simp [idx] at h; omega
  | [], true :: _, h => by simp [idx] at h; omega
  | false :: _, [], h => by simp [idx] at h
  | true :: _, [], h => by simp [idx] at h
  | false :: r, false :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | true :: r, true :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | false :: _, true :: _, h => by simp [idx] at h; omega
  | true :: _, false :: _, h => by simp [idx] at h; omega

theorem cand_idx (s : List Bool) : cand (idx s) = s := idx_inj _ _ (idx_cand _)

theorem idx_bound (s : List Bool) : idx s + 2 ≤ 2 ^ (s.length + 1) := by
  induction s with
  | nil => simp [idx]
  | cons b r ih =>
    have e : 2 ^ ((b :: r).length + 1) = 2 * 2 ^ (r.length + 1) := by
      rw [List.length_cons, pow_succ, Nat.mul_comm]
    cases b <;> simp only [idx] <;> omega

theorem idx_lt_of_length_le {s : List Bool} {b : ℕ} (h : s.length ≤ b) :
    idx s + 2 ≤ 2 ^ (b + 1) :=
  (idx_bound s).trans (Nat.pow_le_pow_right (by omega) (by omega))

def bflag (b : Bool) : List Bool := if b then [true] else []

theorem bflag_eq_nil (b : Bool) : bflag b = [] ↔ b = false := by
  cases b <;> simp [bflag]

def srchStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (succB (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++ bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))))

def srch (F n : List Bool) : List Bool :=
  (unpairB (unpairB (srchStep^[n.length] (pairB F (pairB [] [])))).2).2

theorem srchStep_pair (F c fl : List Bool) :
    srchStep (pairB F (pairB c fl)) = pairB F (pairB (succB c) (fl ++ bflag (V (F, c)))) := by
  simp [srchStep, unpairB_pairB]

theorem srchStep_iter (F : List Bool) (k : ℕ) : ∀ c fl : List Bool, ∃ fl' : List Bool,
    srchStep^[k] (pairB F (pairB c fl)) = pairB F (pairB (succB^[k] c) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, V (F, succB^[j] c) = false) := by
  induction k with
  | zero => intro c fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro c fl
    obtain ⟨fl', h1, h2⟩ := ih (succB c) (fl ++ bflag (V (F, c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, srchStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

theorem srch_eq_nil (F n : List Bool) :
    srch F n = [] ↔ ∀ j < n.length, V (F, cand j) = false := by
  obtain ⟨fl', h1, h2⟩ := srchStep_iter F n.length [] []
  rw [srch, h1]
  simpa [unpairB_pairB, cand] using h2

def csOf (z : List Bool) : List Bool := (unpairB z).1

def muOf (z : List Bool) : List Bool := (unpairB (unpairB z).2).2

def y0Of (z : List Bool) : List Bool := pairB (unpairB z).1 (pairB (unpairB (unpairB z).2).1 [])

def RD (p : List Bool × List Bool) : Bool :=
  (!condC (y0Of p.1) (muOf p.1) &&
      V (pairB (csOf p.1) (pairB (p.1 ++ [true]) (unpairB p.2).2), (unpairB p.2).1)) ||
    (condC (y0Of p.1) (muOf p.1) && (!condC (y0Of p.1) (muOf p.1).tail &&
      (srch (pairB (csOf p.1) (pairB (y0Of p.1) (lgU (muOf p.1))))
        (muOf p.1 ++ (muOf p.1 ++ (muOf p.1 ++ muOf p.1)))).isEmpty))

def DLang : Language Bool :=
  {z | ∃ w : List Bool, w.length ≤ 2 ^ (z.length ^ 2) + 2 ∧ RD (z, w) = true}

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.Compile
section

namespace PEqualNP.Library.Universal

open Turing

def symIn : Bool ⊕ Bool → ℕ
  | Sum.inl false => 0 | Sum.inl true => 1 | Sum.inr false => 2 | Sum.inr true => 3

def bitCode (b : Bool) : ℕ := if b then 1 else 0

def symOut : ℕ → Bool ⊕ Bool
  | 0 => Sum.inl false | 1 => Sum.inl true | 2 => Sum.inr false | _ => Sum.inr true

theorem symOut_symIn (x : Bool ⊕ Bool) : symOut (symIn x) = x := by
  rcases x with (_ | _) | (_ | _) <;> rfl

theorem symIn_lt (x : Bool ⊕ Bool) : symIn x < 4 := by
  rcases x with (_ | _) | (_ | _) <;> simp [symIn]

theorem bitCode_le (b : Bool) : bitCode b ≤ 1 := by
  cases b <;> simp [bitCode]

theorem step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) : step P c = c := by
  unfold step; rw [h]

theorem iterate_step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) (t : ℕ) :
    (step P)^[t] c = c :=
  Function.iterate_fixed (step_of_pc_none P c h) t

theorem Code.outputsWithin_mono (c : Code) (input : List ℕ) {t t' : ℕ} (h : t ≤ t')
    (out : List ℕ) : c.outputsWithin input t out → c.outputsWithin input t' out := by
  intro ho
  have hrun : c.run input t' = c.run input t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold Code.run
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact iterate_step_of_pc_none _ _ ho.1 s
  unfold Code.outputsWithin
  rw [hrun]
  exact ho

section Flatten

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

def subs : TM2.Stmt Γ Λ σ → List (TM2.Stmt Γ Λ σ)
  | .push k f q => .push k f q :: subs q
  | .peek k f q => .peek k f q :: subs q
  | .pop k f q => .pop k f q :: subs q
  | .load a q => .load a q :: subs q
  | .branch f q₁ q₂ => .branch f q₁ q₂ :: (subs q₁ ++ subs q₂)
  | .goto f => [.goto f]
  | .halt => [.halt]

theorem subs_head (q : TM2.Stmt Γ Λ σ) : ∃ t, subs q = q :: t := by
  cases q <;> (rw [subs]; exact ⟨_, rfl⟩)

def Placed (L : List (TM2.Stmt Γ Λ σ)) (p : ℕ) (q : TM2.Stmt Γ Λ σ) : Prop :=
  ∃ A B, L = A ++ subs q ++ B ∧ A.length = p

theorem Placed.get {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : L[p]? = some q := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  obtain ⟨t, ht⟩ := subs_head q
  rw [ht]
  simp

theorem Placed.le {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : p + (subs q).length ≤ L.length := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  simp only [List.length_append]
  omega

theorem Placed.sub {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q r : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) (X Y : List (TM2.Stmt Γ Λ σ)) (hq : subs q = q :: (X ++ subs r ++ Y)) :
    Placed L (p + 1 + X.length) r := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  refine ⟨A ++ q :: X, Y ++ B, ?_, ?_⟩
  · rw [hq]; simp
  · simp; omega

theorem forall₂_tail {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R l₁.tail l₂.tail := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons _ h2 => exact h2

theorem forall₂_singleton {α β : Type} {R : α → β → Prop} {l₁ : List α} {y : β}
    (h : List.Forall₂ R l₁ [y]) : ∃ s, l₁ = [s] ∧ R s y := by
  cases h with
  | cons h1 h3 => cases h3; exact ⟨_, rfl, h1⟩

theorem exists_placed (M : Λ → TM2.Stmt Γ Λ σ) (ls : List Λ) (l : Λ) (h : l ∈ ls) :
    ∃ p, Placed ((ls.map fun l => subs (M l)).flatten) p (M l) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨((s.map fun l => subs (M l)).flatten).length, (s.map fun l => subs (M l)).flatten,
    (t.map fun l => subs (M l)).flatten, by simp, rfl⟩

end Flatten

structure Env (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) where
  M : Λ → TM2.Stmt Γ Λ σ
  nσ : ℕ
  nσ_pos : 0 < nσ
  num : σ → ℕ
  σof : ℕ → σ
  σof_num : ∀ v, σof (num v) = v
  num_lt : ∀ v, num v < nσ
  nK : ℕ
  numK : K → ℕ
  numK_lt : ∀ k, numK k < nK
  numK_inj : Function.Injective numK
  L : List (TM2.Stmt Γ Λ σ)
  start : Λ → ℕ
  placed_start : ∀ l, Placed L (start l) (M l)
  k₀ : K
  inSym : ℕ → Γ k₀
  k₁ : K
  outBit : Γ k₁ → ℕ

namespace Env

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (E : Env K Γ Λ σ)

def W : ℕ := 4 + E.nσ * E.L.length + 1

theorem W_pos : 0 < E.W := by unfold W; omega

def decS (s : ℕ) : Option (Σ k, Γ k) :=
  if s < 4 then some ⟨E.k₀, E.inSym s⟩
  else match E.L[(s - 4) / E.nσ]? with
    | some (.push k f _) => some ⟨k, f (E.σof ((s - 4) % E.nσ))⟩
    | _ => none

def decode (k : K) (s : ℕ) : Option (Γ k) :=
  match E.decS s with
  | some ⟨k', y⟩ => if h : k' = k then some (h ▸ y) else none
  | none => none

theorem decode_of_decS {k : K} {s : ℕ} {y : Γ k} (h : E.decS s = some ⟨k, y⟩) :
    E.decode k s = some y := by
  simp [decode, h]

theorem decode_in {s : ℕ} (h : s < 4) : E.decode E.k₀ s = some (E.inSym s) :=
  E.decode_of_decS (by simp [decS, h])

theorem decode_push {p : ℕ} {k : K} {f : σ → Γ k} {r : TM2.Stmt Γ Λ σ}
    (h : E.L[p]? = some (.push k f r)) {a : ℕ} (ha : a < E.nσ) :
    E.decode k (4 + (a + E.nσ * p)) = some (f (E.σof a)) := by
  apply E.decode_of_decS
  unfold decS
  have e : 4 + (a + E.nσ * p) - 4 = a + E.nσ * p := by omega
  have h4 : ¬ (4 + (a + E.nσ * p) < 4) := by omega
  simp only [h4, ↓reduceIte]
  rw [e, Nat.add_mul_div_left _ _ E.nσ_pos, Nat.div_eq_of_lt ha, zero_add, h,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem decode_lt {k : K} {s : ℕ} {y : Γ k} (h : E.decode k s = some y) : s + 1 < E.W := by
  by_contra hc
  unfold W at hc
  have hd : E.decS s = none := by
    unfold decS
    have h1 : E.L.length ≤ (s - 4) / E.nσ := by
      rw [Nat.le_div_iff_mul_le E.nσ_pos, Nat.mul_comm]
      omega
    have h4 : ¬ (s < 4) := by omega
    simp only [h4, ↓reduceIte]
    rw [List.getElem?_eq_none h1]
  simp [decode, hd] at h

def arg (k : K) : ℕ → Option (Γ k)
  | 0 => none
  | s + 1 => E.decode k s

theorem top_spec {k : K} {ns : List ℕ} {ys : List (Γ k)}
    (h : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    topIndex ns < E.W ∧ E.arg k (topIndex ns) = ys.head? := by
  cases h with
  | nil => exact ⟨E.W_pos, rfl⟩
  | cons h1 _ => exact ⟨E.decode_lt h1, by simpa [topIndex, arg] using h1⟩

def tbl1 (g : ℕ → ℕ) : List ℕ := (List.range E.nσ).map g

def tbl2 (g : ℕ → ℕ → ℕ) : List ℕ :=
  (List.range (E.nσ * E.W)).map fun i => g (i / E.W) (i % E.W)

theorem tbl1_get (g : ℕ → ℕ) {a : ℕ} (ha : a < E.nσ) : (E.tbl1 g)[a]?.getD 0 = g a := by
  simp [tbl1, ha]

theorem tbl2_get (g : ℕ → ℕ → ℕ) {a c : ℕ} (ha : a < E.nσ) (hc : c < E.W) :
    (E.tbl2 g)[a * E.W + c]?.getD 0 = g a c := by
  have hlt : a * E.W + c < E.nσ * E.W :=
    calc a * E.W + c < a * E.W + E.W := by omega
      _ = (a + 1) * E.W := by ring
      _ ≤ E.nσ * E.W := Nat.mul_le_mul_right _ ha
  have h1 : (a * E.W + c) / E.W = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ E.W_pos, Nat.div_eq_of_lt hc, zero_add]
  have h2 : (a * E.W + c) % E.W = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp [tbl2, hlt, h1, h2]

def pcOf : Option Λ → ℕ
  | some l => E.start l
  | none => E.L.length

def instrOf (p : ℕ) : TM2.Stmt Γ Λ σ → Instr
  | .push k _ _ => .push (E.numK k) (E.tbl1 fun a => 4 + (a + E.nσ * p)) (p + 1)
  | .peek k f _ =>
    .peek (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .pop k f _ =>
    .pop (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .load f _ => .load (E.tbl1 fun a => E.num (f (E.σof a))) (p + 1)
  | .branch f q₁ _ =>
    .branch (E.tbl1 fun a => if f (E.σof a) then 1 else 0) (p + 1) (p + 1 + (subs q₁).length)
  | .goto f => .goto (E.tbl1 fun a => E.start (f (E.σof a)))
  | .halt => .branch [] E.L.length E.L.length

def finTbl : List ℕ :=
  E.tbl2 fun _ c => match E.arg E.k₁ c with
    | some y => E.outBit y
    | none => 0

def P : List Instr :=
  E.L.mapIdx E.instrOf ++
    [.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
     .push (E.numK E.k₁) [0, 1] (E.L.length + 2),
     .halt]

theorem step_at {p : ℕ} {q : TM2.Stmt Γ Λ σ} (h : E.L[p]? = some q) (a : ℕ)
    (T : List (List ℕ)) : step E.P ⟨some p, a, T⟩ = exec (E.instrOf p q) a T := by
  have hp : p < E.L.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have : E.P[p]? = some (E.instrOf p q) := by
    unfold P
    rw [List.getElem?_append_left (by simpa using hp), List.getElem?_mapIdx, h]
    rfl
  simp [step, this]

theorem step_fin (i : ℕ) (I : Instr)
    (h : [Instr.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
      Instr.push (E.numK E.k₁) [0, 1] (E.L.length + 2), Instr.halt][i]? = some I)
    (a : ℕ) (T : List (List ℕ)) : step E.P ⟨some (E.L.length + i), a, T⟩ = exec I a T := by
  have : E.P[E.L.length + i]? = some I := by
    unfold P
    rw [List.getElem?_append_right (by simp)]
    simpa using h
  simp [step, this]

def StkRel (T : List (List ℕ)) (S : ∀ k, List (Γ k)) : Prop :=
  T.length = E.nK ∧
    ∀ k, List.Forall₂ (fun s y => E.decode k s = some y) (T.getD (E.numK k) []) (S k)

variable {E}

theorem StkRel.set {T : List (List ℕ)} {S : ∀ k, List (Γ k)} (h : E.StkRel T S) (k : K)
    {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel (T.set (E.numK k) ns) (Function.update S k ys) := by
  refine ⟨by simp [h.1], fun k' => ?_⟩
  by_cases hk : k' = k
  · subst hk
    have hlt : E.numK k' < T.length := by rw [h.1]; exact E.numK_lt k'
    simpa [List.getD_eq_getElem?_getD, hlt] using h2
  · have hne : E.numK k ≠ E.numK k' := fun e => hk (E.numK_inj e).symm
    rw [Function.update_of_ne hk]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne] using h.2 k'

theorem StkRel.init (k : K) {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel ((List.replicate E.nK []).set (E.numK k) ns)
      (Function.update (fun _ => []) k ys) := by
  refine StkRel.set ⟨by simp, fun k' => ?_⟩ k h2
  simp [List.getD_eq_getElem?_getD, E.numK_lt k']

variable (E)

theorem sim_stmt (q : TM2.Stmt Γ Λ σ) : ∀ (p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (T : List (List ℕ)), Placed E.L p q → E.StkRel T S →
    ∃ t ≤ (subs q).length, ∃ T', (step E.P)^[t] ⟨some p, E.num v, T⟩ =
        ⟨some (E.pcOf (TM2.stepAux q v S).l), E.num (TM2.stepAux q v S).var, T'⟩ ∧
      E.StkRel T' (TM2.stepAux q v S).stk := by
  induction q with
  | push k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    have hd := E.decode_push hp.get (E.num_lt v)
    rw [E.σof_num] at hd
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) v (Function.update S k (f v :: S k)) _
      (hp.sub [] [] (by simp [subs])) (hr.set k (List.Forall₂.cons hd (hr.2 k)))
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v)] using h
  | peek k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) S T
      (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | pop k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    have htail : List.Forall₂ (fun s y => E.decode k s = some y)
        (T.getD (E.numK k) []).tail (S k).tail := by
      exact forall₂_tail (hr.2 k)
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) (Function.update S k (S k).tail) _
      (hp.sub [] [] (by simp [subs])) (hr.set k htail)
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | load a q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (a v) S T (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num] using h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    cases hf : f v
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₂ (p + 1 + (subs q₁).length) v S T
        (hp.sub (subs q₁) [] (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₁ (p + 1) v S T
        (hp.sub [] (subs q₂) (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
  | goto f =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, pcOf]
  | halt =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, pcOf]

def Rel (c : TM2.Cfg Γ Λ σ) (X : Cfg) : Prop :=
  X.pc = some (E.pcOf c.l) ∧ X.state = E.num c.var ∧ E.StkRel X.stk c.stk

theorem iterate_bind_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem sim_run : ∀ (n : ℕ) (c c' : TM2.Cfg Γ Λ σ) (X : Cfg),
    (flip bind (TM2.step E.M))^[n] (some c) = some c' → E.Rel c X →
    ∃ t ≤ E.L.length * n, E.Rel c' ((step E.P)^[t] X) := by
  intro n
  induction n with
  | zero =>
    intro c c' X h hr
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    exact ⟨0, by simp, hr⟩
  | succ n ih =>
    intro c c' X h hr
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    obtain ⟨pc, a, T⟩ := X
    obtain ⟨h1, h2, h3⟩ := hr
    simp only at h1 h2 h3
    subst h1 h2
    cases l with
    | none =>
      have : flip bind (TM2.step E.M) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
      rw [this, iterate_bind_none] at h
      cases h
    | some l =>
      have : flip bind (TM2.step E.M) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
          some (TM2.stepAux (E.M l) v S) := rfl
      rw [this] at h
      obtain ⟨t₁, ht₁, T', hs, hr'⟩ := E.sim_stmt (E.M l) (E.start l) v S T (E.placed_start l) h3
      have hle := (E.placed_start l).le
      obtain ⟨t₂, ht₂, hfin⟩ := ih _ c' ((step E.P)^[t₁] ⟨some (E.start l), E.num v, T⟩) h
        (by rw [hs]; exact ⟨rfl, rfl, hr'⟩)
      refine ⟨t₂ + t₁, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]; exact hfin

theorem sim_fin (a : ℕ) (ha : a < E.nσ) (T : List (List ℕ)) (hT : T.length = E.nK) (s : ℕ)
    (y : Γ E.k₁) (hs : T.getD (E.numK E.k₁) [] = [s]) (hy : E.decode E.k₁ s = some y)
    (hb : E.outBit y ≤ 1) :
    ∃ T', (step E.P)^[3] ⟨some E.L.length, a, T⟩ = ⟨none, E.outBit y, T'⟩ ∧
      T'.getD (E.numK E.k₁) [] = [E.outBit y] := by
  have hlt : E.numK E.k₁ < T.length := by rw [hT]; exact E.numK_lt _
  have e1 := E.step_fin 0 _ rfl a T
  have e2 := E.step_fin 1 _ rfl
  have e3 := E.step_fin 2 _ rfl
  have hget : E.finTbl.getD (a * E.W + (s + 1)) 0 = E.outBit y := by
    unfold finTbl
    rw [List.getD_eq_getElem?_getD, E.tbl2_get _ ha (E.decode_lt hy)]
    simp [arg, hy]
  have hpush : [0, 1].getD (E.outBit y) 0 = E.outBit y := by
    generalize E.outBit y = c at hb
    interval_cases c <;> rfl
  refine ⟨(T.set (E.numK E.k₁) []).set (E.numK E.k₁) [E.outBit y], ?_, ?_⟩
  · simp only [Function.iterate_succ_apply, Function.iterate_zero, id, Nat.add_zero] at e1 ⊢
    rw [e1]
    simp only [exec, hs, topIndex, hget, List.tail_cons]
    rw [e2]
    simp only [exec, hpush]
    rw [e3]
    simp [exec, List.getD_eq_getElem?_getD, hlt]
  · simp [List.getD_eq_getElem?_getD, hlt]

end Env

section Compile

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

noncomputable def σEquiv : tm.σ ≃ Fin (@Fintype.card tm.σ tm.σFin) :=
  @Fintype.equivFin tm.σ tm.σFin

noncomputable def kEquiv : tm.K ≃ Fin (@Fintype.card tm.K tm.kFin) :=
  @Fintype.equivFin tm.K tm.kFin

noncomputable def flatList : List (TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  ((@Finset.univ tm.Λ tm.ΛFin).toList.map fun l => subs (tm.m l)).flatten

theorem flatList_placed (l : tm.Λ) : ∃ p, Placed (flatList tm) p (tm.m l) :=
  exists_placed tm.m _ l (by simp)

noncomputable def envOf : Env tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  nσ := @Fintype.card tm.σ tm.σFin
  nσ_pos := @Fintype.card_pos tm.σ tm.σFin ⟨tm.initialState⟩
  num v := (σEquiv tm v).val
  σof n := if h : n < @Fintype.card tm.σ tm.σFin then (σEquiv tm).symm ⟨n, h⟩ else tm.initialState
  σof_num v := by simp
  num_lt v := (σEquiv tm v).isLt
  nK := @Fintype.card tm.K tm.kFin
  numK k := (kEquiv tm k).val
  numK_lt k := (kEquiv tm k).isLt
  numK_inj := fun a b h => (kEquiv tm).injective (Fin.ext h)
  L := flatList tm
  start l := Classical.choose (flatList_placed tm l)
  placed_start l := Classical.choose_spec (flatList_placed tm l)
  k₀ := tm.k₀
  inSym n := eIn.symm (symOut n)
  k₁ := tm.k₁
  outBit y := bitCode (eOut y)

theorem compile :
    ∃ (c : Code) (d : ℕ), ∀ (l : List (Bool ⊕ Bool)) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map symIn) (d * n + d) [bitCode b] := by
  let E := envOf tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, fun l b n hrun => ?_⟩

  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y) (l.map symIn)
      (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have := E.decode_in (symIn_lt x)
    simpa [E, envOf, symOut_symIn] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map symIn)⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel

  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOf]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩

end Compile

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Machines.Compose
section

namespace PEqualNP.Library.Machines

open Turing

section update

variable {ι : Type} [DecidableEq ι] {β : ι → Type}

theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

end update

variable (M1 M2 : FinTM2)

abbrev CK : Type := Option (M1.K ⊕ M2.K)

abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k

abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool

abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

variable (M1 M2)

def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))

def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))

def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d

def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M2.Γk₀Fin
  { K := CK M1 M2
    k₀ := some (Sum.inl M1.k₀)
    k₁ := some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main := Sum.inl M1.main
    σ := Cσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }

variable {M1 M2}

def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk1 S) (some (Sum.inl k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk2 S) (some (Sum.inr k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]

theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩

def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩

theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))

theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)

theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)

def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u

theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]

theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _

theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.ComposeRun
section

namespace PEqualNP.Library.Machines

open Turing

variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)

abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)

theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]

theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]

theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]

theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]

theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp

theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp

theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp

theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl

theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FilterMap
section

namespace PEqualNP.Library.Machines

open Turing

variable {Γ₀ Γ₁ : Type}

abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁

def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
            | none => .goto fun _ => true)
          (.goto fun _ => true))
        .halt)

def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main := false
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := fmProg φ d

def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)

variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]

theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := fm φ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.TwoPass
section

namespace PEqualNP.Library.Machines

open Turing

inductive TPK : Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq

instance : Fintype TPK :=
  Fintype.ofList [.inp, .t1, .t2, .t3, .out] (fun x => by cases x <;> simp)

inductive TPL : Type
  | a | b | c | e
  deriving DecidableEq

instance : Fintype TPL :=
  Fintype.ofList [.a, .b, .c, .e] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ : Type}

abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | .inp => Γ₀
  | .t1 => Option Γ₀
  | .t2 => Option Γ₀
  | .t3 => Option Γ₀
  | .out => Γ₁

def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)

def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .t1 (fun s => s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t2 (fun s => s) (tpWrite φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t3 (fun s => s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d .e)
        .halt)

def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d

def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | .inp => l
  | .t1 => a
  | .t2 => b
  | .t3 => c
  | .out => u

theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .inp l' = st5 l' a b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t1 a' = st5 l a' b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t2 b' = st5 l a b' c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t3 c' = st5 l a b c' u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) .out u' = st5 l a b c u' := by
  funext k; cases k <;> simp [st5]

theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .inp l := by
  funext k; cases k <;> simp [st5]

theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .out u := by
  funext k; cases k <;> simp [st5]

abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)

variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]

theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]

theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]

theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]

theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]

theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]

theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]

theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]

theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some .a, s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp

theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .b, s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b, s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]

theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .c, s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c, s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp

theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .e, s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e, s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]

theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
        (l.length + 1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
    (l.length + 1) + (l.length + 1) + (l.length + 1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
      (l.length + 1)]
    (some (⟨some .a, none, Function.update (fun _ => []) .inp l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .a, none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]

theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.First
section

namespace PEqualNP.Library.Machines

open Turing

inductive FX
  | I | W | T | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.T, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => Bool ⊕ Bool
  | Sum.inr FX.W => Bool
  | Sum.inr FX.T => Bool
  | Sum.inr FX.O => Bool ⊕ Bool

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)

def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b

def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

variable {M}

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M)

def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }

variable {M}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.T => t
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i' = fstk S i' w t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w' = fstk S i w' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t' = fstk S i w t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o' = fstk S i w t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)

def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w t o⟩

theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FirstRun
section

namespace PEqualNP.Library.Machines

open Turing

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr FX.T) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr FX.O) = o := rfl
end fstk

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))

theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]

theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]

theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp

theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]

theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp

theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp

theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]

theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FirstPoly
section

namespace PEqualNP.Library.Machines

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])

theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])

theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl

theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]

theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Pairing
section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem filterMap_map_some {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

private theorem filterMap_map_none {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2

theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]

theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c

theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap

theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)

theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.AllTrue
section

namespace PEqualNP.Library.Machines

open Turing

abbrev AΓ : Bool → Type
  | false => Bool ⊕ Bool
  | true => Bool

def aval : Bool ⊕ Bool → Bool := Sum.elim id id

def atProg : Unit → TM2.Stmt AΓ Unit (Bool × Bool) :=
  fun _ => .pop false (fun s o => (s.1 && (o.map aval).getD true, o.isSome))
    (.branch (fun s => s.2)
      (.goto fun _ => ())
      (.push true (fun s => s.1) (.load (fun _ => (true, false)) .halt)))

def atM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := AΓ
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (true, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := atProg

def ast (l : List (Bool ⊕ Bool)) (u : List Bool) : ∀ k, List (AΓ k)
  | false => l
  | true => u

theorem ast_in (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u false = l := rfl

theorem ast_out (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u true = u := rfl

theorem ast_set_in (l l' : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (ast l u) false l' = ast l' u := by
  funext k
  cases k <;> simp [ast]

theorem ast_set_out (l : List (Bool ⊕ Bool)) (u u' : List Bool) :
    Function.update (ast l u) true u' = ast l u' := by
  funext k
  cases k <;> simp [ast]

theorem ast_start (l : List (Bool ⊕ Bool)) :
    ast l [] = Function.update (fun _ => [] : ∀ k, List (AΓ k)) false l := by
  funext k
  cases k <;> simp [ast]

theorem ast_end (u : List Bool) :
    ast [] u = Function.update (fun _ => [] : ∀ k, List (AΓ k)) true u := by
  funext k
  cases k <;> simp [ast]

abbrev ACfg : Type := TM2.Cfg AΓ Unit (Bool × Bool)

theorem at_cons (s : Bool × Bool) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast (x :: l) u⟩ : ACfg) =
      some ⟨some (), (s.1 && aval x, true), ast l u⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_set_in]

theorem at_nil (s : Bool × Bool) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast [] u⟩ : ACfg) =
      some ⟨none, (true, false), ast [] (s.1 :: u)⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_out, ast_set_in, ast_set_out]

theorem at_loop :
    ∀ (l : List (Bool ⊕ Bool)) (s : Bool × Bool),
      (flip bind (TM2.step atProg))^[l.length + 1]
          (some (⟨some (), s, ast l []⟩ : ACfg)) =
        some ⟨none, (true, false), ast [] [s.1 && l.all aval]⟩ := by
  intro l
  induction l with
  | nil =>
    intro s
    have h : (s.1 && ([] : List (Bool ⊕ Bool)).all aval) = s.1 := by simp
    rw [h]
    exact at_nil s []
  | cons x l ih =>
    intro s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step atProg)
        (some (⟨some (), s, ast (x :: l) []⟩ : ACfg)) =
        some ⟨some (), (s.1 && aval x, true), ast l []⟩ := at_cons s x l []
    rw [e, ih]
    simp [Bool.and_assoc]

theorem at_run (l : List (Bool ⊕ Bool)) :
    (flip bind (TM2.step atProg))^[l.length + 1]
        (some (initList atM l)) = some (haltList atM [l.all aval]) := by
  refine (congrArg (fun c => (flip bind (TM2.step atProg))^[l.length + 1]
    (some c)) (initList_eq atM l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq atM [l.all aval])).symm)
  show (flip bind (TM2.step atProg))^[l.length + 1]
    (some (⟨some (), (true, false), Function.update (fun _ => []) false l⟩ : ACfg)) =
    some (⟨none, (true, false), Function.update (fun _ => []) true [l.all aval]⟩ : ACfg)
  rw [← ast_start, at_loop, ← ast_end]
  simp

theorem all_aval_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).all aval = (p.1 ++ p.2).all id := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  unfold PEqualNP.Library.encodePair
  rw [List.all_append, List.all_append, h1, h2]

theorem allTrue_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => (p.1 ++ p.2).all id)) :=
  ⟨{
    tm := atM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun p =>
      { steps := (PEqualNP.Library.encodePair p).length + 1
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [(PEqualNP.Library.encodePair p).all aval] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool ((p.1 ++ p.2).all id)) := by
            rw [hm, all_aval_encodePair]
            rfl
          exact (congrArg (fun x => (flip bind (TM2.step atProg))^[
            (PEqualNP.Library.encodePair p).length + 1]
            (some (initList atM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((at_run (PEqualNP.Library.encodePair p)).trans
              (congrArg (fun x => some (haltList atM x)) hout))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.LenLE
section

namespace PEqualNP.Library.Machines.LenCmp

open Turing

abbrev LΓ : Bool × Bool → Type
  | (false, false) => Bool ⊕ Bool
  | (false, true) => Unit
  | (true, false) => Unit
  | (true, true) => Bool

inductive LL : Type
  | split
  | cmp
  | eraseA
  | eraseB
  deriving DecidableEq

instance : Fintype LL :=
  Fintype.ofList [LL.split, LL.cmp, LL.eraseA, LL.eraseB] (fun x => by cases x <;> simp)

def lenProg : LL → TM2.Stmt LΓ LL (Bool × Bool)
  | .split =>
    .pop (false, false) (fun _ o => (o.isSome, (o.map Sum.isRight).getD false))
      (.branch (fun s => s.1)
        (.branch (fun s => s.2)
          (.push (true, false) (fun _ => ()) (.goto fun _ => .split))
          (.push (false, true) (fun _ => ()) (.goto fun _ => .split)))
        (.goto fun _ => .cmp))
  | .cmp =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.pop (true, false) (fun s o => (s.1, o.isSome))
        (.branch (fun s => s.2)
          (.branch (fun s => s.1)
            (.goto fun _ => .cmp)
            (.load (fun _ => (false, false)) (.goto fun _ => .eraseB)))
          (.load (fun _ => (false, false)) (.goto fun _ => .eraseA))))
  | .eraseA =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseA)
        (.push (true, true) (fun _ => true) (.load (fun _ => (false, false)) .halt)))
  | .eraseB =>
    .pop (true, false) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseB)
        (.push (true, true) (fun _ => false) (.load (fun _ => (false, false)) .halt)))

def lenM : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := LΓ
  Λ := LL
  main := .split
  σ := Bool × Bool
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := lenProg

def lst (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) : ∀ k, List (LΓ k)
  | (false, false) => l
  | (false, true) => List.replicate a ()
  | (true, false) => List.replicate b ()
  | (true, true) => o

theorem lst_in (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, false) = l := rfl

theorem lst_a (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, true) = List.replicate a () := rfl

theorem lst_b (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, false) = List.replicate b () := rfl

theorem lst_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, true) = o := rfl

theorem lst_set_in (l l' : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, false) l' = lst l' a b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (Bool ⊕ Bool)) (a a' b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, true) (List.replicate a' ()) = lst l a' b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (Bool ⊕ Bool)) (a b b' : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) (List.replicate b' ()) = lst l a b' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b0 (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) [] = lst l a 0 o :=
  lst_set_b l a b 0 o

theorem lst_set_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o o' : List Bool) :
    Function.update (lst l a b o) (true, true) o' = lst l a b o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (Bool ⊕ Bool)) :
    lst l 0 0 [] = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst [] 0 0 o = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

abbrev LCfg : Type := TM2.Cfg LΓ LL (Bool × Bool)

abbrev lenStep : Option LCfg → Option LCfg := flip bind (TM2.step lenProg)

theorem split_inl (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inl x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, false), lst l (a + 1) b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inl, Option.getD_some, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_a, ← List.replicate_succ, lst_set_a]

theorem split_inr (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inr x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, true), lst l a (b + 1) o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inr, Option.getD_some, Bool.cond_true]
  rw [lst_set_in, lst_b, ← List.replicate_succ, lst_set_b]

theorem split_nil (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst [] a b o⟩ : LCfg) =
      some ⟨some .cmp, (false, false), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Option.map_none,
    Option.getD_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_ss (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] (a + 1) (b + 1) o⟩ : LCfg) =
      some ⟨some .cmp, (true, true), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
  rw [lst_set_a, lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem cmp_b0 (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] a 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (false, false), lst [] (a - 1) 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_b0]

theorem cmp_a0 (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (false, false), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.replicate_succ, List.head?_nil, List.head?_cons,
    List.tail_cons, Option.isSome_none, Option.isSome_some, Bool.cond_false, Bool.cond_true]
  rw [lst_set_b]

theorem eraseA_s (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] (a + 1) 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (true, s.2), lst [] a 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_a]

theorem eraseA_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (true :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem eraseB_s (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (true, s.2), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem eraseB_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (false :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b, List.tail_replicate, lst_set_b]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (Bool ⊕ Bool)) (a b : ℕ) (s : Bool × Bool),
      lenStep^[l.length + 1] (some (⟨some .split, s, lst l a b []⟩ : LCfg)) =
        some ⟨some .cmp, (false, false),
          lst [] (a + l.countP Sum.isLeft) (b + l.countP Sum.isRight) []⟩ := by
  intro l
  induction l with
  | nil => intro a b s; exact split_nil s a b []
  | cons x l ih =>
    intro a b s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inl x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, false), lst l (a + 1) b []⟩ := split_inl s x l a b []
      have h1 : a + 1 + l.countP Sum.isLeft =
          a + (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isRight =
          (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]
    | inr x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inr x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, true), lst l a (b + 1) []⟩ := split_inr s x l a b []
      have h1 : b + 1 + l.countP Sum.isRight =
          b + (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isLeft =
          (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]

theorem cmpLoopT :
    ∀ (b c : ℕ) (s : Bool × Bool),
      lenStep^[b + 1] (some (⟨some .cmp, s, lst [] (b + c) b []⟩ : LCfg)) =
        some ⟨some .eraseA, (false, false), lst [] (c - 1) 0 []⟩ := by
  intro b
  induction b with
  | zero =>
    intro c s
    rw [Nat.zero_add c]
    exact cmp_b0 s c []
  | succ b ih =>
    intro c s
    rw [Function.iterate_succ_apply]
    have hbc : b + 1 + c = b + c + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (b + 1 + c) (b + 1) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] (b + c) b []⟩ := by
      rw [hbc]; exact cmp_ss s (b + c) b []
    rw [e, ih]

theorem cmpLoopF :
    ∀ (a d : ℕ) (s : Bool × Bool),
      lenStep^[a + 1] (some (⟨some .cmp, s, lst [] a (a + 1 + d) []⟩ : LCfg)) =
        some ⟨some .eraseB, (false, false), lst [] 0 d []⟩ := by
  intro a
  induction a with
  | zero =>
    intro d s
    have h : 0 + 1 + d = d + 1 := by omega
    rw [h]
    exact cmp_a0 s d []
  | succ a ih =>
    intro d s
    rw [Function.iterate_succ_apply]
    have had : a + 1 + 1 + d = a + 1 + d + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (a + 1) (a + 1 + 1 + d) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] a (a + 1 + d) []⟩ := by
      rw [had]; exact cmp_ss s a (a + 1 + d) []
    rw [e, ih]

theorem eraseALoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseA, s, lst [] n 0 []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [true]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseA_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseA, s, lst [] (n + 1) 0 []⟩ : LCfg)) =
        some ⟨some .eraseA, (true, s.2), lst [] n 0 []⟩ := eraseA_s s n []
    rw [e, ih]

theorem eraseBLoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseB, s, lst [] 0 n []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [false]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseB_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseB, s, lst [] 0 (n + 1) []⟩ : LCfg)) =
        some ⟨some .eraseB, (true, s.2), lst [] 0 n []⟩ := eraseB_s s n []
    rw [e, ih]

theorem len_run (l : List (Bool ⊕ Bool)) (a b : ℕ) (ha : l.countP Sum.isLeft = a)
    (hb : l.countP Sum.isRight = b) (hab : a + b ≤ l.length) :
    ∃ n, n ≤ 2 * l.length + 3 ∧
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
  have hs := splitLoop l 0 0 (false, false)
  rw [Nat.zero_add, Nat.zero_add, ha, hb] at hs
  have key : ∀ n : ℕ,
      lenStep^[n] (some (⟨some .split, (false, false), lst l 0 0 []⟩ : LCfg)) =
        some (⟨none, (false, false), lst [] 0 0 [decide (b ≤ a)]⟩ : LCfg) →
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
    intro n h
    refine (congrArg (fun c => lenStep^[n] (some c)) (initList_eq lenM l)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq lenM [decide (b ≤ a)])).symm)
    show lenStep^[n]
      (some (⟨some .split, (false, false), Function.update (fun _ => []) (false, false) l⟩ :
        LCfg)) =
      some (⟨none, (false, false),
        Function.update (fun _ => []) (true, true) [decide (b ≤ a)]⟩ : LCfg)
    rw [← lst_start, ← lst_end]
    exact h
  by_cases h : b ≤ a
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨(c - 1 + 1) + ((b + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (b ≤ b + c) = true := by simp
    rw [Function.iterate_add_apply _ (c - 1 + 1) _, Function.iterate_add_apply _ (b + 1) _, hs,
      cmpLoopT, eraseALoop, hd]
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    refine ⟨(d + 1) + ((a + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (a + 1 + d ≤ a) = false := decide_eq_false h
    rw [Function.iterate_add_apply _ (d + 1) _, Function.iterate_add_apply _ (a + 1) _, hs,
      cmpLoopF, eraseBLoop, hd]

theorem countP_isLeft_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isLeft = p.1.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isLeft =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isLeft = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.add_zero]

theorem countP_isRight_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isRight = p.2.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isRight =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isRight = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.zero_add]

theorem lenLE_run (p : List Bool × List Bool) :
    ∃ n, n ≤ 2 * (PEqualNP.Library.encodePair p).length + 3 ∧
      lenStep^[n] (some (initList lenM (PEqualNP.Library.encodePair p))) =
        some (haltList lenM [decide (p.2.length ≤ p.1.length)]) :=
  len_run (PEqualNP.Library.encodePair p) p.1.length p.2.length
    (countP_isLeft_encodePair p) (countP_isRight_encodePair p)
    (by simp [PEqualNP.Library.encodePair])

theorem lenLE_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length))) :=
  ⟨{
    tm := lenM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := Classical.choose (lenLE_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.2.length ≤ p.1.length)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.2.length ≤ p.1.length))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => lenStep^[Classical.choose (lenLE_run p)]
            (some (initList lenM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((Classical.choose_spec (lenLE_run p)).2.trans
              (congrArg (fun x => some (haltList lenM x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (lenLE_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.Library.Machines.LenCmp
end

-- upstream PEqualNP.Library.Machines.FirstG
section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

inductive FX
  | I | W | TA | TB | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.TA, FX.TB, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2) (A B C : Type)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => A ⊕ C
  | Sum.inr FX.W => C
  | Sum.inr FX.TA => A
  | Sum.inr FX.TB => B
  | Sum.inr FX.O => B ⊕ C

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr FX.TA) (fun s => getA s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => getC s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.TA) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.TB) (fun s => getB s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.TB) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.TA => ta
  | Sum.inr FX.TB => tb
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr FX.TA) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr FX.TB) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr FX.O) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.I) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.W) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TA) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TB) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.O) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

variable (M A B C) in

abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Library.Machines.Gen
end

-- upstream PEqualNP.Library.Machines.FirstGRun
section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l4), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _ | _) <;> rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines.Gen
end

-- upstream PEqualNP.Library.Machines.Mul
section

namespace PEqualNP.Library.Machines

open Turing

inductive MulK
  | I | A | B | C | O
  deriving DecidableEq

instance : Fintype MulK :=
  Fintype.ofList [.I, .A, .B, .C, .O] (fun x => by cases x <;> simp)

inductive MulL
  | split | outer | copy | back | clean
  deriving DecidableEq

instance : Fintype MulL :=
  Fintype.ofList [.split, .outer, .copy, .back, .clean] (fun x => by cases x <;> simp)

abbrev MulΓ : MulK → Type
  | .I => Bool ⊕ Bool
  | .A => Bool
  | .B => Bool
  | .C => Bool
  | .O => Bool

def mulProg : MulL → TM2.Stmt MulΓ MulL (Option Bool)
  | .split =>
    .pop .I (fun _ o => o.map Sum.isLeft)
      (.branch (fun s => s.isSome)
        (.branch (fun s => s == some true)
          (.push .A (fun _ => true) (.goto fun _ => .split))
          (.push .B (fun _ => true) (.goto fun _ => .split)))
        (.goto fun _ => .outer))
  | .outer =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .copy)
        (.goto fun _ => .clean))
  | .copy =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .C (fun _ => true) (.push .O (fun _ => true) (.goto fun _ => .copy)))
        (.goto fun _ => .back))
  | .back =>
    .pop .C (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .clean =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .clean)
        .halt)

def mulTM : FinTM2 where
  K := MulK
  k₀ := .I
  k₁ := .O
  Γ := MulΓ
  Λ := MulL
  main := .split
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := mulProg

def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) : ∀ k, List (MulΓ k)
  | .I => i
  | .A => a
  | .B => b
  | .C => c
  | .O => o

@[simp] theorem mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .I = i := rfl
@[simp] theorem mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .A = a := rfl
@[simp] theorem mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .B = b := rfl
@[simp] theorem mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .C = c := rfl
@[simp] theorem mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .O = o := rfl

@[simp] theorem mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    Function.update (mstk i a b c o) .I i' = mstk i' a b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
    Function.update (mstk i a b c o) .A a' = mstk i a' b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
    Function.update (mstk i a b c o) .B b' = mstk i a b' c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
    Function.update (mstk i a b c o) .C c' = mstk i a b c' o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
    Function.update (mstk i a b c o) .O o' = mstk i a b c o' := by
  funext k; cases k <;> simp [mstk]

theorem mstk_start (i : List (Bool ⊕ Bool)) :
    mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .I i := by
  funext k; cases k <;> simp [mstk]

theorem mstk_end (o : List Bool) :
    mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .O o := by
  funext k; cases k <;> simp [mstk]

abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)

abbrev mulStep : Option MulCfg → Option MulCfg := flip bind (TM2.step mulProg)

theorem split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inl y :: i) a b c o⟩) =
      some ⟨some .split, some true, mstk i (true :: a) b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inr y :: i) a b c o⟩) =
      some ⟨some .split, some false, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_nil (s : Option Bool) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk [] a b c o⟩) =
      some ⟨some .outer, none, mstk [] a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i (y :: a) b c o⟩) =
      some ⟨some .copy, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i [] b c o⟩) =
      some ⟨some .clean, none, mstk i [] b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .copy, some y, mstk i a b (true :: c) (true :: o)⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a [] c o⟩) =
      some ⟨some .back, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b (y :: c) o⟩) =
      some ⟨some .back, some y, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b [] o⟩) =
      some ⟨some .outer, none, mstk i a b [] o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .clean, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a [] c o⟩) =
      some ⟨none, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem splitLoopW (a : List Bool) :
    ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
      mulStep^[w.length + 1] (some ⟨some .split, s, mstk (w.map Sum.inr) a (rep b) [] []⟩) =
        some ⟨some .outer, none, mstk [] a (rep (w.length + b)) [] []⟩ := by
  intro w
  induction w with
  | nil => intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, split_inr, rep_succ, ih]
    rw [show w.length + (b + 1) = w.length + 1 + b from by omega]

theorem splitLoopX (w : List Bool) :
    ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
      mulStep^[x.length + (w.length + 1)]
          (some ⟨some .split, s, mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
        some ⟨some .outer, none, mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [List.length_cons, show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
      from by omega, Function.iterate_succ_apply, List.map_cons, List.cons_append, split_inl,
      rep_succ, ih]
    rw [show x.length + (a + 1) = x.length + 1 + a from by omega]

theorem copyLoop (a : List Bool) :
    ∀ (b c o : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .copy, s, mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some .back, none, mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
  intro b
  induction b with
  | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [Function.iterate_succ_apply, ← rep_succ b, copy_cons, rep_succ, rep_succ, ih]
    rw [show b + (c + 1) = b + 1 + c from by omega, show b + (o + 1) = b + 1 + o from by omega]

theorem backLoop (a o : List Bool) :
    ∀ (c b : ℕ) (s : Option Bool),
      mulStep^[c + 1] (some ⟨some .back, s, mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some .outer, none, mstk [] a (rep (c + b)) [] o⟩ := by
  intro c
  induction c with
  | zero => intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← rep_succ c, back_cons, rep_succ, ih]
    rw [show c + (b + 1) = c + 1 + b from by omega]

theorem outerLoop (b : ℕ) :
    ∀ (a o : ℕ) (s : Option Bool),
      mulStep^[a * (2 * b + 3) + 1] (some ⟨some .outer, s, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .clean, none, mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
  intro a
  induction a with
  | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
      from by ring, Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
      Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
      Function.iterate_succ_apply mulStep (b + 1), ← rep_succ a, outer_cons]
    have h1 : mulStep^[b + 1]
        (some ⟨some .copy, some true, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2 : mulStep^[b + 1]
        (some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
        some ⟨some .outer, none, mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
      backLoop (rep a) (rep (b + o)) b 0 none
    rw [h2, ih]
    rw [show a * b + (b + o) = (a + 1) * b + o from by ring]

theorem cleanLoop (o : List Bool) :
    ∀ (b : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .clean, s, mstk [] [] (rep b) [] o⟩) =
        some ⟨none, none, mstk [] [] [] [] o⟩ := by
  intro b
  induction b with
  | zero => intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [Function.iterate_succ_apply, ← rep_succ b, clean_cons, ih]

def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))

theorem mul_run (x w : List Bool) :
    (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList mulTM (rep (x.length * w.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some .split, none, Function.update (fun _ => []) .I
      (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (rep (x.length * w.length))⟩ : MulCfg)
  rw [← mstk_start, ← mstk_end, mulSteps, Function.iterate_add_apply mulStep (w.length + 1),
    Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
  have h1 : mulStep^[x.length + (w.length + 1)]
      (some ⟨some .split, none, mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
      some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
      (some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some .clean, none, mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2, cleanLoop]

theorem mul_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow, encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Clock
section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem cpt_mul {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime

private theorem pow_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (n : ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ n) true) := by
  induction n with
  | zero => simpa using hconst [true]
  | succ n ih =>
    have h := cpt_mul cpt_id ih
    have e : (fun x : List Bool =>
        List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool => List.replicate (x.length ^ (n + 1)) true) := by
      funext x
      rw [List.length_replicate, pow_succ, Nat.mul_comm]
    rw [← e]
    exact h

theorem clock_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (p : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h := cpt_comp (cpt_pair hp hq) cpt_append
    have e : (fun x : List Bool => List.replicate (p.eval x.length) true ++
        List.replicate (q.eval x.length) true) =
        (fun x : List Bool => List.replicate ((p + q).eval x.length) true) := by
      funext x
      rw [Polynomial.eval_add, List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h := cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
    have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
      funext x
      rw [List.length_replicate, List.length_replicate, Polynomial.eval_monomial]
    rw [← e]
    exact h

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.ConstList
section

namespace PEqualNP.Library.Machines

open Turing

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a

theorem constList_polyTime (l : List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => l)) :=
  ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.L055
section

theorem PEqualNP.Library.L055 : ∀ p : Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
  fun p => PEqualNP.Library.Machines.clock_polyTime
    (fun l => PEqualNP.Library.Machines.constList_polyTime l) p
end

-- upstream PEqualNP.Library.Machines.NormalForm
section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

def nfDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

theorem nfDec_encodePair (q : List Bool × List Bool) : nfDec (encodePair q) = q := by
  obtain ⟨x, w⟩ := q
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [nfDec, encodePair, List.filterMap_append, h1, h2, h3, h4, List.append_nil,
    List.nil_append]

theorem nfDec_polyTime :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair nfDec := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
    (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
  intro l
  simp only [nfDec, encodePair, List.map_filterMap]

theorem nf_restrict {β βΓ : Type} {eb : β → List βΓ} {F : List (Bool ⊕ Bool) → β}
    (h : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) eb F) :
    ComputableInPolyTime encodePair eb (fun q => F (encodePair q)) := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun (encodePair q)⟩⟩

theorem nf_and {A B : List (Bool ⊕ Bool) → Bool}
    (hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool A)
    (hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool B) :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => B l && A l) := by
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  have dup : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l)
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun l => (l, l)) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro l
    have e1 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inl (β := Bool ⊕ Bool) s)) = l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have e2 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inr (α := Bool ⊕ Bool) s)) = l.map Sum.inr := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp only [Gen.gpair, e1, e2]
  have s1 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (A p.1, p.2)) :=
    Gen.first_polyTime (C := Bool ⊕ Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool A cA
  have sw : ComputableInPolyTime
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p => (p.2, [p.1])) := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
    rintro ⟨b, l⟩
    have h1 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun _ => none) (fun b => some (Sum.inl (β := Bool) b)) s) =
        l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have h2 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun b => some (Sum.inr (α := Bool ⊕ Bool) b)) (fun _ => none) s) = [] := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp [Gen.gpair, Computability.encodeBool, h2]
    exact (h1 l).symm
  have s2 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (B p.1, p.2)) :=
    Gen.first_polyTime (C := Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool B cB
  have cv : ComputableInPolyTime
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      encodePair (fun p => (([p.1], p.2) : List Bool × List Bool)) := by
    refine filterMap_polyTime _ _ _ (fun s => some s) ?_
    intro p
    simp only [List.filterMap_some]
    rfl
  have h := cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp dup s1) sw) s2) cv)
    allTrue_polyTime
  have e : (fun l : List (Bool ⊕ Bool) => B l && A l) =
      (fun l : List (Bool ⊕ Bool) => ([B l] ++ [A l]).all id) := by
    funext l; simp
  rw [e]; exact h

theorem nf_decider (fR : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (cR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => decide (q.2.length ≤ p.eval q.1.length) && fR q) := by
  have hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => fR (nfDec l)) := cpt_comp nfDec_polyTime cR
  have hB0 := cpt_comp (cpt_comp nfDec_polyTime (cpt_first (PEqualNP.Library.L055 p)))
    LenCmp.lenLE_polyTime
  have hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) := by
    have e : (fun l : List (Bool ⊕ Bool) =>
        decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) =
        (fun l : List (Bool ⊕ Bool) => decide ((nfDec l).2.length ≤
          (List.replicate (p.eval (nfDec l).1.length) true).length)) := by
      funext l; simp
    rw [e]; exact hB0
  have h := nf_restrict (nf_and hA hB)
  have e : (fun q : List Bool × List Bool =>
      decide (q.2.length ≤ p.eval q.1.length) && fR q) =
      (fun q : List Bool × List Bool =>
        decide ((nfDec (encodePair q)).2.length ≤ p.eval (nfDec (encodePair q)).1.length) &&
          fR (nfDec (encodePair q))) := by
    funext q; rw [nfDec_encodePair]
  rw [e]; exact h

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.L045
section

theorem PEqualNP.Library.L045 : ∀ L ∈ PEqualNP.Library.NP, ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair R ∧ (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) ∧ ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R := by
  rintro L ⟨R, p, ⟨fR, hfR, cR⟩, hL⟩
  refine ⟨{q | q.2.length ≤ p.eval q.1.length ∧ q ∈ R}, p,
    ⟨fun q => decide (q.2.length ≤ p.eval q.1.length) && fR q, fun q => ?_,
      PEqualNP.Library.Machines.nf_decider fR p cR⟩, fun x w h => h.1, fun x => hL x⟩
  exact (and_congr decide_eq_true_iff.symm (hfR q)).trans Bool.and_eq_true_iff.symm
end

-- upstream PEqualNP.Library.Helpers.PolyExp
section

namespace PEqualNP.Library.Helpers

theorem polynomial_le_pow_add (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, Polynomial.eval n p ≤ n ^ k + k := by
  have small : ∀ (n e : ℕ), n < 2 → n ^ e ≤ 1 := fun n e hn => by
    have := Nat.pow_le_pow_left (show n ≤ 1 by omega) e
    rwa [Nat.one_pow] at this
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 2, fun n => ?_⟩
    rw [Polynomial.eval_add]
    have h1 := ha n
    have h2 := hb n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n a hn
      have e2 := small n b hn
      omega
    · have pa : n ^ a ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have pb : n ^ b ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have ps : n ^ (a + b + 1) = n ^ (a + b) * n := Nat.pow_succ ..
      have pt : n ^ (a + b + 1) ≤ n ^ (a + b + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * n ^ (a + b) ≤ n ^ (a + b) * n := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hn
      omega
  | monomial d c =>
    refine ⟨d + c, fun n => ?_⟩
    rw [Polynomial.eval_monomial]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n d hn
      calc c * n ^ d ≤ c * 1 := Nat.mul_le_mul_left _ e1
        _ ≤ n ^ (d + c) + (d + c) := by omega
    · have hc : c ≤ n ^ c := (Nat.lt_pow_self (by omega)).le
      calc c * n ^ d ≤ n ^ c * n ^ d := Nat.mul_le_mul_right _ hc
        _ = n ^ (d + c) := by rw [Nat.add_comm, Nat.pow_add]
        _ ≤ n ^ (d + c) + (d + c) := Nat.le_add_right _ _

theorem polynomial_le_two_pow_pow_add (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, Polynomial.eval n p ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨k, hk⟩ := polynomial_le_pow_add p
  exact ⟨k, fun n => (hk n).trans (Nat.add_le_add_right Nat.lt_two_pow_self.le k)⟩

end PEqualNP.Library.Helpers
end

-- upstream PEqualNP.Library.L048
section

theorem PEqualNP.Library.L048 : PEqualNP.Library.NP ⊆ PEqualNP.Library.NEXP := by
  intro L hL
  obtain ⟨R, p, hR, hlen, hmem⟩ := PEqualNP.Library.L045 L hL
  obtain ⟨k, hk⟩ := PEqualNP.Library.Helpers.polynomial_le_two_pow_pow_add p
  refine ⟨R, k, hR, fun x => ?_⟩
  rw [hmem x]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (hlen x w hw).trans (hk _), hw⟩, fun ⟨w, _, hw⟩ => ⟨w, hw⟩⟩
end

-- upstream PEqualNP.Library.Universal.Lazy
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem map_symIn_encodePair' (x w : List Bool) :
    (encodePair (x, w)).map symIn =
      x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2) := by
  simp only [encodePair, List.map_append, List.map_map]
  congr 1 <;> (apply List.map_congr_left; intro b _; cases b <;> rfl)

theorem np_code (L : Language Bool) (hL : L ∈ NP) :
    ∃ (c : Code) (q : Polynomial ℕ),
      (∀ (y : List Bool) (t : ℕ), q.eval y.length ≤ t → y ∈ L →
        ∃ w : List Bool, V (pairB (encCode c) (pairB y (un t)), w) = true) ∧
      (∀ (y : List Bool) (t : ℕ) (w : List Bool),
        V (pairB (encCode c) (pairB y (un t)), w) = true → y ∈ L) := by
  obtain ⟨R, p, ⟨fR, hfR, ⟨cR⟩⟩, hbound, hL⟩ := L045 L hL
  obtain ⟨c, d, hc⟩ := compile cR.tm cR.inputAlphabet cR.outputAlphabet
  have hrun : ∀ x w : List Bool, ∃ n, n ≤ cR.time.eval (x.length + w.length) ∧
      c.outputsWithin (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2))
        (d * n + d) [bitCode (fR (x, w))] := by
    intro x w
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cR.time.eval (encodePair (x, w)).length ∧
        (flip bind (Turing.TM2.step cR.tm.m))^[n]
          (some (Turing.initList cR.tm ((encodePair (x, w)).map cR.inputAlphabet.invFun))) =
        some (Turing.haltList cR.tm [cR.outputAlphabet.invFun (fR (x, w))]) :=
      ⟨(cR.outputsFun (x, w)).steps, (cR.outputsFun (x, w)).steps_le_m,
        (cR.outputsFun (x, w)).evals_in_steps⟩
    have h := hc (encodePair (x, w)) (fR (x, w)) n hev
    rw [map_symIn_encodePair'] at h
    refine ⟨n, ?_, h⟩
    simpa [encodePair] using hn
  let q : Polynomial ℕ :=
    p + Polynomial.C d * cR.time.comp (Polynomial.X + p) + Polynomial.C d
  have hq : ∀ n : ℕ, q.eval n = p.eval n + d * cR.time.eval (n + p.eval n) + d := by
    intro n
    simp [q, Polynomial.eval_comp]
  refine ⟨c, q, ?_, ?_⟩
  · intro x t ht hx
    obtain ⟨w, hw⟩ := (hL x).1 hx
    have hwl : w.length ≤ p.eval x.length := hbound x w hw
    have hwt : w.length ≤ q.eval x.length := by rw [hq]; omega
    refine ⟨w, (V_spec c x w t).2 ⟨hwt.trans ht, ?_⟩⟩
    obtain ⟨n, hn, ho⟩ := hrun x w
    have hfw : fR (x, w) = true := (hfR (x, w)).1 hw
    rw [hfw] at ho
    have hle : d * n + d ≤ q.eval x.length := by
      rw [hq]
      have h1 : n ≤ cR.time.eval (x.length + p.eval x.length) :=
        hn.trans (eval_mono _ (by omega))
      have h2 : d * n ≤ d * cR.time.eval (x.length + p.eval x.length) :=
        Nat.mul_le_mul_left d h1
      omega
    exact Code.outputsWithin_mono c _ (hle.trans ht) _ ho
  · intro x t w hVw
    obtain ⟨-, ho⟩ := (V_spec c x w t).1 hVw
    obtain ⟨n, -, ho'⟩ := hrun x w
    have h1 := Code.outputsWithin_mono c _ (le_max_left t (d * n + d)) _ ho
    have h2 := Code.outputsWithin_mono c _ (le_max_right t (d * n + d)) _ ho'
    have heq : [1] = [bitCode (fR (x, w))] := h1.2.symm.trans h2.2
    have hfw : fR (x, w) = true := by
      cases hb : fR (x, w) with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    exact (hL x).2 ⟨w, (hfR (x, w)).2 hfw⟩

theorem V_budget (cs x b w : List Bool) :
    V (pairB cs (pairB x b), w) = V (pairB cs (pairB x (un b.length)), w) := by
  simp [V, unpairB_pairB]

theorem V_length (cs x b w : List Bool) (h : V (pairB cs (pairB x b), w) = true) :
    w.length ≤ b.length := by
  simp only [V, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

def zc (cs au : List Bool) (m : ℕ) : List Bool := pairB cs (pairB au (un m))

theorem zc_length (cs au : List Bool) (m : ℕ) :
    (zc cs au m).length = (zc cs au 0).length + m := by
  simp [zc, pairB_length]
  omega

theorem zc_succ (cs au : List Bool) (m : ℕ) : zc cs au m ++ [true] = zc cs au (m + 1) := by
  simp [zc, pairB, un, List.replicate_succ']

theorem csOf_zc (cs au : List Bool) (m : ℕ) : csOf (zc cs au m) = cs := by
  simp [csOf, zc, unpairB_pairB]

theorem muOf_zc (cs au : List Bool) (m : ℕ) : muOf (zc cs au m) = un m := by
  simp [muOf, zc, unpairB_pairB]

theorem y0Of_zc (cs au : List Bool) (m : ℕ) : y0Of (zc cs au m) = zc cs au 0 := by
  simp [y0Of, zc, unpairB_pairB]

theorem un_tail (m : ℕ) : (un m).tail = un (m - 1) := by
  cases m <;> simp [un, List.replicate_succ]

theorem RD_below (cs au : List Bool) (m : ℕ) (w : List Bool)
    (hC : ¬ (zc cs au 0).length ≤ Nat.size (Nat.size m)) :
    RD (zc cs au m, w) =
      V (pairB cs (pairB (zc cs au (m + 1)) (unpairB w).2), (unpairB w).1) := by
  simp [RD, csOf_zc, muOf_zc, y0Of_zc, condC_un, hC, zc_succ]

theorem RD_at (cs au : List Bool) (m : ℕ) (w : List Bool)
    (hC : (zc cs au 0).length ≤ Nat.size (Nat.size m))
    (hC' : ¬ (zc cs au 0).length ≤ Nat.size (Nat.size (m - 1))) :
    RD (zc cs au m, w) = true ↔
      ∀ w' : List Bool, V (pairB cs (pairB (zc cs au 0) (un (Nat.size m))), w') = false := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hC' hC
  simp only [RD, csOf_zc, muOf_zc, y0Of_zc, condC_un, un_tail, hC, hC', decide_true,
    decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_or,
    List.isEmpty_iff, srch_eq_nil, lgU_un, List.length_append, un_length]
  constructor
  · intro h w'
    by_contra hV
    rw [Bool.not_eq_false] at hV
    have hlen : w'.length ≤ Nat.size m := by simpa using V_length _ _ _ _ hV
    have h1 := idx_lt_of_length_le hlen
    have h2 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (by
      have : 0 < Nat.size m := Nat.size_pos.2 (by omega)
      omega)
    have h3 : 2 ^ (Nat.size m + 1) = 2 ^ (Nat.size m - 1) * 4 := by
      have : Nat.size m + 1 = (Nat.size m - 1) + 2 := by
        have : 0 < Nat.size m := Nat.size_pos.2 (by omega)
        omega
      rw [this, pow_add]; norm_num
    have h4 := h (idx w') (by omega)
    rw [cand_idx, hV] at h4
    exact Bool.noConfusion h4
  · intro h j _
    exact h _

private theorem arith1 (k n : ℕ) (h : k + 3 ≤ n) : 3 * ((n + 1) ^ k + k) + 1 ≤ 2 ^ (n ^ 2) := by
  have h1 : (n + 1) ^ k ≤ 2 ^ (n * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self k
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hA : 0 < 2 ^ (n * k) := by positivity
  have hB : 0 < 2 ^ k := by positivity
  have h3 : 2 ^ (n * k + k + 3) = 8 * (2 ^ (n * k) * 2 ^ k) := by
    rw [pow_add, pow_add]; ring
  have h4 : 2 ^ (n * k + k + 3) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  nlinarith [Nat.mul_le_mul hA hB]

private theorem arith2 (k s : ℕ) (h : 2 * k + 2 ≤ s) :
    (2 ^ (2 * s)) ^ k + k ≤ 2 ^ (2 ^ (2 * s) - 1) := by
  have h1 : (2 ^ (2 * s)) ^ k = 2 ^ (2 * s * k) := (pow_mul 2 (2 * s) k).symm
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : 2 ^ k ≤ 2 ^ (2 * s * k) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h4 : 2 ^ (2 * s * k + 1) = 2 * 2 ^ (2 * s * k) := by rw [pow_succ]; ring
  have h5 : s < 2 ^ s := Nat.lt_two_pow_self
  have h6 : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [two_mul, pow_add]
  have h7 : 2 * s * k + 1 ≤ 2 ^ (2 * s) - 1 := by
    have : 2 * s * k + 2 ≤ 2 ^ s * 2 ^ s := by nlinarith
    omega
  have h8 : 2 ^ (2 * s * k + 1) ≤ 2 ^ (2 ^ (2 * s) - 1) :=
    Nat.pow_le_pow_right (by omega) h7
  omega

theorem DLang_not_NP : DLang ∉ PEqualNP.Library.NP := by
  intro hD
  obtain ⟨c, q, hfwd, hbwd⟩ := np_code DLang hD
  obtain ⟨k, hk⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add q

  have hs5 : 2 * k + (encCode c).length + 3 < 2 ^ (2 * k + (encCode c).length + 3) :=
    Nat.lt_two_pow_self
  have hn6 : 2 ^ (2 * (2 * k + (encCode c).length + 3)) =
      2 ^ (2 * k + (encCode c).length + 3) * 2 ^ (2 * k + (encCode c).length + 3) := by
    rw [two_mul, pow_add]
  have hn2 : 2 ^ (2 * (2 * k + (encCode c).length + 3)) =
      2 * 2 ^ (2 * (2 * k + (encCode c).length + 3) - 1) := by
    rw [← pow_succ']; congr 1
  have hnbig : 2 * (2 * k + (encCode c).length + 3) ≤
      2 ^ (2 * (2 * k + (encCode c).length + 3)) := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 * (encCode c).length + 2 * a + 2 =
      2 ^ (2 * (2 * k + (encCode c).length + 3)) :=
    ⟨2 ^ (2 * (2 * k + (encCode c).length + 3) - 1) - (encCode c).length - 1, by omega⟩
  have harith2 := arith2 k (2 * k + (encCode c).length + 3) (by omega)
  generalize 2 ^ (2 * (2 * k + (encCode c).length + 3)) = n at *
  generalize hcs : encCode c = cs at *
  have hl : (zc cs (un a) 0).length = n := by
    simp [zc, pairB_length]
    omega
  have hz : ∀ m, (zc cs (un a) m).length = n + m := fun m => by rw [zc_length, hl]

  have hroom : ∀ N : ℕ, n ≤ N → 3 * q.eval (N + 1) + 1 ≤ 2 ^ (N ^ 2) + 2 := by
    intro N hN
    have h1 := hk (N + 1)
    have h2 := arith1 k N (by omega)
    omega

  have hex : ∃ m : ℕ, n ≤ Nat.size (Nat.size m) := by
    refine ⟨2 ^ 2 ^ n, ?_⟩
    rw [Nat.size_pow]
    have h1 : n < Nat.size (2 ^ n + 1) := Nat.lt_size.2 (by omega)
    exact h1.le
  classical
  let E := Nat.find hex
  have hE : n ≤ Nat.size (Nat.size E) := Nat.find_spec hex
  have hEmin : ∀ m, m < E → ¬ n ≤ Nat.size (Nat.size m) := fun m hm => Nat.find_min hex hm
  have hE0 : E ≠ 0 := by
    intro h0
    rw [h0] at hE
    simp at hE
    omega

  have hbud : q.eval n ≤ Nat.size E := by
    have h1 : n - 1 < Nat.size (Nat.size E) := by omega
    rw [Nat.lt_size] at h1
    have h2 := hk n
    omega

  have hstep : ∀ m, m < E → (zc cs (un a) m ∈ DLang ↔ zc cs (un a) (m + 1) ∈ DLang) := by
    intro m hm
    have hC : ¬ (zc cs (un a) 0).length ≤ Nat.size (Nat.size m) := by
      rw [hl]; exact hEmin m hm
    constructor
    · rintro ⟨w, -, hw⟩
      rw [RD_below _ _ _ _ hC, V_budget] at hw
      exact hbwd _ _ _ hw
    · intro hmem
      obtain ⟨w', hw'⟩ := hfwd (zc cs (un a) (m + 1)) (q.eval (n + m + 1)) (by rw [hz, Nat.add_assoc]) hmem
      have hlen : w'.length ≤ q.eval (n + m + 1) := by simpa using V_length _ _ _ _ hw'
      refine ⟨pairB w' (un (q.eval (n + m + 1))), ?_, ?_⟩
      · rw [pairB_length, un_length, hz]
        have := hroom (n + m) (by omega)
        omega
      · rw [RD_below _ _ _ _ hC, unpairB_pairB]
        exact hw'
  have hchain : ∀ m, m ≤ E → (zc cs (un a) 0 ∈ DLang ↔ zc cs (un a) m ∈ DLang) := by
    intro m
    induction m with
    | zero => intro _; exact Iff.rfl
    | succ m ih => intro hm; exact (ih (by omega)).trans (hstep m (by omega))

  have hdiag : zc cs (un a) E ∈ DLang ↔ ¬ zc cs (un a) 0 ∈ DLang := by
    have hC : (zc cs (un a) 0).length ≤ Nat.size (Nat.size E) := by rw [hl]; exact hE
    have hC' : ¬ (zc cs (un a) 0).length ≤ Nat.size (Nat.size (E - 1)) := by
      rw [hl]; exact hEmin _ (by omega)
    constructor
    · rintro ⟨w, -, hw⟩ hmem
      rw [RD_at _ _ _ _ hC hC'] at hw
      obtain ⟨w', hw'⟩ := hfwd (zc cs (un a) 0) (Nat.size E) (by rw [hl]; exact hbud) hmem
      rw [hw w'] at hw'
      exact Bool.noConfusion hw'
    · intro hnot
      refine ⟨[], by simp, (RD_at _ _ _ _ hC hC').2 fun w' => ?_⟩
      by_contra hV
      rw [Bool.not_eq_false] at hV
      exact hnot (hbwd _ _ _ hV)
  have h := (hchain E le_rfl).trans hdiag
  by_cases h0 : zc cs (un a) 0 ∈ DLang
  · exact (h.1 h0) h0
  · exact h0 (h.2 h0)

theorem NP_ssubset_NEXP_of (hRD : PEqualNP.Library.ComputableInPolyTime
    PEqualNP.Library.encodePair Computability.encodeBool RD) :
    PEqualNP.Library.NP ⊂ PEqualNP.Library.NEXP := by
  have hmem : DLang ∈ PEqualNP.Library.NEXP :=
    ⟨{p | RD p = true}, 2, ⟨RD, fun _ => Iff.rfl, hRD⟩, fun _ => Iff.rfl⟩
  refine ⟨PEqualNP.Library.L048, fun hsub => DLang_not_NP (hsub hmem)⟩

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Machines.Iter
section

namespace PEqualNP.Library.Machines.Iter

open Turing

inductive IX
  | I | C | T | O
  deriving DecidableEq

instance : Fintype IX :=
  Fintype.ofList [IX.I, IX.C, IX.T, IX.O] (fun x => by cases x <;> simp)

inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq

instance : Fintype IL :=
  Fintype.ofList [IL.l1, IL.l2, IL.l3, IL.l4, IL.l5, IL.l6] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr IX.I => Bool ⊕ Bool
  | Sum.inr IX.C => Bool
  | Sum.inr IX.T => Bool
  | Sum.inr IX.O => Bool

abbrev ItΛ : Type := M.Λ ⊕ IL

abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)

variable {M}

def trI : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr IL.l4)

variable (M)

def iterProg (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l => trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1)))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr IL.l2))
        (.goto fun _ => Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => Sum.inl M.main)
        (.goto fun _ => Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l4))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o => (s.1, o.map fun y => Sum.inl (d₀ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l5))
        (.goto fun _ => Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.O) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l6))
        .halt)

def iterM (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ IX
    k₀ := Sum.inr IX.I
    k₁ := Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main := Sum.inr IL.l1
    σ := Itσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := iterProg M e₀ d₀ e₁ }

variable {M}

def istk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    ∀ k, List (ItΓ M k)
  | Sum.inl k => S k
  | Sum.inr IX.I => i
  | Sum.inr IX.C => cn
  | Sum.inr IX.T => t
  | Sum.inr IX.O => o

section istk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)

@[simp] theorem istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] theorem istk_I : istk S i cn t o (Sum.inr IX.I) = i := rfl
@[simp] theorem istk_C : istk S i cn t o (Sum.inr IX.C) = cn := rfl
@[simp] theorem istk_T : istk S i cn t o (Sum.inr IX.T) = t := rfl
@[simp] theorem istk_O : istk S i cn t o (Sum.inr IX.O) = o := rfl

theorem istk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x = istk (Function.update S k x) i cn t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem istk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i' = istk S i' cn t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_C (cn' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn' = istk S i cn' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_T (t' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t' = istk S i cn t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_O (o' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o' = istk S i cn t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end istk

abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)

def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl), (c.var, b), istk c.stk i cn t o⟩

theorem simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trI q) ((v, b) : Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← istk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← istk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepI (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
    (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)

theorem embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (l : List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
  rw [initList_eq]; rfl

theorem embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (m : List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
  rw [haltList_eq]; rfl

theorem istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k, List (ItΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem istk_nil_I (i : List (Bool ⊕ Bool)) :
    (istk (fun _ => []) i [] [] [] : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.I) i :=
  (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])

theorem istk_nil_O (o : List Bool) :
    (istk (fun _ => []) [] [] [] o : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.O) o :=
  (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])

end PEqualNP.Library.Machines.Iter
end

-- upstream PEqualNP.Library.Machines.IterRun
section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)


variable (v : M.σ) (S : ∀ k, List (M.Γ k))

theorem i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_T, isFst, bit]

theorem i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_C, isFst, bit]

theorem i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S [] cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk S [] cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I]

theorem iloop1 (o : List Bool) :
    ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
        (some (⟨some (Sum.inr IL.l1), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]

theorem i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l3), (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l3), (v, none),
        istk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i (a :: cn) t o⟩ : ICfg M) =
      some ⟨some (Sum.inl M.main), (v, some (Sum.inl a)), istk S i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i [] t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, none), istk S i [] t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk (Function.update S M.k₁ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4), (v, b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, none), istk (Function.update S M.k₀ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6), (v, none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5), (v, b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_O, bit]

theorem i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨none, (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
    ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨none, (v, none), istk S i cn [] (t.reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem update_nil_nil (k : M.K) :
    Function.update (fun _ => [] : ∀ k, List (M.Γ k)) k [] = fun _ => [] :=
  Function.update_eq_self k (fun _ => [] : ∀ k, List (M.Γ k))

theorem main_loop (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)), z.length + k * cn.length ≤ L →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_map, List.length_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hgz : (g z).length ≤ z.length + k := hk z
    have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (by omega)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iter_polyTime (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (k : ℕ) (hk : ∀ y : List Bool, (g y).length ≤ y.length + k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n, hn, hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length + u.length + k * (y.length + u.length)) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    have hmul : u.length * (Polynomial.eval (y.length + u.length + k * (y.length + u.length))
          c.time + 2 * (y.length + u.length + k * (y.length + u.length)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          (y.length + u.length + k * (y.length + u.length)) c.time +
            2 * (y.length + u.length + k * (y.length + u.length)) + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize k * (y.length + u.length) = B at hmul ⊢
    omega
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter
end

-- upstream PEqualNP.Library.Machines.IterMeasure
section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)


theorem main_loop_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length, (g^[j] z).length ≤ L) →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    simp only [List.length_reverse, List.length_map, List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    have hgz : (g z).length ≤ L := hL 1 (by omega)
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (fun j hj => by
      have := hL (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length, (g^[j] y).length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iterate_length_measure (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) :
    ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h1 := hm (g^[j] y)
    have h2 := hg (g^[j] y)
    obtain ⟨i1, i2⟩ := ih
    generalize j * m y = A at i2 ⊢
    exact ⟨by omega, by omega⟩

theorem measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
    A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
  omega

theorem iter_polyTime_measure (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ :=
    Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hL : ∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
      intro j hj
      have h1 := (iterate_length_measure g m hm hg y j).2
      have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n, hn, hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
      (y.length + u.length * (a * y.length + a)) hL
    have hLV : y.length + u.length * (a * y.length + a) ≤
        (y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp := eval_mono c.time hLV
    have hmul : u.length * (Polynomial.eval (y.length + u.length * (a * y.length + a)) c.time +
          2 * (y.length + u.length * (a * y.length + a)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          ((y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a))
            c.time +
            2 * ((y.length + u.length) +
              (y.length + u.length) * (a * (y.length + u.length) + a)) + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter
end

-- upstream PEqualNP.Library.Universal.Prims
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem fm_elim {A B C : Type} (φl : A → Option C) (φr : B → Option C) (x : List A)
    (w : List B) :
    (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr := by
  have h1 : ∀ x : List A, (x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  have h2 : ∀ w : List B, (w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
    intro w; induction w with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [List.filterMap_append, h1, h2]

private theorem fm_some {A C : Type} (g : A → C) (l : List A) :
    l.filterMap (fun a => some (g a)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem fm_none {A C : Type} (l : List A) :
    l.filterMap (fun _ : A => (none : Option C)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have hA : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (p.1, p.1 ++ p.2)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
    rintro ⟨x, w⟩
    simp only [encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_some, fm_none]
    simp
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
    refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true))
      (fun _ => some false) () ?_
    intro a
    induction a with
    | nil => rfl
    | cons b l ih =>
      simp only [fstRun, List.map_cons, List.cons_append, Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x, w⟩
  simp [pairB, un]

theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := constList_polyTime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']

theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp

theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf : ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h

theorem cpt_pairG {α αΓ : Type} [Fintype αΓ] [Inhabited αΓ] {ea : α → List αΓ}
    {f g : α → List Bool}
    (hf : ComputableInPolyTime ea (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime ea (fun x : List Bool => x) g) :
    ComputableInPolyTime ea encodePair (fun a => (f a, g a)) := by
  obtain ⟨cf⟩ := hf
  obtain ⟨cg⟩ := hg
  have s0 : ComputableInPolyTime ea (fun a : α => Gen.gpair (ea a, ea a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro a
    simp only [Gen.gpair, fm_some]
  have s1 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, ea a))
      (fun a : α => Gen.gpair (f a, ea a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := αΓ) ea (fun x : List Bool => x) f cf
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, ea a)⟩⟩
  have s2 : ComputableInPolyTime (fun a : α => Gen.gpair (f a, ea a))
      (fun a : α => Gen.gpair (ea a, f a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : αΓ => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : αΓ => none)) ?_
    intro a
    simp only [Gen.gpair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  have s3 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, f a))
      (fun a : α => Gen.gpair (g a, f a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea (fun x : List Bool => x) g cg
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, f a)⟩⟩
  have s4 : ComputableInPolyTime (fun a : α => Gen.gpair (g a, f a))
      encodePair (fun a : α => (f a, g a)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : Bool => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : Bool => none)) ?_
    intro a
    simp only [Gen.gpair, encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp s0 s1) s2) s3) s4

private def encT (u : List Bool) : List Bool := u.flatMap (fun b => [true, b])

private def encF (v : List Bool) : List Bool := v.flatMap (fun b => [false, b])

private def twD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem twD_run (l : List Bool) :
    fstRun twD (fun _ => none) false l = [] ∧
      fstRun twD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, twD, ih.1, ih.2]

private def e0D : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, none, none)
  | false, false => (true, none, none)
  | true, b => (true, some false, some b)

private theorem e0D_run_true (l : List Bool) :
    fstRun2 e0D (fun _ => none) true l = encF l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, e0D, encF, ih]

private theorem e0D_run_false (l : List Bool) :
    fstRun2 e0D (fun _ => none) false l = encF (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, e0D, ih, e0D_run_true]

private def mkD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d, false), t => ((d || !t, true), some (t || !d))
  | (d, true), b => ((d, false), some b)

private def mk (l : List Bool) : List Bool := fstRun mkD (fun _ => none) (false, false) l

private theorem mkD_length (q : Bool × Bool) (l : List Bool) :
    (fstRun mkD (fun _ => none) q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih => obtain ⟨d, ph⟩ := q; cases ph <;> simp [fstRun, mkD, ih]

private theorem mkD_done (v : List Bool) :
    fstRun mkD (fun _ => none) (true, false) (encF v) = encF v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, mkD, encF] at ih ⊢; exact ih

private theorem mkD_marked (u r : List Bool) :
    fstRun mkD (fun _ => none) (false, false) (encT u ++ r) =
      encT u ++ fstRun mkD (fun _ => none) (false, false) r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, mkD, encT] at ih ⊢; exact ih

private theorem mk_nil (u : List Bool) : mk (encT u ++ encF []) = encT u ++ encF [] := by
  unfold mk; rw [mkD_marked]; rfl

private theorem mk_cons (u : List Bool) (b : Bool) (v : List Bool) :
    mk (encT u ++ encF (b :: v)) = encT (u ++ [b]) ++ encF v := by
  unfold mk
  rw [mkD_marked]
  have h : fstRun mkD (fun _ => none) (false, false) (encF (b :: v)) =
      true :: b :: encF v := by
    have h' := mkD_done v
    simp [fstRun, mkD, encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]

private theorem mk_iter (k : ℕ) : ∀ u t : List Bool,
    mk^[k] (encT u ++ encF t) = encT (u ++ t.take k) ++ encF (t.drop k) := by
  induction k with
  | zero => intro u t; simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => rw [mk_nil, ih]; simp
    | cons b t => rw [mk_cons, ih]; simp

private def dcD : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, t => (some t, none)
  | some t, b => (none, some (if t then Sum.inl b else Sum.inr b))

private theorem dcD_F (v : List Bool) :
    fstRun dcD (fun _ => none) none (encF v) = v.map Sum.inr := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, dcD, encF] at ih ⊢; exact ih

private theorem dcD_T (u r : List Bool) :
    fstRun dcD (fun _ => none) none (encT u ++ r) =
      u.map Sum.inl ++ fstRun dcD (fun _ => none) none r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, dcD, encT] at ih ⊢; exact ih

private def rawDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

private theorem rawDec_tagged (u v : List Bool) :
    rawDec (u.map Sum.inl ++ v.map Sum.inr) = (u, v) := by
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [rawDec, List.filterMap_append, h1, h2, h3, h4, List.append_nil, List.nil_append]

theorem cpt_unpairB :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
  have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _ => none) true (fun s => (twD_run s).2.symm)
  have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _ => none) false (fun s => (e0D_run_false s).symm)
  have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
    fst_polyTime _ _ _ mkD (fun _ => none) (false, false) (fun _ => rfl)
  obtain ⟨cMk⟩ := hMk
  have hIt := Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk, mkD_length])
  have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List Bool => fstRun dcD (fun _ => none) none l) :=
    fst_polyTime _ _ _ dcD (fun _ => none) none (fun _ => rfl)
  have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
      (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec, encodePair, List.map_filterMap]
  refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h := mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
  have e : encT [] ++ encF (s.dropWhile id).tail = encF (s.dropWhile id).tail := rfl
  rw [e] at h
  simp only [h, List.nil_append]
  rw [dcD_T, dcD_F, rawDec_tagged]
  rfl

theorem cpt_iterB (g : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y, m (g y) ≤ m y) (hgl : ∀ y, (g y).length ≤ y.length + m y)
    (ha : ∀ y, m y ≤ a * y.length + a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => g^[(unpairB s).2.length] (unpairB s).1) := by
  obtain ⟨c⟩ := hg
  exact cpt_comp cpt_unpairB (Iter.iter_polyTime_measure g c m a hm hgl ha)

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.PrimsCPT
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private def hdD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem hdD_run (l : List Bool) :
    fstRun hdD (fun _ => none) false l = [] ∧
      fstRun hdD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, hdD, ih.1, ih.2]

theorem cpt_hd :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
  fst_polyTime _ _ _ hdD (fun _ => none) true (fun s => (hdD_run s).2.symm)

private def dnD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, b => (true, some b)

private theorem dnD_true (l : List Bool) : fstRun dnD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, dnD, ih]

private theorem dnD_false (l : List Bool) :
    fstRun dnD (fun _ => none) false l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dnD, ih, dnD_true]

theorem cpt_dropN :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropN :=
  fst_polyTime _ _ _ dnD (fun _ => none) false (fun s => (dnD_false s).symm)

private def tlD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, b => (true, some b)

private theorem tlD_true (l : List Bool) : fstRun tlD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tlD, ih]

private theorem tlD_false (l : List Bool) : fstRun tlD (fun _ => none) false l = l.tail := by
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, tlD, tlD_true]

theorem cpt_tail :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail) :=
  fst_polyTime _ _ _ tlD (fun _ => none) false (fun s => (tlD_false s).symm)

private def tkD : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, none)

private theorem tkD_none (l : List Bool) : fstRun tkD (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tkD, ih]

private theorem tkD_some (b : Bool) (l : List Bool) :
    fstRun tkD (fun _ => none) (some b) l = takeLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, tkD, takeLA, ih, tkD_none]

theorem cpt_takeL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) takeL :=
  fst_polyTime _ _ _ tkD (fun _ => none) (some false) (fun s => (tkD_some false s).symm)

private def drD : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (none, some b)
  | some _, true => (some true, none)
  | some true, false => (some false, none)
  | some false, false => (none, none)

private theorem drD_none (l : List Bool) : fstRun drD (fun _ => none) none l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, drD, ih]

private theorem drD_some (b : Bool) (l : List Bool) :
    fstRun drD (fun _ => none) (some b) l = dropLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, drD, dropLA, ih, drD_none]

theorem cpt_dropL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropL :=
  fst_polyTime _ _ _ drD (fun _ => none) (some false) (fun s => (drD_some false s).symm)

private def hlD : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, some false)

private theorem hlD_none (l : List Bool) : fstRun hlD (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, hlD, ih]

private theorem hlD_some (b : Bool) (l : List Bool) :
    fstRun hlD (fun _ => none) (some b) l = headLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, hlD, headLA, ih, hlD_none]

theorem cpt_headL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headL :=
  fst_polyTime _ _ _ hlD (fun _ => none) (some false) (fun s => (hlD_some false s).symm)

private def ppD : Option Bool → Bool → Option Bool × Option Bool
  | none, true => (some false, none)
  | none, false => (some true, some false)
  | some false, true => (some false, none)
  | some false, false => (some true, none)
  | some true, b => (some true, some b)

private theorem ppD_true (l : List Bool) : fstRun ppD (fun _ => none) (some true) l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ppD, ih]

private theorem ppD_false (l : List Bool) :
    fstRun ppD (fun _ => none) (some false) l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, ppD, ih, ppD_true]

private theorem ppD_none (l : List Bool) : fstRun ppD (fun _ => none) none l = popT l := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [fstRun, ppD, popT, dropN, ppD_true, ppD_false]

theorem cpt_popT :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) popT :=
  fst_polyTime _ _ _ ppD (fun _ => none) none (fun s => (ppD_none s).symm)

private theorem blank_run (l : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) () l = blank l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, blank] at ih ⊢; exact ih

theorem cpt_blank :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) blank :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) ()
    (fun s => (blank_run s).symm)

private def spD : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, some false)
  | _, false => ((), some false, none)

private theorem spD_run (l : List Bool) : fstRun2 spD (fun _ => none) () l = spread l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, spD, spread] at ih ⊢ <;> exact ih

theorem cpt_spread :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) spread :=
  fst2_polyTime _ _ _ spD (fun _ => none) () (fun s => (spD_run s).symm)

private def buD : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, none)
  | _, false => ((), some true, some false)

private theorem buD_run (l : List Bool) : fstRun2 buD (fun _ => none) () l = bump l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, buD, bump] at ih ⊢ <;> exact ih

theorem cpt_bump :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bump :=
  fst2_polyTime _ _ _ buD (fun _ => none) () (fun s => (buD_run s).symm)

theorem cpt_const (l : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l) :=
  constList_polyTime l

theorem cpt_mulU :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => mulU p.1 p.2) :=
  cptc mul_polyTime (fun _ => rfl)

theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) :=
  cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)

theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) :=
  cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)

theorem cpt_app2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => u s ++ v s) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)

theorem cpt_pairB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)

theorem cpt_mulU2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ => rfl)

theorem cpt_sel {f a b : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (f s) (a s) (b s)) := by
  have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h : f s = [] <;> simp [sel, h]

theorem cpt_iterLen {g cnt arg : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (hgl : ∀ s, (g s).length ≤ s.length)
    (hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt)
    (harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

theorem cpt_move :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) move :=
  cptc (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropL)
    (cpt_app2 cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_headL))) (fun _ => rfl)

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.VerifyCPT
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines


private theorem cptv {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem cpt_hNst {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => hNst (f s)) :=
  cptv (cpt_comp (cpt_comp hf cpt_hd) cpt_tail) (fun _ => rfl)

private theorem cpt_hPc {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => hPc (f s)) :=
  cptv (cpt_comp (cpt_comp hf cpt_dropN) cpt_hd) (fun _ => rfl)

private theorem cpt_hSt {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => hSt (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN) cpt_hd) cpt_tail)
    (fun _ => rfl)

private theorem cpt_hKin {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => hKin (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN) cpt_dropN)
    cpt_hd) cpt_tail) (fun _ => rfl)

private theorem cpt_hKout {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => hKout (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN)
    cpt_dropN) cpt_dropN) cpt_hd) cpt_tail) (fun _ => rfl)

private theorem cpt_iterLen1 {g cnt arg : List Bool → List Bool} (hg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) g)
    (hgl : ∀ s, (g s).length ≤ s.length + 1) (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt) (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 1 hgl
  exact cptv (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

private theorem cpt_iterS (hstep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sstep) {cnt arg : List Bool → List Bool}
    (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt) (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => sstep^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hstep
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => sstep^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure sstep c smeasure 7 smeasure_sstep sstep_length smeasure_le
  exact cptv (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

private theorem cpt_splitK_u39 {kf sk : List Bool → List Bool} (hkf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) kf) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => splitK (kf s) (sk s)) :=
  cptv (cpt_iterLen1 cpt_move move_length hkf (cpt_pairB2 hsk (cpt_const [])))
    (fun _ => rfl)

private theorem cpt_insK {kf new sk : List Bool → List Bool} (hkf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) kf) (hnew : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) new)
    (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => insK (kf s) (new s) (sk s)) := by
  have h := cpt_splitK_u39 hkf hsk
  have h1 := cpt_comp h cpt_unpairB1
  have h2 := cpt_comp h cpt_unpairB2
  exact cptv (cpt_sel h1 h2 (cpt_app2 h2 (cpt_app2 hnew h1))) (fun _ => rfl)

private theorem cpt_inSyms {x w : List Bool → List Bool} (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) (hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) w) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => inSyms (x s) (w s)) :=
  cptv (cpt_app2 (cpt_comp (cpt_comp hx cpt_spread) cpt_bump)
    (cpt_comp (cpt_comp (cpt_comp (cpt_comp hw cpt_spread) cpt_bump) cpt_bump) cpt_bump))
    (fun _ => rfl)

private theorem cpt_initS {cs x w : List Bool → List Bool} (hcs : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cs) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x)
    (hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) w) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => initS (cs s) (x s) (w s)) := by
  have h1 := cpt_comp hcs cpt_unpairB1
  have h2 := cpt_comp hcs cpt_unpairB2
  exact cptv (cpt_pairB2 h1 (cpt_pairB2 (cpt_hPc h2) (cpt_pairB2 (cpt_hSt h2)
    (cpt_insK (cpt_hKin h2) (cpt_inSyms hx hw) (cpt_comp (cpt_hNst h2) cpt_blank)))))
    (fun _ => rfl)

private theorem cpt_stkS {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => stkS (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp hf cpt_unpairB2) cpt_unpairB2) cpt_unpairB2)
    (fun _ => rfl)

private inductive O4 : Type
  | s0 | s1 | s2 | s3 | ok | bad
  deriving DecidableEq

private instance : Fintype O4 :=
  Fintype.ofList [.s0, .s1, .s2, .s3, .ok, .bad] (fun x => by cases x <;> simp)

private def o4D : O4 → Bool → O4 × Option Bool
  | .s0, true => (.s1, none)
  | .s1, true => (.s2, none)
  | .s2, false => (.s3, none)
  | .s3, false => (.ok, none)
  | .ok, _ => (.ok, none)
  | _, _ => (.bad, none)

private def o4F : O4 → Option Bool
  | .ok => some true
  | _ => none

private theorem o4_ok (l : List Bool) : fstRun o4D o4F .ok l = [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_bad (l : List Bool) : fstRun o4D o4F .bad l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_run (l : List Bool) :
    fstRun o4D o4F .s0 l = if l.take 4 = [true, true, false, false] then [true] else [] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [fstRun, o4F]
  · cases a <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> cases d <;> simp [fstRun, o4D, o4_ok, o4_bad]

private theorem cpt_o4 :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun l : List Bool => if l.take 4 = [true, true, false, false] then [true] else []) :=
  fst_polyTime _ _ _ o4D o4F .s0 (fun s => (o4_run s).symm)

private theorem ne_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_ne :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, ne_true, Computability.encodeBool])

private theorem comb (a : Bool) (A : List Bool) (p : Prop) [Decidable p] :
    (!(sel (if a then [true] else []) []
      (sel (sel A [true] []) [] (sel (if p then [true] else []) [] [true]))).isEmpty) =
      (a && (A.isEmpty && decide p)) := by
  cases a <;> cases A <;> by_cases h : p <;> simp [sel, h]

private theorem cpt_VS (hstep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sstep) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB s).2)) := by
  have hz : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have hcs : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).1).1) :=
    cptv (cpt_comp hz cpt_unpairB1) (fun _ => rfl)
  have hr : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).1).2) :=
    cptv (cpt_comp hz cpt_unpairB2) (fun _ => rfl)
  have hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB (unpairB s).1).2).1) :=
    cptv (cpt_comp hr cpt_unpairB1) (fun _ => rfl)
  have hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB (unpairB s).1).2).2) :=
    cptv (cpt_comp hr cpt_unpairB2) (fun _ => rfl)
  have hit := cpt_iterS hstep hb (cpt_initS hcs hx hw)
  have hc2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB (unpairB s).1).1).2) :=
    cptv (cpt_comp hcs cpt_unpairB2) (fun _ => rfl)
  have hko := cpt_hKout hc2
  have hD := cpt_iterLen cpt_dropL dropL_length hko (cpt_stkS hit)
  have f3 := cpt_comp hD cpt_o4
  have hA := cpt_comp (cpt_comp hit cpt_unpairB2) cpt_unpairB1
  have f2 := cpt_sel hA (cpt_const [true]) (cpt_const [])
  have f1 := cpt_bitFlag (cpt_comp (cpt_pair hb hw) LenCmp.lenLE_polyTime)
  have all := cpt_sel f1 (cpt_const []) (cpt_sel f2 (cpt_const [])
    (cpt_sel f3 (cpt_const []) (cpt_const [true])))
  exact cptv (cpt_comp all cpt_ne) (fun s => comb _ _ _)

theorem cpt_V (hstep : PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) sstep) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool V :=
  cptv (cpt_comp cpt_pairB (cpt_VS hstep)) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.SStepCPT
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines


private theorem cptE {f f' : List Bool → List Bool} (h : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) (e : ∀ a, f a = f' a) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_hd1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => hd (f y)) :=
  cpt_comp hf cpt_hd

theorem cpt_dropN1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => dropN (f y)) :=
  cpt_comp hf cpt_dropN

theorem cpt_tail1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (f y).tail) :=
  cpt_comp hf cpt_tail

theorem cpt_takeL1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => takeL (f y)) :=
  cpt_comp hf cpt_takeL

theorem cpt_popT1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => popT (f y)) :=
  cpt_comp hf cpt_popT

theorem cpt_unpairB1_1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB (f y)).1) :=
  cptE (cpt_comp hf cpt_unpairB1) (fun _ => rfl)

theorem cpt_unpairB2_1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB (f y)).2) :=
  cptE (cpt_comp hf cpt_unpairB2) (fun _ => rfl)

theorem cpt_cons1 (b : Bool) {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => b :: f y) :=
  cptE (cpt_app2 (cpt_const [b]) hf) (fun _ => rfl)

theorem cpt_iterGrow {g cnt arg : List Bool → List Bool} (hg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) g) (k : ℕ)
    (hgl : ∀ s, (g s).length ≤ s.length + k) (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt) (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c k hgl
  exact cptE (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

theorem cpt_fetch {ps pc : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fetch (ps y) (pc y)) := by
  unfold fetch
  exact cpt_takeL1 (cpt_iterLen cpt_dropL dropL_length (cpt_tail1 hpc) hps)

theorem cpt_fOp {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fOp (I y)) := by
  unfold fOp
  exact cpt_hd1 hI

theorem cpt_fK {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fK (I y)) := by
  unfold fK
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 hI))

theorem cpt_fW {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fW (I y)) := by
  unfold fW
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN1 {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fN1 (I y)) := by
  unfold fN1
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN2 {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fN2 (I y)) := by
  unfold fN2
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_fTb {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fTb (I y)) := by
  unfold fTb
  exact cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_lookup {tb idx : List Bool → List Bool} (htb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) tb) (hidx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) idx) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => lookup (tb y) (idx y)) := by
  unfold lookup
  exact cpt_tail1 (cpt_hd1 (cpt_iterLen cpt_dropN dropN_length hidx htb))

theorem cpt_splitK {kf sk : List Bool → List Bool} (hkf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) kf) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => splitK (kf y) (sk y)) := by
  unfold splitK
  exact cpt_iterGrow cpt_move 1 move_length hkf (cpt_pairB2 hsk (cpt_const []))

theorem cpt_pcSel {pc o n1 n2 valS : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hn1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n1) (hn2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n2) (hv : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valS) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => pcSel (pc y) (o y) (n1 y) (n2 y) (valS y)) := by
  unfold pcSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  have h5 := cpt_tail1 h4
  have h6 := cpt_tail1 h5
  exact cpt_sel hpc hpc (cpt_sel ho (cpt_const []) (cpt_sel h1 hn1 (cpt_sel h2 hn1
    (cpt_sel h3 hn1 (cpt_sel h4 hn1 (cpt_sel h5 (cpt_sel hv hn2 hn1)
      (cpt_sel h6 (cpt_cons1 true hv) (cpt_const []))))))))

theorem cpt_stSel {pc o st valS valT : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hvS : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valS) (hvT : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valT) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => stSel (pc y) (o y) (st y) (valS y) (valT y)) := by
  unfold stSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  exact cpt_sel hpc hst (cpt_sel ho hst (cpt_sel h1 hst (cpt_sel h2 hvT (cpt_sel h3 hvT
    (cpt_sel h4 hvS hst)))))

theorem cpt_skSel {pc o sk r d pushed : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) (hr : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) r) (hd' : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) d) (hp : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pushed) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => skSel (pc y) (o y) (sk y) (r y) (d y) (pushed y)) := by
  unfold skSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  exact cpt_sel hpc hsk (cpt_sel ho hsk (cpt_sel h1
    (cpt_sel hr hd' (cpt_app2 hd' (cpt_app2 hp hr)))
    (cpt_sel h2 (cpt_app2 hd' (cpt_popT1 hr)) hsk)))

theorem cpt_pcOut {ps pc st : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => pcOut (ps y) (pc y) (st y)) := by
  unfold pcOut
  have hI := cpt_fetch hps hpc
  exact cpt_pcSel hpc (cpt_fOp hI) (cpt_fN1 hI) (cpt_fN2 hI) (cpt_lookup (cpt_fTb hI) hst)

theorem cpt_stOut {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => stOut (ps y) (pc y) (st y) (sk y)) := by
  unfold stOut
  have hI := cpt_fetch hps hpc
  have hT := cpt_fTb hI
  exact cpt_stSel hpc (cpt_fOp hI) hst (cpt_lookup hT hst)
    (cpt_lookup hT (cpt_app2 (cpt_mulU2 hst (cpt_fW hI))
      (cpt_hd1 (cpt_unpairB1_1 (cpt_splitK (cpt_fK hI) hsk)))))

theorem cpt_skOut {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => skOut (ps y) (pc y) (st y) (sk y)) := by
  unfold skOut
  have hI := cpt_fetch hps hpc
  have hS := cpt_splitK (cpt_fK hI) hsk
  exact cpt_skSel hpc (cpt_fOp hI) hsk (cpt_unpairB1_1 hS) (cpt_unpairB2_1 hS)
    (cpt_app2 (cpt_cons1 true (cpt_lookup (cpt_fTb hI) hst)) (cpt_const [false]))

theorem cpt_sstepParts {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => sstepParts (ps y) (pc y) (st y) (sk y)) := by
  unfold sstepParts
  exact cpt_pairB2 hps (cpt_pairB2 (cpt_pcOut hps hpc hst)
    (cpt_pairB2 (cpt_stOut hps hpc hst hsk) (cpt_skOut hps hpc hst hsk)))

theorem cpt_sstep : PEqualNP.Library.ComputableInPolyTime
    (fun x : List Bool => x) (fun x : List Bool => x) sstep := by
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB y).2) := cpt_unpairB2
  have h22 := cpt_unpairB2_1 h2
  have h : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => sstepParts (unpairB y).1 (unpairB (unpairB y).2).1
      (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2) :=
    cpt_sstepParts cpt_unpairB1 (cpt_unpairB1_1 h2) (cpt_unpairB1_1 h22) (cpt_unpairB2_1 h22)
  exact h

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.LazyCPT
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines


private theorem cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem cpt_half : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

private theorem cpt_lgStep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) lgStep :=
  cptl (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 cpt_half)))
    (fun _ => rfl)

private theorem lgStep_length (s : List Bool) : (lgStep s).length ≤ s.length + 2 := by
  have h := unpairB_length s
  unfold lgStep sel
  split
  · omega
  · rename_i hne
    have h1 : 1 ≤ (unpairB s).2.length := by
      rcases hb : (unpairB s).2 with _ | ⟨b, l⟩
      · exact absurd hb hne
      · simp
    rw [pairB_length, half_eq, un_length, List.length_cons]
    omega

private theorem cpt_lgU {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => lgU (f s)) :=
  cptl (cpt_unpairB1_1 (cpt_iterGrow cpt_lgStep 2 lgStep_length hf
    (cpt_pairB2 (cpt_const []) hf))) (fun _ => rfl)

private theorem cpt_condC {y mu : List Bool → List Bool} (hy : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) y) (hmu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) mu) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => if condC (y s) (mu s) then [true] else []) :=
  cptl (cpt_bitFlag (cpt_comp (cpt_pair (cpt_lgU (cpt_lgU hmu)) hy) LenCmp.lenLE_polyTime))
    (fun _ => rfl)

private theorem cpt_succB : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) succB :=
  fst_polyTime _ _ _ succD succFin true (fun _ => rfl)

private theorem succD_length (q : Bool) (s : List Bool) :
    (fstRun succD succFin q s).length ≤ s.length + 1 := by
  induction s generalizing q with
  | nil => cases q <;> simp [fstRun, succFin]
  | cons b l ih =>
    have h1 := ih b
    have h2 := ih false
    cases q <;> simp [fstRun, succD] <;> omega

private theorem succB_length (s : List Bool) : (succB s).length ≤ s.length + 1 :=
  succD_length true s

private theorem bflag_length (b : Bool) : (bflag b).length ≤ 1 := by
  cases b <;> simp [bflag]

private theorem srchStep_length (s : List Bool) : (srchStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := succB_length (unpairB (unpairB s).2).1
  have h4 := bflag_length (V ((unpairB s).1, (unpairB (unpairB s).2).1))
  unfold srchStep
  rw [pairB_length, pairB_length, List.length_append]
  omega

private theorem cpt_srchStep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) srchStep := by
  have hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have hc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hF hc) (cpt_V cpt_sstep)
  have hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))) :=
    cptl (cpt_bitFlag hV) (fun _ => rfl)
  have hs : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => succB (unpairB (unpairB s).2).1) := cpt_comp hc cpt_succB
  exact cptl (cpt_pairB2 hF (cpt_pairB2 hs (cpt_app2 hfl hb))) (fun _ => rfl)

private theorem cpt_srch {F n : List Bool → List Bool} (hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) F) (hn : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => srch (F s) (n s)) :=
  cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow cpt_srchStep 5 srchStep_length hn
    (cpt_pairB2 hF (cpt_pairB2 (cpt_const []) (cpt_const [])))))) (fun _ => rfl)

private theorem neL_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neL :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neL_true, Computability.encodeBool])

private theorem combL (a b v : Bool) (S : List Bool) :
    (!(sel (if a then [true] else []) (if v then [true] else [])
      (sel (if b then [true] else []) (sel S [true] []) [])).isEmpty) =
      ((!a && v) || (a && (!b && S.isEmpty))) := by
  cases a <;> cases b <;> cases v <;> cases S <;> simp [sel]

private theorem cpt_RDS :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => RD ((unpairB s).1, (unpairB s).2)) := by
  have hz : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have hcs : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => csOf (unpairB s).1) :=
    cptl (cpt_unpairB1_1 hz) (fun _ => rfl)
  have hz2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).1).2) := cpt_unpairB2_1 hz
  have hmu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => muOf (unpairB s).1) :=
    cptl (cpt_unpairB2_1 hz2) (fun _ => rfl)
  have hy0 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => y0Of (unpairB s).1) :=
    cptl (cpt_pairB2 (cpt_unpairB1_1 hz) (cpt_pairB2 (cpt_unpairB1_1 hz2) (cpt_const [])))
      (fun _ => rfl)
  have hmt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (muOf (unpairB s).1).tail) := cpt_tail1 hmu
  have c1 := cpt_condC hy0 hmu
  have c2 := cpt_condC hy0 hmt
  have hw1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hw
  have hw2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hw
  have hzt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1 ++ [true]) := cpt_app2 hz (cpt_const [true])
  have hVa : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => pairB (csOf (unpairB s).1)
      (pairB ((unpairB s).1 ++ [true]) (unpairB (unpairB s).2).2)) :=
    cpt_pairB2 hcs (cpt_pairB2 hzt hw2)
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (pairB (csOf (unpairB s).1)
        (pairB ((unpairB s).1 ++ [true]) (unpairB (unpairB s).2).2),
        (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hVa hw1) (cpt_V cpt_sstep)
  have fv := cpt_bitFlag hV
  have hSF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => pairB (csOf (unpairB s).1)
      (pairB (y0Of (unpairB s).1) (lgU (muOf (unpairB s).1)))) :=
    cpt_pairB2 hcs (cpt_pairB2 hy0 (cpt_lgU hmu))
  have hSn : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => muOf (unpairB s).1 ++ (muOf (unpairB s).1 ++
      (muOf (unpairB s).1 ++ muOf (unpairB s).1))) :=
    cpt_app2 hmu (cpt_app2 hmu (cpt_app2 hmu hmu))
  have hS := cpt_srch hSF hSn
  have fS := cpt_sel hS (cpt_const [true]) (cpt_const [])
  have all := cpt_sel c1 fv (cpt_sel c2 fS (cpt_const []))
  exact cptl (cpt_comp all cpt_neL) (fun s => combL _ _ _ _)

theorem cpt_RD : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool RD :=
  cptl (cpt_comp cpt_pairB cpt_RDS) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Universal.CompileBool
section

namespace PEqualNP.Library.Universal

open Turing

section CompileBool

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

noncomputable def envOfBool : Env tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  nσ := @Fintype.card tm.σ tm.σFin
  nσ_pos := @Fintype.card_pos tm.σ tm.σFin ⟨tm.initialState⟩
  num v := (σEquiv tm v).val
  σof n := if h : n < @Fintype.card tm.σ tm.σFin then (σEquiv tm).symm ⟨n, h⟩ else tm.initialState
  σof_num v := by simp
  num_lt v := (σEquiv tm v).isLt
  nK := @Fintype.card tm.K tm.kFin
  numK k := (kEquiv tm k).val
  numK_lt k := (kEquiv tm k).isLt
  numK_inj := fun a b h => (kEquiv tm).injective (Fin.ext h)
  L := flatList tm
  start l := Classical.choose (flatList_placed tm l)
  placed_start l := Classical.choose_spec (flatList_placed tm l)
  k₀ := tm.k₀
  inSym n := eIn.symm (decide (n = 1))
  k₁ := tm.k₁
  outBit y := bitCode (eOut y)

theorem compileBool :
    ∃ (c : Code) (d : ℕ), ∀ (l : List Bool) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map (fun b => cond b 1 0)) (d * n + d) [bitCode b] := by
  let E := envOfBool tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, fun l b n hrun => ?_⟩

  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y)
      (l.map (fun b => cond b 1 0)) (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have hlt : (cond x 1 0 : ℕ) < 4 := by cases x <;> simp
    have := E.decode_in hlt
    cases x <;> simpa [E, envOfBool] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map (fun b => cond b 1 0))⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel

  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOfBool]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩

end CompileBool

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Machines.ExpPad
section

namespace PEqualNP.Library.Machines.ExpPad

open Turing

def expPad (x : List Bool) : List Bool := List.replicate (2 ^ x.length) true ++ false :: x

inductive PadK
  | I | S | A | B | O
  deriving DecidableEq

instance : Fintype PadK :=
  Fintype.ofList [.I, .S, .A, .B, .O] (fun x => by cases x <;> simp)

inductive PadL
  | start | outer | dbl | back | unsave | fin
  deriving DecidableEq

instance : Fintype PadL :=
  Fintype.ofList [.start, .outer, .dbl, .back, .unsave, .fin] (fun x => by cases x <;> simp)

abbrev PadΓ : PadK → Type
  | .I => Bool
  | .S => Bool
  | .A => Bool
  | .B => Bool
  | .O => Bool

def padProg : PadL → TM2.Stmt PadΓ PadL (Option Bool)
  | .start => .push .A (fun _ => true) (.goto fun _ => .outer)
  | .outer =>
    .pop .I (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .S (fun s => s.getD false) (.goto fun _ => .dbl))
        (.goto fun _ => .unsave))
  | .dbl =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.push .B (fun _ => true) (.goto fun _ => .dbl)))
        (.goto fun _ => .back))
  | .back =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .A (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .unsave =>
    .pop .S (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun s => s.getD false) (.goto fun _ => .unsave))
        (.push .O (fun _ => false) (.goto fun _ => .fin)))
  | .fin =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun _ => true) (.goto fun _ => .fin))
        .halt)

def padTM : FinTM2 where
  K := PadK
  k₀ := .I
  k₁ := .O
  Γ := PadΓ
  Λ := PadL
  main := .start
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := padProg

def pstk (i s a b o : List Bool) : ∀ k, List (PadΓ k)
  | .I => i
  | .S => s
  | .A => a
  | .B => b
  | .O => o

@[simp] theorem pstk_I (i s a b o : List Bool) : pstk i s a b o .I = i := rfl
@[simp] theorem pstk_S (i s a b o : List Bool) : pstk i s a b o .S = s := rfl
@[simp] theorem pstk_A (i s a b o : List Bool) : pstk i s a b o .A = a := rfl
@[simp] theorem pstk_B (i s a b o : List Bool) : pstk i s a b o .B = b := rfl
@[simp] theorem pstk_O (i s a b o : List Bool) : pstk i s a b o .O = o := rfl

@[simp] theorem pstk_set_I (i i' s a b o : List Bool) :
    Function.update (pstk i s a b o) .I i' = pstk i' s a b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_S (i s s' a b o : List Bool) :
    Function.update (pstk i s a b o) .S s' = pstk i s' a b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_A (i s a a' b o : List Bool) :
    Function.update (pstk i s a b o) .A a' = pstk i s a' b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_B (i s a b b' o : List Bool) :
    Function.update (pstk i s a b o) .B b' = pstk i s a b' o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_O (i s a b o o' : List Bool) :
    Function.update (pstk i s a b o) .O o' = pstk i s a b o' := by
  funext k; cases k <;> simp [pstk]

theorem pstk_start (i : List Bool) :
    pstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) .I i := by
  funext k; cases k <;> simp [pstk]

theorem pstk_end (o : List Bool) :
    pstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) .O o := by
  funext k; cases k <;> simp [pstk]

abbrev PadCfg : Type := TM2.Cfg PadΓ PadL (Option Bool)

abbrev padStep : Option PadCfg → Option PadCfg := flip bind (TM2.step padProg)

theorem start_step (st : Option Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .start, st, pstk i s a b o⟩) =
      some ⟨some .outer, st, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .outer, st, pstk (y :: i) s a b o⟩) =
      some ⟨some .dbl, some y, pstk i (y :: s) a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_nil (st : Option Bool) (s a b o : List Bool) :
    padStep (some ⟨some .outer, st, pstk [] s a b o⟩) =
      some ⟨some .unsave, none, pstk [] s a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .dbl, st, pstk i s (y :: a) b o⟩) =
      some ⟨some .dbl, some y, pstk i s a (true :: true :: b) o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some .dbl, st, pstk i s [] b o⟩) =
      some ⟨some .back, none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .back, st, pstk i s a (y :: b) o⟩) =
      some ⟨some .back, some y, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_nil (st : Option Bool) (i s a o : List Bool) :
    padStep (some ⟨some .back, st, pstk i s a [] o⟩) =
      some ⟨some .outer, none, pstk i s a [] o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .unsave, st, pstk i (y :: s) a b o⟩) =
      some ⟨some .unsave, some y, pstk i s a b (y :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_nil (st : Option Bool) (i a b o : List Bool) :
    padStep (some ⟨some .unsave, st, pstk i [] a b o⟩) =
      some ⟨some .fin, none, pstk i [] a b (false :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .fin, st, pstk i s (y :: a) b o⟩) =
      some ⟨some .fin, some y, pstk i s a b (true :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some .fin, st, pstk i s [] b o⟩) =
      some ⟨none, none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem dblLoop (i s o : List Bool) :
    ∀ (a b : ℕ) (st : Option Bool),
      padStep^[a + 1] (some ⟨some .dbl, st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some .back, none, pstk i s [] (rep (2 * a + b)) o⟩ := by
  intro a
  induction a with
  | zero => intro b st; simpa using dbl_nil st i s (rep b) o
  | succ a ih =>
    intro b st
    rw [Function.iterate_succ_apply, ← rep_succ a, dbl_cons, rep_succ, rep_succ, ih]
    rw [show 2 * a + (b + 1 + 1) = 2 * (a + 1) + b from by omega]

theorem backLoop (i s o : List Bool) :
    ∀ (b a : ℕ) (st : Option Bool),
      padStep^[b + 1] (some ⟨some .back, st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some .outer, none, pstk i s (rep (b + a)) [] o⟩ := by
  intro b
  induction b with
  | zero => intro a st; simpa using back_nil st i s (rep a) o
  | succ b ih =>
    intro a st
    rw [Function.iterate_succ_apply, ← rep_succ b, back_cons, rep_succ, ih]
    rw [show b + (a + 1) = b + 1 + a from by omega]

def outerSteps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | a, n + 1 => outerSteps (2 * a) n + ((2 * a + 1) + ((a + 1) + 1))

theorem outerSteps_eq : ∀ (n a : ℕ), outerSteps a n + 3 * a = 3 * a * 2 ^ n + 3 * n + 1 := by
  intro n
  induction n with
  | zero => intro a; simp [outerSteps]; omega
  | succ n ih =>
    intro a
    have h := ih (2 * a)
    have e : 3 * a * 2 ^ (n + 1) = 3 * (2 * a) * 2 ^ n := by ring
    rw [outerSteps, e]
    omega

theorem outerLoop :
    ∀ (x s : List Bool) (a : ℕ) (st : Option Bool),
      padStep^[outerSteps a x.length] (some ⟨some .outer, st, pstk x s (rep a) [] []⟩) =
        some ⟨some .unsave, none, pstk [] (x.reverse ++ s) (rep (a * 2 ^ x.length)) [] []⟩ := by
  intro x
  induction x with
  | nil => intro s a st; simpa [outerSteps] using outer_nil st s (rep a) [] []
  | cons y x ih =>
    intro s a st
    rw [List.length_cons, outerSteps,
      Function.iterate_add_apply padStep (outerSteps (2 * a) x.length),
      Function.iterate_add_apply padStep (2 * a + 1) ((a + 1) + 1),
      Function.iterate_succ_apply padStep (a + 1), outer_cons]
    have h1 : padStep^[a + 1]
        (some ⟨some .dbl, some y, pstk x (y :: s) (rep a) [] []⟩) =
        some ⟨some .back, none, pstk x (y :: s) [] (rep (2 * a)) []⟩ :=
      dblLoop x (y :: s) [] a 0 (some y)
    rw [h1]
    have h2 : padStep^[2 * a + 1]
        (some ⟨some .back, none, pstk x (y :: s) [] (rep (2 * a)) []⟩) =
        some ⟨some .outer, none, pstk x (y :: s) (rep (2 * a)) [] []⟩ :=
      backLoop x (y :: s) [] (2 * a) 0 none
    rw [h2, ih]
    rw [show 2 * a * 2 ^ x.length = a * 2 ^ (x.length + 1) from by ring]
    simp

theorem unsaveLoop (a : List Bool) :
    ∀ (s o : List Bool) (st : Option Bool),
      padStep^[s.length + 1] (some ⟨some .unsave, st, pstk [] s a [] o⟩) =
        some ⟨some .fin, none, pstk [] [] a [] (false :: (s.reverse ++ o))⟩ := by
  intro s
  induction s with
  | nil => intro o st; simpa using unsave_nil st [] a [] o
  | cons y s ih =>
    intro o st
    rw [List.length_cons, Function.iterate_succ_apply, unsave_cons, ih]
    simp

theorem finLoop :
    ∀ (a : ℕ) (o : List Bool) (st : Option Bool),
      padStep^[a + 1] (some ⟨some .fin, st, pstk [] [] (rep a) [] o⟩) =
        some ⟨none, none, pstk [] [] [] [] (rep a ++ o)⟩ := by
  intro a
  induction a with
  | zero => intro o st; simpa using fin_nil st [] [] [] o
  | succ a ih =>
    intro o st
    rw [Function.iterate_succ_apply, ← rep_succ a, fin_cons, ih]
    rw [show rep a ++ true :: o = true :: rep a ++ o from by
      simp [rep, ← List.replicate_succ, List.replicate_succ']]

def padSteps (n : ℕ) : ℕ := (2 ^ n + 1) + ((n + 1) + (outerSteps 1 n + 1))

theorem padSteps_eq (n : ℕ) : padSteps n = 4 * 2 ^ n + 4 * n + 1 := by
  have h := outerSteps_eq n 1
  unfold padSteps
  omega

theorem pad_run (x : List Bool) :
    (flip bind (TM2.step padProg))^[padSteps x.length] (some (initList padTM x)) =
      some (haltList padTM (expPad x)) := by
  refine (congrArg (fun c => (flip bind (TM2.step padProg))^[padSteps x.length]
    (some c)) (initList_eq padTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq padTM _)).symm)
  show padStep^[padSteps x.length]
    (some (⟨some .start, none, Function.update (fun _ => []) .I x⟩ : PadCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (expPad x)⟩ : PadCfg)
  rw [← pstk_start, ← pstk_end, padSteps, Function.iterate_add_apply padStep (2 ^ x.length + 1),
    Function.iterate_add_apply padStep (x.length + 1),
    Function.iterate_succ_apply padStep (outerSteps 1 x.length), start_step]
  have h1 : padStep^[outerSteps 1 x.length]
      (some ⟨some .outer, none, pstk x [] [true] [] []⟩) =
      some ⟨some .unsave, none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩ := by
    simpa using outerLoop x [] 1 none
  have h2 : padStep^[x.length + 1]
      (some ⟨some .unsave, none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩) =
      some ⟨some .fin, none, pstk [] [] (rep (2 ^ x.length)) [] (false :: x)⟩ := by
    simpa using unsaveLoop (rep (2 ^ x.length)) x.reverse [] none
  rw [h1, h2, finLoop]
  rfl

theorem expPad_time : PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x) expPad
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
  refine ⟨{
    tm := padTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := padSteps
    outputsFun := fun x =>
      { steps := padSteps x.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := pad_run x
          exact (congrArg (fun l => (flip bind (TM2.step padProg))^[padSteps x.length]
            (some (initList padTM l))) (hm _ x)).trans
            (this.trans (congrArg (fun l => some (haltList padTM l)) (hm Bool _).symm))
        steps_le_m := le_refl _ } }, fun n => ?_⟩
  show padSteps n ≤ 8 * 2 ^ n + 8 * n + 8
  rw [padSteps_eq]
  omega

end PEqualNP.Library.Machines.ExpPad
end

-- upstream PEqualNP.Library.Machines.ComposeTime
section

namespace PEqualNP.Library.Machines

open Turing

theorem comp_time {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ)
    (h₁ : PEqualNP.Library.ComputableInTime ea eb f t₁)
    (h₂ : PEqualNP.Library.ComputableInTime eb ec g t₂)
    (hmono : Monotone t₂)
    (hlen : ∀ a, (eb (f a)).length ≤ len (ea a).length) :
    PEqualNP.Library.ComputableInTime ea ec (fun a => g (f a))
      (fun n => t₁ n + (2 * len n + 2) + t₂ (len n)) := by
  classical
  obtain ⟨c1, hc1⟩ := h₁
  obtain ⟨c2, hc2⟩ := h₂
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : ℕ → ℕ := fun n => t₁ n + (2 * len n + 2) + t₂ (len n)
  have key : ∀ a, ∃ n, n ≤ T (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ t₁ (ea a).length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ t₂ (len (ea a).length) :=
      (r2.steps_le_m.trans (hc2 _)).trans (hmono (hlen a))
    have b3 := hlen a
    simp only [T, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }, fun _ => le_rfl⟩

theorem time_of_polyTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : PEqualNP.Library.ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, PEqualNP.Library.ComputableInTime ea eb f (fun n => p.eval n) := by
  obtain ⟨c⟩ := h
  exact ⟨c.time, ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet
    time := fun n => c.time.eval n
    outputsFun := c.outputsFun }, fun _ => le_rfl⟩⟩

theorem time_mono {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {t t' : ℕ → ℕ} (h : PEqualNP.Library.ComputableInTime ea eb f t) (ht : ∀ n, t n ≤ t' n) :
    PEqualNP.Library.ComputableInTime ea eb f t' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun n => (hc n).trans (ht n)⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Helpers.OutputLength
section

namespace PEqualNP.Library.Helpers
open Turing PEqualNP.Library PEqualNP.Library.Machines

theorem poly_le_monomial (p : Polynomial ℕ) : ∃ a d : ℕ, ∀ m : ℕ, 1 ≤ m → p.eval m ≤ a * m ^ d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, d, h⟩ := hp
    obtain ⟨b, e, h'⟩ := hq
    refine ⟨a + b, d + e, fun m hm => ?_⟩
    rw [Polynomial.eval_add, Nat.add_mul]
    have h1 : m ^ d ≤ m ^ (d + e) := Nat.pow_le_pow_right hm (by omega)
    have h2 : m ^ e ≤ m ^ (d + e) := Nat.pow_le_pow_right hm (by omega)
    exact add_le_add ((h m hm).trans (Nat.mul_le_mul_left _ h1))
      ((h' m hm).trans (Nat.mul_le_mul_left _ h2))
  | monomial d c => exact ⟨c, d, fun m _ => by rw [Polynomial.eval_monomial]⟩

theorem exists_pow_lt (A D N : ℕ) : ∃ n : ℕ, N ≤ n ∧ A * n ^ D < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt D (show (1 : ℝ) < 2 by norm_num)
  have hpos : (0 : ℝ) < 1 / (A + 1) := by positivity
  have ev := (h.eventually (gt_mem_nhds hpos)).and (Filter.eventually_ge_atTop N)
  obtain ⟨n, hn, hN⟩ := ev.exists
  refine ⟨n, hN, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hn
  have : ((A * n ^ D : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
    nlinarith
  exact_mod_cast this

theorem output_length_le (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ a d : ℕ, ∀ x : List Bool, 1 ≤ x.length → (f x).length ≤ a * x.length ^ d := by
  obtain ⟨c⟩ := hf
  obtain ⟨a, d, had⟩ := poly_le_monomial c.time
  refine ⟨1 + maxPush c.tm * a, d + 1, fun x hx => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  have hsteps : steps ≤ a * x.length ^ d := hle.trans (had _ hx)
  have h1 : x.length ≤ x.length ^ (d + 1) := by
    calc x.length = x.length ^ 1 := (pow_one _).symm
      _ ≤ x.length ^ (d + 1) := Nat.pow_le_pow_right hx (by omega)
  have h2 : x.length ^ d ≤ x.length ^ (d + 1) := Nat.pow_le_pow_right hx (by omega)
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length ^ (d + 1) + maxPush c.tm * (a * x.length ^ (d + 1)) :=
      (add_le_add h1 (Nat.mul_le_mul_left _ (hsteps.trans (Nat.mul_le_mul_left _ h2))))
    _ = (1 + maxPush c.tm * a) * x.length ^ (d + 1) := by ring

open PEqualNP.Search in
theorem code_length (n : ℕ) : (encodeCNF [[(2 ^ n, true)]]).length = 2 * n + 8 := by
  have hb : ∀ bs : List Bool, (bs.flatMap fun d => [true, d]).length = 2 * bs.length := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega
  have hs : (2 ^ n).bits.length = n + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  simp [encodeCNF, encodeClause, encodeLiteral, hb, hs]
  omega

open PEqualNP.Search in

theorem no_indexed_assignment : ¬ ∃ f : List Bool → List Bool,
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ φ : CNF, Satisfiable φ →
        CNF.eval (fun i : ℕ => (f (encodeCNF φ)).getD i false) φ = true := by
  rintro ⟨f, hf, h⟩
  obtain ⟨a, d, hlen⟩ := output_length_le f hf
  obtain ⟨n, hn8, hn⟩ := exists_pow_lt (a * 3 ^ d) d 8
  have hsat : Satisfiable [[(2 ^ n, true)]] :=
    ⟨fun _ => true, by simp [CNF.eval, Clause.eval, Literal.eval]⟩
  have hv := h _ hsat
  simp only [CNF.eval, Clause.eval, Literal.eval, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq] at hv
  have hlt : 2 ^ n < (f (encodeCNF [[(2 ^ n, true)]])).length := by
    by_contra hge
    rw [List.getD_eq_default _ _ (not_lt.mp hge)] at hv
    exact Bool.false_ne_true hv
  have hb := hlen (encodeCNF [[(2 ^ n, true)]]) (by rw [code_length]; omega)
  rw [code_length] at hb
  have h3 : (2 * n + 8) ^ d ≤ (3 * n) ^ d := Nat.pow_le_pow_left (by omega) d
  have : a * (2 * n + 8) ^ d ≤ a * 3 ^ d * n ^ d := by
    calc a * (2 * n + 8) ^ d ≤ a * (3 * n) ^ d := Nat.mul_le_mul_left _ h3
      _ = a * 3 ^ d * n ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]
  omega
end PEqualNP.Library.Helpers
end

-- upstream PEqualNP.Library.Universal.ExpHierarchy
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Machines.ExpPad

def expQ (s : List Bool) : List Bool :=
  pairB (unpairB (dropN s)).1 (pairB (dropN s) (hd s))

def expG (s : List Bool) : Bool := !V (expQ s, [])

theorem hd_expPad (z : List Bool) : hd (expPad z) = un (2 ^ z.length) :=
  hd_un (2 ^ z.length) z

theorem dropN_expPad (z : List Bool) : dropN (expPad z) = z :=
  dropN_un (2 ^ z.length) z

theorem expQ_expPad (z : List Bool) :
    expQ (expPad z) = pairB (unpairB z).1 (pairB z (un (2 ^ z.length))) := by
  simp only [expQ, hd_expPad, dropN_expPad]

theorem expPad_length (z : List Bool) : (expPad z).length = 2 ^ z.length + z.length + 1 := by
  simp only [expPad, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem cpt_expQ :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) expQ :=
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB (dropN s)).1) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).1) cpt_dropN cpt_unpairB1
  cpt_pairB2 h1 (cpt_pairB2 cpt_dropN cpt_hd)

theorem cpt_expG :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool expG := by
  have h1 : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (expQ s, [])) :=
    cpt_comp (cpt_pair cpt_expQ (cpt_const [])) (cpt_V cpt_sstep)
  have h2 : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime Computability.encodeBool Computability.encodeBool (fun b => !b)
      (fun b => some (!b)) (fun b => by cases b <;> rfl)
  exact cpt_comp (g := fun b : Bool => !b) h1 h2

theorem exp_linear_le (b : ℕ → ℕ) (c : ℕ) (hb : ∀ n, b n ≤ 2 ^ (c * (n + 1))) :
    ∃ k, ∀ n, b n ≤ 2 ^ (n ^ k) + k := by
  refine ⟨c + 2 + b 0 + b 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact le_trans (by omega : b 0 ≤ c + 2 + b 0 + b 1) (Nat.le_add_left _ _)
    · exact le_trans (by omega : b 1 ≤ c + 2 + b 0 + b 1) (Nat.le_add_left _ _)
  · have h1 : c ≤ n ^ c := by
      have h2 : c < 2 ^ c := Nat.lt_two_pow_self
      have h3 : 2 ^ c ≤ n ^ c := Nat.pow_le_pow_left h c
      omega
    have h4 : n + 1 ≤ n ^ 2 := by nlinarith
    have h5 : c * (n + 1) ≤ n ^ (c + 2) := by
      rw [pow_add]
      exact Nat.mul_le_mul h1 h4
    have h6 : n ^ (c + 2) ≤ n ^ (c + 2 + b 0 + b 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (c * (n + 1)) ≤ 2 ^ (n ^ (c + 2 + b 0 + b 1)) :=
      Nat.pow_le_pow_right (by norm_num) (h5.trans h6)
    have := hb n
    omega

theorem expTime_bound (p : Polynomial ℕ) :
    ∃ k, ∀ n : ℕ, 8 * 2 ^ n + 8 * n + 8 + (2 * (2 ^ n + n + 1) + 2) + p.eval (2 ^ n + n + 1) ≤
      2 ^ (n ^ k) + k := by
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add p
  refine exp_linear_le _ (j + 6) (fun n => ?_)
  have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hm : 2 ^ n + n + 1 ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
  have h1 : (2 ^ n + n + 1) ^ j ≤ 2 ^ ((n + 1) * j) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hm j
  have h2 : j ≤ 2 ^ ((n + 1) * j) := by
    have h3 : j < 2 ^ j := Nat.lt_two_pow_self
    have h4 : (2 : ℕ) ^ j ≤ 2 ^ ((n + 1) * j) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have h5 : (2 : ℕ) ^ ((n + 1) * j) * 2 ≤ 2 ^ ((n + 1) * (j + 5)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h6 : (2 : ℕ) ^ n * 32 ≤ 2 ^ ((n + 1) * (j + 5)) := by
    have : (2 : ℕ) ^ n * 32 = 2 ^ (n + 5) := by rw [pow_add]; norm_num
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h7 : (2 : ℕ) ^ ((n + 1) * (j + 5)) * 2 ≤ 2 ^ ((j + 6) * (n + 1)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h8 := hj (2 ^ n + n + 1)
  omega

theorem expG_time : ∃ k : ℕ, ComputableInTime (fun x : List Bool => x) Computability.encodeBool
    (fun z : List Bool => expG (expPad z)) (fun n : ℕ => 2 ^ (n ^ k) + k) := by
  obtain ⟨p, hp⟩ := time_of_polyTime cpt_expG
  obtain ⟨k, hk⟩ := expTime_bound p
  have h := comp_time (fun x : List Bool => x) (fun x : List Bool => x) Computability.encodeBool
    expPad expG (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) (fun n => p.eval n)
    (fun n => 2 ^ n + n + 1) expPad_time hp (fun _ _ hxy => eval_mono p hxy)
    (fun a => (expPad_length a).le)
  exact ⟨k, time_mono h hk⟩

theorem exp_clock (d : ℕ) (T : Polynomial ℕ) (N : ℕ) :
    ∃ m, N + 1 ≤ m ∧ d * T.eval m + d ≤ 2 ^ m := by
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add T
  obtain ⟨m, hm, hlt⟩ := PEqualNP.Library.Helpers.exists_pow_lt (d * (j + 2)) j (N + 1)
  refine ⟨m, hm, ?_⟩
  have hP : 1 ≤ m ^ j := Nat.one_le_pow _ _ (by omega)
  have h1 : d * T.eval m ≤ d * (m ^ j + j) := Nat.mul_le_mul_left d (hj m)
  have h2 : d * (j + 1) * 1 ≤ d * (j + 1) * m ^ j := Nat.mul_le_mul_left _ hP
  have e : d * (j + 2) * m ^ j = d * m ^ j + d * (j + 1) * m ^ j := by ring
  have e2 : d * (m ^ j + j) + d = d * m ^ j + d * (j + 1) * 1 := by ring
  omega

theorem expHierarchy : ∃ L : Language Bool,
    (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧
      L ∉ PEqualNP.Library.P := by
  let A : Language Bool := {z | expG (expPad z) = true}
  have hA : ∀ z, z ∈ A ↔ expG (expPad z) = true := fun _ => Iff.rfl
  refine ⟨A, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := expG_time
    exact ⟨k, fun z => expG (expPad z), fun _ => Iff.rfl, hk⟩
  rintro ⟨f, hf, ⟨cM⟩⟩
  have hf' : ∀ z, z ∈ A ↔ f z = true := hf
  obtain ⟨c, d, hc⟩ := compileBool cM.tm cM.inputAlphabet cM.outputAlphabet
  have hrun : ∀ z : List Bool, ∃ n, n ≤ cM.time.eval z.length ∧
      c.outputsWithin (z.map (fun b => cond b 1 0)) (d * n + d) [bitCode (f z)] := by
    intro z
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cM.time.eval z.length ∧
        (flip bind (Turing.TM2.step cM.tm.m))^[n]
          (some (Turing.initList cM.tm (z.map cM.inputAlphabet.invFun))) =
        some (Turing.haltList cM.tm [cM.outputAlphabet.invFun (f z)]) :=
      ⟨(cM.outputsFun z).steps, (cM.outputsFun z).steps_le_m, (cM.outputsFun z).evals_in_steps⟩
    exact ⟨n, hn, hc z (f z) n hev⟩
  obtain ⟨m, hm, hclock⟩ := exp_clock d cM.time (2 * (encCode c).length)
  let z : List Bool := pairB (encCode c) (un (m - (2 * (encCode c).length + 1)))
  have hzl : z.length = m := by
    simp only [z, pairB_length, un, List.length_replicate]
    omega
  have hq : expQ (expPad z) = pairB (encCode c) (pairB z (un (2 ^ m))) := by
    rw [expQ_expPad, hzl]
    simp only [z, unpairB_pairB]
  obtain ⟨n, hn, ho⟩ := hrun z
  have hle : d * n + d ≤ 2 ^ m := by
    rw [hzl] at hn
    have h2 : d * n ≤ d * cM.time.eval m := Nat.mul_le_mul_left d hn
    omega
  have ho' := Code.outputsWithin_mono c _ hle _ ho
  have hV : V (expQ (expPad z), []) = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) (2 ^ m) [1] := by
    rw [hq, V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  have hiff : V (expQ (expPad z), []) = true ↔ f z = true := by
    rw [hV]
    constructor
    · intro h1
      have heq : [1] = [bitCode (f z)] := h1.2.symm.trans ho'.2
      cases hb : f z with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    · intro hb
      rw [hb] at ho'
      exact ho'
  have hneg : z ∈ A ↔ V (expQ (expPad z), []) = false := by
    rw [hA]
    simp only [expG, Bool.not_eq_true']
  have hcontra : V (expQ (expPad z), []) = true ↔ V (expQ (expPad z), []) = false :=
    hiff.trans ((hf' z).symm.trans hneg)
  cases hv : V (expQ (expPad z), []) with
  | true => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.1 rfl)
  | false => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.2 rfl)

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.Machines.ReduceNP
section

namespace PEqualNP.Library.Machines
open Turing PEqualNP.Library

theorem output_length_poly (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  obtain ⟨c⟩ := hf
  refine ⟨Polynomial.X + Polynomial.C (maxPush c.tm) * c.time, fun x => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length + maxPush c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Universal.BruteForce
section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Machines.ExpPad


theorem bf_cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem bf_cpt_succB : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) succB :=
  fst_polyTime _ _ _ succD succFin true (fun _ => rfl)

theorem bf_succD_length (q : Bool) (s : List Bool) :
    (fstRun succD succFin q s).length ≤ s.length + 1 := by
  induction s generalizing q with
  | nil => cases q <;> simp [fstRun, succFin]
  | cons b l ih =>
    have h1 := ih b
    have h2 := ih false
    cases q <;> simp [fstRun, succD] <;> omega

theorem bf_succB_length (s : List Bool) : (succB s).length ≤ s.length + 1 :=
  bf_succD_length true s

theorem bf_bflag_length (b : Bool) : (bflag b).length ≤ 1 := by
  cases b <;> simp [bflag]

theorem bf_srchStep_length (s : List Bool) : (srchStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := bf_succB_length (unpairB (unpairB s).2).1
  have h4 := bf_bflag_length (V ((unpairB s).1, (unpairB (unpairB s).2).1))
  unfold srchStep
  rw [pairB_length, pairB_length, List.length_append]
  omega

theorem bf_cpt_srchStep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) srchStep := by
  have hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have hc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hF hc) (cpt_V cpt_sstep)
  have hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))) :=
    bf_cptl (cpt_bitFlag hV) (fun _ => rfl)
  have hs : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => succB (unpairB (unpairB s).2).1) := cpt_comp hc bf_cpt_succB
  exact bf_cptl (cpt_pairB2 hF (cpt_pairB2 hs (cpt_app2 hfl hb))) (fun _ => rfl)

theorem bf_cpt_srch {F n : List Bool → List Bool} (hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) F) (hn : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => srch (F s) (n s)) :=
  bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow bf_cpt_srchStep 5 bf_srchStep_length hn
    (cpt_pairB2 hF (cpt_pairB2 (cpt_const []) (cpt_const [])))))) (fun _ => rfl)

theorem bf_neL_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

theorem bf_cpt_neL :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, bf_neL_true, Computability.encodeBool])

def bfG (s : List Bool) : Bool := !(srch (dropN s) (hd s)).isEmpty

theorem cpt_bfG :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool bfG :=
  bf_cptl (cpt_comp (bf_cpt_srch cpt_dropN cpt_hd) bf_cpt_neL) (fun _ => rfl)

theorem bfG_expPad (F : List Bool) (hlen : ∀ w, V (F, w) = true → w.length + 1 ≤ F.length) :
    bfG (expPad F) = true ↔ ∃ w, V (F, w) = true := by
  have e : bfG (expPad F) = true ↔ ¬ srch F (un (2 ^ F.length)) = [] := by
    simp [bfG, hd_expPad, dropN_expPad]
  rw [e, srch_eq_nil, un_length]
  constructor
  · intro h
    by_contra hc
    exact h (fun j _ => by
      cases hv : V (F, cand j) with
      | false => rfl
      | true => exact absurd ⟨cand j, hv⟩ hc)
  · rintro ⟨w, hw⟩ h
    have h1 := idx_bound w
    have h2 : (2 : ℕ) ^ (w.length + 1) ≤ 2 ^ F.length :=
      Nat.pow_le_pow_right (by norm_num) (hlen w hw)
    have h3 := h (idx w) (by omega)
    rw [cand_idx, hw] at h3
    exact Bool.noConfusion h3

theorem bf_cpt_query (a : List Bool) (q : Polynomial ℕ) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun x : List Bool => pairB a (pairB x (un (q.eval x.length)))) :=
  cpt_pairB2 (cpt_const a) (cpt_pairB2 cpt_id (L055 q))

theorem exp_pow_le (b : ℕ → ℕ) (M : ℕ) (hb : ∀ n, 2 ≤ n → b n ≤ 2 ^ (n ^ M)) :
    ∃ k, ∀ n, b n ≤ 2 ^ (n ^ k) + k := by
  refine ⟨M + b 0 + b 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact le_trans (by omega : b 0 ≤ M + b 0 + b 1) (Nat.le_add_left _ _)
    · exact le_trans (by omega : b 1 ≤ M + b 0 + b 1) (Nat.le_add_left _ _)
  · have h6 : n ^ M ≤ n ^ (M + b 0 + b 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (n ^ M) ≤ 2 ^ (n ^ (M + b 0 + b 1)) :=
      Nat.pow_le_pow_right (by norm_num) h6
    have := hb n h
    omega

theorem bf_time_bound (p₁ r p₂ : Polynomial ℕ) :
    ∃ k, ∀ n : ℕ, p₁.eval n + (2 * r.eval n + 2) +
        (8 * 2 ^ r.eval n + 8 * r.eval n + 8) +
        (2 * (2 ^ r.eval n + r.eval n + 1) + 2) + p₂.eval (2 ^ r.eval n + r.eval n + 1) ≤
      2 ^ (n ^ k) + k := by
  obtain ⟨k, hk⟩ := expTime_bound p₂
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add r
  obtain ⟨i, hi⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add
    (p₁ + Polynomial.C 2 * r + Polynomial.C (2 + k))
  refine exp_pow_le _ (i + 1 + (j + 1) * k + 1) (fun n hn => ?_)
  have hk' := hk (r.eval n)
  have hi' := hi n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hi'
  have hpos : ∀ e : ℕ, e < n ^ e := fun e =>
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hn e)

  have a1 : n ^ i + i ≤ n ^ (i + 1) := by
    have := hpos i
    rw [pow_succ]
    nlinarith
  have a2 : n ^ (i + 1) ≤ 2 ^ (n ^ (i + 1)) := Nat.lt_two_pow_self.le

  have b1 : r.eval n ≤ n ^ (j + 1) := by
    have := hpos j
    have := hj n
    rw [pow_succ]
    nlinarith
  have b2 : r.eval n ^ k ≤ n ^ ((j + 1) * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left b1 k
  have hM1 : n ^ (i + 1) ≤ n ^ (i + 1 + (j + 1) * k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hM2 : n ^ ((j + 1) * k) ≤ n ^ (i + 1 + (j + 1) * k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have c1 : (2 : ℕ) ^ (n ^ (i + 1)) ≤ 2 ^ (n ^ (i + 1 + (j + 1) * k)) :=
    Nat.pow_le_pow_right (by norm_num) hM1
  have c2 : (2 : ℕ) ^ (r.eval n ^ k) ≤ 2 ^ (n ^ (i + 1 + (j + 1) * k)) :=
    Nat.pow_le_pow_right (by norm_num) (b2.trans hM2)
  have c3 : (2 : ℕ) ^ (n ^ (i + 1 + (j + 1) * k)) * 2 ≤
      2 ^ (n ^ (i + 1 + (j + 1) * k + 1)) := by
    rw [← pow_succ]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 1 ≤ n ^ (i + 1 + (j + 1) * k) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith
  omega

theorem np_subset_exp (L : Language Bool) (hL : L ∈ NP) :
    ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k) := by
  obtain ⟨c, q, hcomp, hsound⟩ := np_code L hL
  let F : List Bool → List Bool :=
    fun x => pairB (encCode c) (pairB x (un (q.eval x.length)))
  have hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) F := bf_cpt_query (encCode c) q
  have hFlen : ∀ x w, V (F x, w) = true → w.length + 1 ≤ (F x).length := by
    intro x w hw
    have h1 := V_length _ _ _ _ hw
    simp only [F, pairB_length]
    omega
  have hcorr : ∀ x, x ∈ L ↔ bfG (expPad (F x)) = true := by
    intro x
    refine Iff.trans ?_ (bfG_expPad (F x) (hFlen x)).symm
    exact ⟨fun hx => hcomp x _ le_rfl hx, fun ⟨w, hw⟩ => hsound x _ w hw⟩
  obtain ⟨p₁, hp₁⟩ := time_of_polyTime hF
  obtain ⟨r, hr⟩ := output_length_poly F hF
  obtain ⟨p₂, hp₂⟩ := time_of_polyTime cpt_bfG
  have hmono : Monotone (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
    intro a b hab
    have : (2 : ℕ) ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    show 8 * 2 ^ a + 8 * a + 8 ≤ 8 * 2 ^ b + 8 * b + 8
    omega
  have h1 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) F expPad (fun n => p₁.eval n)
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) (fun n => r.eval n) hp₁ expPad_time hmono hr
  have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (fun x => expPad (F x)) bfG _ (fun n => p₂.eval n)
    (fun n => 2 ^ r.eval n + r.eval n + 1) h1 hp₂ (fun _ _ hxy => eval_mono p₂ hxy)
    (fun x => by
      have e := expPad_length (F x)
      have h3 := hr x
      have : (2 : ℕ) ^ (F x).length ≤ 2 ^ r.eval x.length :=
        Nat.pow_le_pow_right (by norm_num) h3
      show (expPad (F x)).length ≤ 2 ^ r.eval x.length + r.eval x.length + 1
      omega)
  obtain ⟨k, hk⟩ := bf_time_bound p₁ r p₂
  exact ⟨k, fun x => bfG (expPad (F x)), hcorr, time_mono h2 hk⟩

end PEqualNP.Library.Universal
end

-- upstream PEqualNP.Library.L014
section

theorem PEqualNP.Library.L014 : ∀ L ∈ PEqualNP.Library.NP, ∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k) :=
  fun L hL => PEqualNP.Library.Universal.np_subset_exp L hL
end

-- the bridge from the upstream definitions to the campaign's
section bridge
theorem P_iff (L : Language Bool) : L ∈ PvsNP.P ↔ L ∈ PEqualNP.Library.P := by
  constructor
  · rintro ⟨f, hf, hL⟩
    exact ⟨f, hL, hf⟩
  · rintro ⟨f, hL, hf⟩
    exact ⟨f, hf, hL⟩

theorem karp_iff (L₁ L₂ : Language Bool) :
    PvsNP.KarpReducible L₁ L₂ ↔ PEqualNP.Library.PolyTimeReducible L₁ L₂ := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h⟩

theorem NP_iff (L : Language Bool) : L ∈ PvsNP.NP ↔ L ∈ PEqualNP.Library.NP := by
  constructor
  · rintro ⟨V, p, hV, hL⟩
    exact ⟨{xw | V xw = true}, p, ⟨V, fun _ => Iff.rfl, hV⟩, hL⟩
  · rintro ⟨R, p, ⟨f, hf, hc⟩, hL⟩
    refine ⟨f, p, hc, fun x => (hL x).trans ?_⟩
    exact exists_congr fun w => and_congr_right fun _ => hf (x, w)

theorem NPHard_iff (L : Language Bool) : PvsNP.NPHard L ↔ PEqualNP.Library.NPHard L := by
  constructor
  · intro h L' hL'
    exact (karp_iff L' L).1 (h L' ((NP_iff L').2 hL'))
  · intro h L' hL'
    exact (karp_iff L' L).2 (h L' ((NP_iff L').1 hL'))

theorem NPComplete_iff (L : Language Bool) :
    PvsNP.NPComplete L ↔ PEqualNP.Library.NPComplete L :=
  and_congr (NP_iff L) (NPHard_iff L)

theorem coNP_iff (L : Language Bool) : L ∈ PvsNP.coNP ↔ L ∈ PEqualNP.Library.coNP :=
  NP_iff Lᶜ

theorem P_eq : PvsNP.P = PEqualNP.Library.P := Set.ext P_iff

theorem NP_eq : PvsNP.NP = PEqualNP.Library.NP := Set.ext NP_iff

theorem coNP_eq : PvsNP.coNP = PEqualNP.Library.coNP := Set.ext coNP_iff
end bridge

end PvsNP.Units.fr_np_in_exp

/-- Every NP language is decided in exponential time: upstream L014 (brute force over certificates), with 2 ^ (n ^ k) + k ≤ 2 ^ (n ^ k + k). -/
theorem PvsNP.Units.fr_np_in_exp :
  ∀ L ∈ PvsNP.NP, ∃ f : List Bool → Bool, (∀ x, x ∈ L ↔ f x = true) ∧
    ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (k : ℕ),
      ∀ n, h.time n ≤ 2 ^ (n ^ k + k) := by
  intro L hL
  obtain ⟨k, f, hf, c, hc⟩ := PvsNP.Units.fr_np_in_exp.PEqualNP.Library.L014 L ((PvsNP.Units.fr_np_in_exp.NP_iff L).1 hL)
  refine ⟨f, hf, c, k, fun n => (hc n).trans ?_⟩
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ (n ^ k) := Nat.one_le_two_pow
  rw [pow_add]
  nlinarith
