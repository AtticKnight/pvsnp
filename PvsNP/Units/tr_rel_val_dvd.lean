import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_reverse_polytime

set_option autoImplicit false

namespace PvsNP.Units.tr_rel_val_dvd

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

lemma encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

lemma encodeString_eq :
    PvsNP.encodeString = (fun x : List Bool => x) := by
  funext x
  rfl

def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

lemma val_nil : val [] = 0 := rfl

lemma val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

lemma val_append_singleton (l : List Bool) (b : Bool) :
    val (l ++ [b]) = val l + 2 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [val_nil, val_cons]
  | cons a rest ih =>
    simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ]
    ring

def subBit (x y bor : Bool) : Bool :=
  (x != y) != bor

def subBor (x y bor : Bool) : Bool :=
  (!x && (y || bor)) || (y && bor)

lemma sub_step_arith (x y bor : Bool) :
    x.toNat + 2 * (subBor x y bor).toNat = (subBit x y bor).toNat + y.toNat + bor.toNat := by
  cases x <;> cases y <;> cases bor <;> decide

def subRaw : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, [], bor => subBit a false bor :: subRaw as [] (subBor a false bor)
  | a :: as, b :: bs, bor => subBit a b bor :: subRaw as bs (subBor a b bor)

lemma subRaw_length (a b : List Bool) (bor : Bool) :
    (subRaw a b bor).length = a.length := by
  induction a generalizing b bor with
  | nil => rfl
  | cons x as ih =>
    cases b with
    | nil => simp [subRaw, ih]
    | cons y bs => simp [subRaw, ih]

lemma val_subRaw (a b : List Bool) (bor : Bool) (hle : val b + bor.toNat ≤ val a) :
    val (subRaw a b bor) + val b + bor.toNat = val a := by
  induction a generalizing b bor with
  | nil =>
    simp [val_nil] at hle
    have hbor : bor = false := by cases bor <;> simp_all
    simp [subRaw, val_nil, hle.1, hbor]
  | cons x as ih =>
    cases b with
    | nil =>
      have har := sub_step_arith x false bor
      have hbit : (subBit x false bor).toNat ≤ 1 := by cases subBit x false bor <;> decide
      rw [val_cons] at hle
      have hle' : val [] + (subBor x false bor).toNat ≤ val as := by
        simp only [val_nil, Nat.zero_add] at hle ⊢
        simp only [Bool.toNat_false, Nat.add_zero] at har
        omega
      have hrec := ih [] (subBor x false bor) hle'
      simp only [subRaw, val_cons, val_nil, Nat.add_zero] at hrec ⊢
      simp only [Bool.toNat_false, Nat.add_zero] at har
      omega
    | cons y bs =>
      have har := sub_step_arith x y bor
      have hbit : (subBit x y bor).toNat ≤ 1 := by cases subBit x y bor <;> decide
      rw [val_cons, val_cons] at hle
      have hle' : val bs + (subBor x y bor).toNat ≤ val as := by omega
      have hrec := ih bs (subBor x y bor) hle'
      simp only [subRaw, val_cons]
      omega

inductive SK
  | I | R1 | R2 | S1 | S2 | O
  deriving DecidableEq

instance : Fintype SK :=
  Fintype.ofList [SK.I, SK.R1, SK.R2, SK.S1, SK.S2, SK.O] (fun x => by cases x <;> simp)

inductive SL
  | split | rev1 | rev2 | work | clear2 | emit
  deriving DecidableEq

instance : Fintype SL :=
  Fintype.ofList [SL.split, SL.rev1, SL.rev2, SL.work, SL.clear2, SL.emit]
    (fun x => by cases x <;> simp)

abbrev SΓ : SK → Type
  | .I => Bool ⊕ Bool
  | _ => Bool

abbrev Sσ : Type := Option (Bool ⊕ Bool) × Option Bool × Option Bool × Bool

def mkStk (i : List (Bool ⊕ Bool)) (r1 r2 s1 s2 o : List Bool) : ∀ k : SK, List (SΓ k)
  | .I => i
  | .R1 => r1
  | .R2 => r2
  | .S1 => s1
  | .S2 => s2
  | .O => o

lemma update_mkStk_I (i i' : List (Bool ⊕ Bool)) (r1 r2 s1 s2 o : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .I i' = mkStk i' r1 r2 s1 s2 o := by
  funext k; cases k <;> rfl

lemma update_mkStk_R1 (i : List (Bool ⊕ Bool)) (r1 r1' r2 s1 s2 o : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .R1 r1' = mkStk i r1' r2 s1 s2 o := by
  funext k; cases k <;> rfl

lemma update_mkStk_R2 (i : List (Bool ⊕ Bool)) (r1 r2 r2' s1 s2 o : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .R2 r2' = mkStk i r1 r2' s1 s2 o := by
  funext k; cases k <;> rfl

lemma update_mkStk_S1 (i : List (Bool ⊕ Bool)) (r1 r2 s1 s1' s2 o : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .S1 s1' = mkStk i r1 r2 s1' s2 o := by
  funext k; cases k <;> rfl

lemma update_mkStk_S2 (i : List (Bool ⊕ Bool)) (r1 r2 s1 s2 s2' o : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .S2 s2' = mkStk i r1 r2 s1 s2' o := by
  funext k; cases k <;> rfl

lemma update_mkStk_O (i : List (Bool ⊕ Bool)) (r1 r2 s1 s2 o o' : List Bool) :
    Function.update (mkStk i r1 r2 s1 s2 o) .O o' = mkStk i r1 r2 s1 s2 o' := by
  funext k; cases k <;> rfl

def subProg : SL → TM2.Stmt SΓ SL Sσ
  | .split =>
    .pop .I (fun _ o => (o, none, none, false)) <|
      .branch (fun s => s.1.isSome)
        (.branch (fun s => match s.1 with | some (Sum.inl _) => true | _ => false)
          (.push .R1 (fun s => match s.1 with | some (Sum.inl b) => b | _ => false) <|
           .load (fun _ => (none, none, none, false)) <| .goto (fun _ => .split))
          (.push .R2 (fun s => match s.1 with | some (Sum.inr b) => b | _ => false) <|
           .load (fun _ => (none, none, none, false)) <| .goto (fun _ => .split)))
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .rev1))
  | .rev1 =>
    .pop .R1 (fun _ o => (none, o, none, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push .S1 (fun s => s.2.1.getD false) <|
         .load (fun _ => (none, none, none, false)) <| .goto (fun _ => .rev1))
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .rev2))
  | .rev2 =>
    .pop .R2 (fun _ o => (none, o, none, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push .S2 (fun s => s.2.1.getD false) <|
         .load (fun _ => (none, none, none, false)) <| .goto (fun _ => .rev2))
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .work))
  | .work =>
    .pop .S1 (fun s o => (none, o, none, s.2.2.2)) <|
      .branch (fun s => s.2.1.isSome)
        (.pop .S2 (fun s o => (none, s.2.1, o, s.2.2.2)) <|
         .push .R1 (fun s => subBit (s.2.1.getD false) (s.2.2.1.getD false) s.2.2.2) <|
         .load (fun s => (none, none, none,
           subBor (s.2.1.getD false) (s.2.2.1.getD false) s.2.2.2)) <|
         .goto (fun _ => .work))
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .clear2))
  | .clear2 =>
    .pop .S2 (fun _ o => (none, o, none, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .clear2))
        (.load (fun _ => (none, none, none, false)) <| .goto (fun _ => .emit))
  | .emit =>
    .pop .R1 (fun _ o => (none, o, none, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push .O (fun s => s.2.1.getD false) <|
         .load (fun _ => (none, none, none, false)) <| .goto (fun _ => .emit))
        (.load (fun _ => (none, none, none, false)) <| .halt)

def subTM : FinTM2 where
  K := SK
  k₀ := .I
  k₁ := .O
  Γ := SΓ
  Λ := SL
  main := .split
  σ := Sσ
  initialState := (none, none, none, false)
  m := subProg

abbrev SCfg := TM2.Cfg SΓ SL Sσ
abbrev sstep : Option SCfg → Option SCfg := flip bind (TM2.step subProg)

lemma initList_sub (l : List (Bool ⊕ Bool)) :
    initList subTM l = (⟨some .split, (none, none, none, false), mkStk l [] [] [] [] []⟩ : SCfg) := by
  simp only [initList, subTM]
  congr 1
  funext k; cases k <;> rfl

lemma haltList_sub (l : List Bool) :
    haltList subTM l = (⟨none, (none, none, none, false), mkStk [] [] [] [] [] l⟩ : SCfg) := by
  simp only [haltList, subTM]
  congr 1
  funext k; cases k <;> rfl

lemma iter_trans {a b : ℕ} {x y z : Option SCfg}
    (h1 : sstep^[a] x = y) (h2 : sstep^[b] y = z) :
    sstep^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

lemma run_split_left (x : List Bool) (rest : List (Bool ⊕ Bool)) (r1 r2 : List Bool) :
    sstep^[x.length]
      (some ⟨some .split, (none, none, none, false), mkStk (x.map Sum.inl ++ rest) r1 r2 [] [] []⟩) =
      some ⟨some .split, (none, none, none, false), mkStk rest (x.reverse ++ r1) r2 [] [] []⟩ := by
  induction x generalizing r1 with
  | nil => rfl
  | cons a xs ih =>
    have hs : sstep
        (some ⟨some .split, (none, none, none, false),
          mkStk (Sum.inl a :: (xs.map Sum.inl ++ rest)) r1 r2 [] [] []⟩) =
        some ⟨some .split, (none, none, none, false),
          mkStk (xs.map Sum.inl ++ rest) (a :: r1) r2 [] [] []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_I, update_mkStk_R1]
    have hstep := iter_trans (a := 1) (by simpa using hs) (ih (a :: r1))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc, Nat.add_comm] using hstep

lemma run_split_right (y r1 r2 : List Bool) :
    sstep^[y.length + 1]
      (some ⟨some .split, (none, none, none, false), mkStk (y.map Sum.inr) r1 r2 [] [] []⟩) =
      some ⟨some .rev1, (none, none, none, false), mkStk [] r1 (y.reverse ++ r2) [] [] []⟩ := by
  induction y generalizing r2 with
  | nil =>
    simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_I]
  | cons b ys ih =>
    have hs : sstep
        (some ⟨some .split, (none, none, none, false),
          mkStk (Sum.inr b :: ys.map Sum.inr) r1 r2 [] [] []⟩) =
        some ⟨some .split, (none, none, none, false),
          mkStk (ys.map Sum.inr) r1 (b :: r2) [] [] []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_I, update_mkStk_R2]
    have hstep := iter_trans (a := 1) (by simpa using hs) (ih (b :: r2))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_rev1 (r1 r2 s1 : List Bool) :
    sstep^[r1.length + 1]
      (some ⟨some .rev1, (none, none, none, false), mkStk [] r1 r2 s1 [] []⟩) =
      some ⟨some .rev2, (none, none, none, false), mkStk [] [] r2 (r1.reverse ++ s1) [] []⟩ := by
  induction r1 generalizing s1 with
  | nil =>
    simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R1]
  | cons a rest ih =>
    have hs : sstep (some ⟨some .rev1, (none, none, none, false), mkStk [] (a :: rest) r2 s1 [] []⟩) =
        some ⟨some .rev1, (none, none, none, false), mkStk [] rest r2 (a :: s1) [] []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R1, update_mkStk_S1]
    have hstep := iter_trans (a := 1) (by simpa using hs) (ih (a :: s1))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_rev2 (r2 s1 s2 : List Bool) :
    sstep^[r2.length + 1]
      (some ⟨some .rev2, (none, none, none, false), mkStk [] [] r2 s1 s2 []⟩) =
      some ⟨some .work, (none, none, none, false), mkStk [] [] [] s1 (r2.reverse ++ s2) []⟩ := by
  induction r2 generalizing s2 with
  | nil =>
    simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R2]
  | cons b rest ih =>
    have hs : sstep (some ⟨some .rev2, (none, none, none, false), mkStk [] [] (b :: rest) s1 s2 []⟩) =
        some ⟨some .rev2, (none, none, none, false), mkStk [] [] rest s1 (b :: s2) []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R2, update_mkStk_S2]
    have hstep := iter_trans (a := 1) (by simpa using hs) (ih (b :: s2))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_clear2 (r1 s2 : List Bool) :
    sstep^[s2.length + 1]
      (some ⟨some .clear2, (none, none, none, false), mkStk [] r1 [] [] s2 []⟩) =
      some ⟨some .emit, (none, none, none, false), mkStk [] r1 [] [] [] []⟩ := by
  induction s2 with
  | nil =>
    simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_S2]
  | cons b rest ih =>
    have hs : sstep (some ⟨some .clear2, (none, none, none, false), mkStk [] r1 [] [] (b :: rest) []⟩) =
        some ⟨some .clear2, (none, none, none, false), mkStk [] r1 [] [] rest []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_S2]
    have hstep := iter_trans (a := 1) (by simpa using hs) ih
    simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_emit (r1 o : List Bool) :
    sstep^[r1.length + 1]
      (some ⟨some .emit, (none, none, none, false), mkStk [] r1 [] [] [] o⟩) =
      some ⟨none, (none, none, none, false), mkStk [] [] [] [] [] (r1.reverse ++ o)⟩ := by
  induction r1 generalizing o with
  | nil =>
    simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R1]
  | cons c rest ih =>
    have hs : sstep (some ⟨some .emit, (none, none, none, false), mkStk [] (c :: rest) [] [] [] o⟩) =
        some ⟨some .emit, (none, none, none, false), mkStk [] rest [] [] [] (c :: o)⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_R1, update_mkStk_O]
    have hstep := iter_trans (a := 1) (by simpa using hs) (ih (c :: o))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_work (s1 : List Bool) :
    ∀ (s2 acc : List Bool) (bor : Bool),
      ∃ t, t ≤ s1.length + s2.length + 2 ∧
        sstep^[t] (some ⟨some .work, (none, none, none, bor), mkStk [] acc [] s1 s2 []⟩) =
          some ⟨some .emit, (none, none, none, false),
            mkStk [] ((subRaw s1 s2 bor).reverse ++ acc) [] [] [] []⟩ := by
  induction s1 with
  | nil =>
    intro s2 acc bor
    have hs : sstep (some ⟨some .work, (none, none, none, bor), mkStk [] acc [] [] s2 []⟩) =
        some ⟨some .clear2, (none, none, none, false), mkStk [] acc [] [] s2 []⟩ := by
      simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk, update_mkStk_S1]
    refine ⟨1 + (s2.length + 1), by simp; omega, ?_⟩
    simpa [subRaw] using iter_trans (a := 1) (by simpa using hs) (run_clear2 acc s2)
  | cons a s1' ih =>
    intro s2 acc bor
    cases s2 with
    | nil =>
      have hs : sstep
          (some ⟨some .work, (none, none, none, bor), mkStk [] acc [] (a :: s1') [] []⟩) =
          some ⟨some .work, (none, none, none, subBor a false bor),
            mkStk [] (subBit a false bor :: acc) [] s1' [] []⟩ := by
        simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk,
          update_mkStk_S1, update_mkStk_S2, update_mkStk_R1]
      obtain ⟨t', ht', hrec⟩ := ih [] (subBit a false bor :: acc) (subBor a false bor)
      refine ⟨1 + t', by simp at ht' ⊢; omega, ?_⟩
      have hstep := iter_trans (a := 1) (by simpa using hs) hrec
      simpa [subRaw, List.reverse_cons, List.append_assoc] using hstep
    | cons b s2' =>
      have hs : sstep
          (some ⟨some .work, (none, none, none, bor), mkStk [] acc [] (a :: s1') (b :: s2') []⟩) =
          some ⟨some .work, (none, none, none, subBor a b bor),
            mkStk [] (subBit a b bor :: acc) [] s1' s2' []⟩ := by
        simp [sstep, flip, TM2.step, subProg, TM2.stepAux, mkStk,
          update_mkStk_S1, update_mkStk_S2, update_mkStk_R1]
      obtain ⟨t', ht', hrec⟩ := ih s2' (subBit a b bor :: acc) (subBor a b bor)
      refine ⟨1 + t', by simp; omega, ?_⟩
      have hstep := iter_trans (a := 1) (by simpa using hs) hrec
      simpa [subRaw, List.reverse_cons, List.append_assoc] using hstep

lemma run_sub (p : List Bool × List Bool) :
    ∃ t, t ≤ 4 * (p.1.length + p.2.length) + 8 ∧
      sstep^[t] (some ⟨some .split, (none, none, none, false),
        mkStk (PvsNP.encodePair p) [] [] [] [] []⟩) =
        some ⟨none, (none, none, none, false), mkStk [] [] [] [] [] (subRaw p.1 p.2 false)⟩ := by
  rcases p with ⟨x, y⟩
  have henc : PvsNP.encodePair (x, y) = x.map Sum.inl ++ y.map Sum.inr := rfl
  rw [henc]
  have h1 := run_split_left x (y.map Sum.inr) [] []
  have h2 := run_split_right y (x.reverse ++ []) []
  have h3 := run_rev1 (x.reverse ++ []) (y.reverse ++ []) []
  have h4 := run_rev2 (y.reverse ++ []) ((x.reverse ++ []).reverse ++ []) []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2 h3 h4
  obtain ⟨tw, htw, h5⟩ := run_work x y [] false
  simp only [List.append_nil] at h5
  have h6 := run_emit (subRaw x y false).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, subRaw_length] at h6
  have hall := iter_trans (iter_trans (iter_trans (iter_trans (iter_trans h1 h2) h3) h4) h5) h6
  refine ⟨x.length + (y.length + 1) + (x.length + 1) + (y.length + 1) + tw + (x.length + 1), ?_, hall⟩
  dsimp only
  omega

lemma cpt_subRaw :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => subRaw p.1 p.2 false) :=
  ⟨{
    tm := subTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 8
    outputsFun := fun p =>
      let h := run_sub p
      { steps := Classical.choose h
        evals_in_steps := by
          have hm : ∀ l : List (Bool ⊕ Bool), @List.map (Bool ⊕ Bool) (subTM.Γ subTM.k₀)
              (Equiv.refl (Bool ⊕ Bool)).invFun l = l := fun l => List.map_id l
          have hm1 : ∀ l : List Bool, @List.map Bool (subTM.Γ subTM.k₁)
              (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
          have hinit : initList subTM (@List.map (Bool ⊕ Bool) (subTM.Γ subTM.k₀)
              (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair p)) =
              (⟨some .split, (none, none, none, false),
                mkStk (PvsNP.encodePair p) [] [] [] [] []⟩ : SCfg) :=
            (congrArg (initList subTM) (hm _)).trans (initList_sub _)
          have hhalt : haltList subTM (@List.map Bool (subTM.Γ subTM.k₁)
              (Equiv.refl Bool).invFun (subRaw p.1 p.2 false)) =
              (⟨none, (none, none, none, false),
                mkStk [] [] [] [] [] (subRaw p.1 p.2 false)⟩ : SCfg) :=
            (congrArg (haltList subTM) (hm1 _)).trans (haltList_sub _)
          exact (congrArg (fun c => sstep^[Classical.choose h] (some c)) hinit).trans
            ((Classical.choose_spec h).2.trans (congrArg some hhalt.symm))
        steps_le_m := by
          have hs := (Classical.choose_spec h).1
          have hlen : (PvsNP.encodePair p).length = p.1.length + p.2.length := by
            rcases p with ⟨x, y⟩
            change (x.map Sum.inl ++ y.map Sum.inr).length = x.length + y.length
            simp
          rw [hlen]
          simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X] using hs } }⟩

lemma nonempty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => !x.isEmpty) := by
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p Bool (fun _ _ => true) false id
  have hfold_true : ∀ y : List Bool, y.foldl (fun _ _ => true) true = true := by
    intro y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => !x.isEmpty := by
    funext x
    have hx := hdec x
    change id (x.foldl (fun _ _ => true) false) = true ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, id, List.isEmpty_nil, Bool.not_true] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, hfold_true, id, List.isEmpty_cons, Bool.not_false] at hx ⊢
      exact hx.1 trivial
  rwa [← heq]

lemma headD_false_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => x.headD false := by
    funext x
    have hx := hdec x
    change ((x.foldl δ none == some true) = true) ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, List.headD_nil] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, δ, hfold_some, List.headD_cons] at hx ⊢
      cases b with
      | false => cases hcx : c (false :: y) <;> simp_all
      | true => exact hx.1 (by decide)
  rwa [← heq]

def allFalse (x : List Bool) : Bool := x.all (fun b => !b)

lemma allFalse_iff_val_eq_zero (x : List Bool) :
    allFalse x = true ↔ val x = 0 := by
  induction x with
  | nil => simp [allFalse, val_nil]
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [allFalse, List.all_cons, Bool.not_false, Bool.true_and, val_cons,
        Bool.toNat_false, Nat.zero_add]
      rw [← allFalse, ih]
      omega
    | true =>
      simp [allFalse, val_cons]

lemma allFalse_reverse (x : List Bool) :
    allFalse x.reverse = allFalse x := by
  simp [allFalse]

lemma allFalse_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer allFalse := by
  let δ : Bool → Bool → Bool := fun q b => q && !b
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p Bool δ true id
  have hfold_false : ∀ y : List Bool, y.foldl δ false = false := by
    intro y; induction y with | nil => rfl | cons _ _ ih => simpa [δ] using ih
  have hfold_eq : ∀ y : List Bool, y.foldl δ true = allFalse y := by
    intro y
    induction y with
    | nil => rfl
    | cons b rest ih =>
      cases b with
      | false => simpa [δ, allFalse] using ih
      | true => simp [δ, allFalse, hfold_false]
  have heq : c = allFalse := by
    funext x
    have hx := hdec x
    change id (x.foldl δ true) = true ↔ c x = true at hx
    rw [hfold_eq] at hx
    cases ha : allFalse x <;> cases hcx : c x <;> simp_all
  rwa [← heq]

def sD (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def sY (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def sR (s : List Bool) : List Bool := (unpairB s).2

def rShift (s : List Bool) : List Bool :=
  if (sY s).headD false = true then [true] ++ sR s else [false] ++ sR s

def divStep (s : List Bool) : List Bool :=
  if !(sY s).isEmpty = true then
    pairB (pairB (sD s) (sY s).tail)
      (if decide (val (sD s) ≤ val (rShift s)) = true then
        subRaw (rShift s) (sD s) false
      else
        rShift s)
  else
    s

lemma rShift_length (s : List Bool) : (rShift s).length = (sR s).length + 1 := by
  unfold rShift
  split_ifs <;> simp

lemma divStep_len (s : List Bool) : (divStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have hy : (sY s).tail.length ≤ (sY s).length := by simp
  have hbound : 4 * (sD s).length + 2 * (sY s).length + (sR s).length ≤ s.length := by
    unfold sD sY sR; omega
  unfold divStep
  split_ifs
  · simp only [pairB_length, subRaw_length, rShift_length]; omega
  · simp only [pairB_length, rShift_length]; omega
  · omega

lemma divStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString divStep := by
  have hD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sD :=
    cpt_unpairB1_1 cpt_unpairB1
  have hY : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sY :=
    cpt_unpairB2_1 cpt_unpairB1
  have hR : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sR :=
    cpt_unpairB2
  have hYne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sY (fun x => !x.isEmpty) hY nonempty_poly
  have hYhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sY (fun x => x.headD false) hY headD_false_poly
  have hrShift : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rShift :=
    PvsNP.Units.m2_ite_polytime _ _ _ hYhd
      (cpt_app2 (cpt_const [true]) hR)
      (cpt_app2 (cpt_const [false]) hR)
  have hpairDR : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => (sD s, rShift s)) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair hD hrShift
  have hcanSub : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (sD s) ≤ val (rShift s))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun s => (sD s, rShift s))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairDR PvsNP.Units.m2_binary_le_polytime
  have hpairRD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => (rShift s, sD s)) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair hrShift hD
  have hrSub : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => subRaw (rShift s) (sD s) false) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (rShift s, sD s))
      (fun p : List Bool × List Bool => subRaw p.1 p.2 false)
      hpairRD cpt_subRaw
  have hrNext := PvsNP.Units.m2_ite_polytime _ _ _ hcanSub hrSub hrShift
  have hstepBody := cpt_pairB2 (cpt_pairB2 hD (cpt_tail1 hY)) hrNext
  exact PvsNP.Units.m2_ite_polytime _ _ _ hYne hstepBody cpt_id

lemma divStep_cons (d : List Bool) (hd : 0 < val d) (b : Bool) (u r : List Bool)
    (hr : val r < val d) :
    ∃ r' : List Bool,
      divStep (pairB (pairB d (b :: u)) r) = pairB (pairB d u) r' ∧
      val r' = (2 * val r + b.toNat) % val d ∧
      val r' < val d := by
  have hrs : rShift (pairB (pairB d (b :: u)) r) = b :: r := by
    unfold rShift sY sR
    cases b <;> simp [unpairB_pairB]
  have hv_br : val (b :: r) = 2 * val r + b.toNat := by
    rw [val_cons]; omega
  by_cases hle : val d ≤ val (b :: r)
  · refine ⟨subRaw (b :: r) d false, ?_, ?_, ?_⟩
    · unfold divStep
      simp [sD, sY, unpairB_pairB, hrs, hle]
    · have hsub := val_subRaw (b :: r) d false (by simpa using hle)
      simp only [Bool.toNat_false, Nat.add_zero] at hsub
      have hlt2 : val (b :: r) - val d < val d := by
        have hb : b.toNat ≤ 1 := by cases b <;> decide
        omega
      have hmod : (2 * val r + b.toNat) % val d = val (b :: r) - val d := by
        rw [← hv_br, Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt2]
      omega
    · have hsub := val_subRaw (b :: r) d false (by simpa using hle)
      simp only [Bool.toNat_false, Nat.add_zero] at hsub
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      omega
  · refine ⟨b :: r, ?_, ?_, ?_⟩
    · unfold divStep
      simp [sD, sY, unpairB_pairB, hrs, hle]
    · rw [← hv_br, Nat.mod_eq_of_lt (by omega)]
    · omega

lemma divStep_iter (d : List Bool) (hd : 0 < val d) (u v : List Bool) :
    ∀ r : List Bool, val r < val d →
      ∃ r' : List Bool,
        divStep^[u.length] (pairB (pairB d (u ++ v)) r) = pairB (pairB d v) r' ∧
        val r' = (val r * 2 ^ u.length + val u.reverse) % val d ∧
        val r' < val d := by
  induction u with
  | nil =>
    intro r hr
    refine ⟨r, rfl, ?_, hr⟩
    simp [val_nil, Nat.mod_eq_of_lt hr]
  | cons b u' ih =>
    intro r hr
    rw [List.length_cons, Function.iterate_succ_apply]
    obtain ⟨r1, hstep, hval1, hlt1⟩ := divStep_cons d hd b (u' ++ v) r hr
    simp only [List.cons_append]
    rw [hstep]
    obtain ⟨r', hiter, hval', hlt'⟩ := ih r1 hlt1
    refine ⟨r', hiter, ?_, hlt'⟩
    rw [hval', hval1]
    have hrev : val (b :: u').reverse = val u'.reverse + 2 ^ u'.length * b.toNat := by
      rw [List.reverse_cons, val_append_singleton, List.length_reverse]
    rw [hrev]
    have hmod :
        ((2 * val r + b.toNat) % val d * 2 ^ u'.length + val u'.reverse) % val d =
        ((2 * val r + b.toNat) * 2 ^ u'.length + val u'.reverse) % val d := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    rw [hmod]
    congr 1
    simp only [pow_succ]
    ring

def remOf (s : List Bool) : List Bool :=
  (unpairB (divStep^[(unpairB s).2.length] (pairB s []))).2

def outOf (s : List Bool) : List Bool :=
  if allFalse (unpairB s).1 = true then (unpairB s).2 else remOf s

def dvdDecider (p : List Bool × List Bool) : Bool :=
  allFalse (outOf (pairB p.1 p.2.reverse))

theorem main_proof :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∣
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) ↔ f p = true := by
  obtain ⟨cd⟩ := divStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => divStep^[p.2.length] p.1) :=
    Iter.iter_polyTime divStep cd 5 divStep_len
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => pairB s []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hrem : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString remOf :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit cpt_unpairB2) hiter)
  have hzeroD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool => allFalse (unpairB s).1) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => (unpairB s).1) allFalse cpt_unpairB1 allFalse_poly
  have hout : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString outOf :=
    PvsNP.Units.m2_ite_polytime _ _ _ hzeroD cpt_unpairB2 hrem
  have hdecS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool => allFalse (outOf s)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
      outOf allFalse hout allFalse_poly
  have hrevSnd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2.reverse)) := by
    rw [← encodePair_eq]
    exact cpt_second PvsNP.Units.m2_reverse_polytime
  have hpbRev : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2.reverse) := by
    have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => pairB p.1 p.2) := by
      rw [← encodePair_eq]
      exact cpt_pairB
    exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1, p.2.reverse))
      (fun p : List Bool × List Bool => pairB p.1 p.2) hrevSnd hpb
  have hf : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer dvdDecider :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => pairB p.1 p.2.reverse)
      (fun s : List Bool => allFalse (outOf s)) hpbRev hdecS
  refine ⟨dvdDecider, hf, ?_⟩
  rintro ⟨d, y⟩
  change (val d ∣ val y) ↔ dvdDecider (d, y) = true
  by_cases hd0 : val d = 0
  · have hafd : allFalse d = true := (allFalse_iff_val_eq_zero d).mpr hd0
    have hout_eq : outOf (pairB d y.reverse) = y.reverse := by
      simp [outOf, unpairB_pairB, hafd]
    rw [hd0, Nat.zero_dvd]
    simp only [dvdDecider, hout_eq, allFalse_reverse, allFalse_iff_val_eq_zero]
  · have hdpos : 0 < val d := Nat.pos_of_ne_zero hd0
    have hafd : allFalse d = false :=
      Bool.eq_false_iff.mpr fun h => hd0 ((allFalse_iff_val_eq_zero d).mp h)
    have hout_eq : outOf (pairB d y.reverse) = remOf (pairB d y.reverse) := by
      simp [outOf, unpairB_pairB, hafd]
    obtain ⟨r', hrun, hvalr', _⟩ := divStep_iter d hdpos y.reverse [] [] (by simpa [val_nil])
    simp only [List.append_nil, List.reverse_reverse, val_nil, Nat.zero_mul, Nat.zero_add] at hrun hvalr'
    have hrem_eq : remOf (pairB d y.reverse) = r' := by
      simp only [remOf, unpairB_pairB, hrun]
    rw [dvdDecider, hout_eq, hrem_eq, allFalse_iff_val_eq_zero, hvalr', Nat.dvd_iff_mod_eq_zero]

end PvsNP.Units.tr_rel_val_dvd

theorem PvsNP.Units.tr_rel_val_dvd :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) ↔
          f p = true :=
  PvsNP.Units.tr_rel_val_dvd.main_proof
