import Mathlib
import PvsNP.Defs
import CookLevin

/-
A single-tape machine simulated by a four-stack machine of Mathlib's TM2 model.

The stacks: the input stack, the output stack, the tape to the left of the head (nearest cell on
top) and the tape from the head rightwards (the head cell on top). The machine first moves the
input onto the right stack (through the left stack, to keep its order), then performs one step of
the single-tape machine per step of its own, and once that machine halts it empties the left
stack, moves the output letters at the head onto the left stack, empties the right stack and moves
the letters to the output stack.

The lemmas initList_eq, haltList_eq and iterate_none follow the ones of the same names in
PvsNP/Units/m2_polytime_comp.lean of this repository (Apache License 2.0), which was adapted from
github.com/brilliant-hq/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9.
-/

namespace PvsNP.Units.m1_st_to_tm2

open Turing

/-- The labels of the multi-stack machine. -/
inductive Lbl
  | ld1 | ld2 | sim | clrL | mvOut | clrR | fin
  deriving DecidableEq

instance : Fintype Lbl where
  elems := {Lbl.ld1, Lbl.ld2, Lbl.sim, Lbl.clrL, Lbl.mvOut, Lbl.clrR, Lbl.fin}
  complete := by intro x; cases x <;> decide

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem headI_eq {Γ : Type} [Inhabited Γ] (l : List Γ) : l.headI = l.head?.getD default := by
  cases l <;> rfl

section machine

variable {A B : Type} (M : PvsNP.SingleTape.Machine A B)

/-- The stack names: input, output, left of the head, from the head rightwards. -/
abbrev SK : Type := Bool ⊕ Bool

/-- The stack alphabets. -/
abbrev SΓ : SK → Type
  | Sum.inl false => A
  | Sum.inl true => B
  | Sum.inr _ => M.Γ

/-- The internal state: the state of the single-tape machine and a register. -/
abbrev Sσ : Type := M.Λ × Option M.Γ

abbrev SStmt : Type := TM2.Stmt (SΓ M) Lbl (Sσ M)

abbrev SCfg : Type := TM2.Cfg (SΓ M) Lbl (Sσ M)

/-- The four stacks. -/
def stk (i : List A) (o : List B) (l r : List M.Γ) : ∀ k : SK, List (SΓ M k)
  | Sum.inl false => i
  | Sum.inl true => o
  | Sum.inr false => l
  | Sum.inr true => r

theorem stk_i (i : List A) (o : List B) (l r : List M.Γ) : stk M i o l r (Sum.inl false) = i := rfl

theorem stk_o (i : List A) (o : List B) (l r : List M.Γ) : stk M i o l r (Sum.inl true) = o := rfl

theorem stk_l (i : List A) (o : List B) (l r : List M.Γ) : stk M i o l r (Sum.inr false) = l := rfl

theorem stk_r (i : List A) (o : List B) (l r : List M.Γ) : stk M i o l r (Sum.inr true) = r := rfl

theorem stk_set_i (i i' : List A) (o : List B) (l r : List M.Γ) :
    Function.update (stk M i o l r) (Sum.inl false) i' = stk M i' o l r := by
  funext k
  rcases k with (_ | _) | (_ | _) <;> simp [Function.update, stk]

theorem stk_set_o (i : List A) (o o' : List B) (l r : List M.Γ) :
    Function.update (stk M i o l r) (Sum.inl true) o' = stk M i o' l r := by
  funext k
  rcases k with (_ | _) | (_ | _) <;> simp [Function.update, stk]

theorem stk_set_l (i : List A) (o : List B) (l l' r : List M.Γ) :
    Function.update (stk M i o l r) (Sum.inr false) l' = stk M i o l' r := by
  funext k
  rcases k with (_ | _) | (_ | _) <;> simp [Function.update, stk]

theorem stk_set_r (i : List A) (o : List B) (l r r' : List M.Γ) :
    Function.update (stk M i o l r) (Sum.inr true) r' = stk M i o l r' := by
  funext k
  rcases k with (_ | _) | (_ | _) <;> simp [Function.update, stk]

/-- Whether the register holds an output letter. -/
noncomputable def isOut (x : Option M.Γ) : Bool :=
  @decide (∃ b : B, x = some (M.out b)) (Classical.propDecidable _)

/-- The output letter the register holds. -/
noncomputable def dec (b₀ : B) (x : Option M.Γ) : B :=
  @dite B (∃ b : B, x = some (M.out b)) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => b₀)

theorem isOut_iff (x : Option M.Γ) : isOut M x = true ↔ ∃ b : B, x = some (M.out b) := by
  unfold isOut
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem isOut_out (b : B) : isOut M (some (M.out b)) = true :=
  (isOut_iff M _).mpr ⟨b, rfl⟩

theorem dec_out (b₀ b : B) : dec M b₀ (some (M.out b)) = b := by
  have h : ∃ b' : B, some (M.out b) = some (M.out b') := ⟨b, rfl⟩
  unfold dec
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (M.out_injective (Option.some.inj (Classical.choose_spec h))).symm

/-- What the single-tape machine does in the state and on the symbol the internal state holds. -/
def act (s : Sσ M) : Option (M.Λ × TM0.Stmt M.Γ) := M.δ s.1 (s.2.getD default)

def halts (s : Sσ M) : Bool := (act M s).isNone

def isWrite (s : Sσ M) : Bool :=
  match act M s with
  | some (_, TM0.Stmt.write _) => true
  | _ => false

def isLeft (s : Sσ M) : Bool :=
  match act M s with
  | some (_, TM0.Stmt.move Dir.left) => true
  | _ => false

def nextq (s : Sσ M) : M.Λ :=
  match act M s with
  | some (q, _) => q
  | none => s.1

def wsym (s : Sσ M) : M.Γ :=
  match act M s with
  | some (_, TM0.Stmt.write b) => b
  | _ => default

/-- Read a popped symbol into the register. -/
def rd (s : Sσ M) (x : Option M.Γ) : Sσ M := (s.1, x)

/-- The symbol in the register, the blank when it is empty. -/
def top (s : Sσ M) : M.Γ := s.2.getD default

def regSome (s : Sσ M) : Bool := s.2.isSome

/-- The program. -/
noncomputable def prog (d : Option B) : Lbl → SStmt M
  | Lbl.ld1 =>
    TM2.Stmt.pop (Sum.inl false) (fun s (x : Option A) => (s.1, x.map M.inp))
      (TM2.Stmt.branch (regSome M)
        (TM2.Stmt.push (Sum.inr false) (top M) (TM2.Stmt.goto fun _ => Lbl.ld1))
        (TM2.Stmt.goto fun _ => Lbl.ld2))
  | Lbl.ld2 =>
    TM2.Stmt.pop (Sum.inr false) (rd M)
      (TM2.Stmt.branch (regSome M)
        (TM2.Stmt.push (Sum.inr true) (top M) (TM2.Stmt.goto fun _ => Lbl.ld2))
        (TM2.Stmt.goto fun _ => Lbl.sim))
  | Lbl.sim =>
    TM2.Stmt.peek (Sum.inr true) (rd M)
      (TM2.Stmt.branch (halts M) (TM2.Stmt.goto fun _ => Lbl.clrL)
        (TM2.Stmt.branch (isWrite M)
          (TM2.Stmt.pop (Sum.inr true) (fun s _ => s)
            (TM2.Stmt.push (Sum.inr true) (wsym M)
              (TM2.Stmt.load (fun s => (nextq M s, none)) (TM2.Stmt.goto fun _ => Lbl.sim))))
          (TM2.Stmt.branch (isLeft M)
            (TM2.Stmt.pop (Sum.inr false) (fun s x => (nextq M s, x))
              (TM2.Stmt.push (Sum.inr true) (top M)
                (TM2.Stmt.load (fun s => (s.1, none)) (TM2.Stmt.goto fun _ => Lbl.sim))))
            (TM2.Stmt.pop (Sum.inr true) (fun s _ => s)
              (TM2.Stmt.push (Sum.inr false) (top M)
                (TM2.Stmt.load (fun s => (nextq M s, none))
                  (TM2.Stmt.goto fun _ => Lbl.sim)))))))
  | Lbl.clrL =>
    TM2.Stmt.pop (Sum.inr false) (rd M)
      (TM2.Stmt.branch (regSome M) (TM2.Stmt.goto fun _ => Lbl.clrL)
        (TM2.Stmt.goto fun _ => Lbl.mvOut))
  | Lbl.mvOut =>
    TM2.Stmt.pop (Sum.inr true) (rd M)
      (TM2.Stmt.branch (fun s => isOut M s.2)
        (TM2.Stmt.push (Sum.inr false) (top M) (TM2.Stmt.goto fun _ => Lbl.mvOut))
        (TM2.Stmt.goto fun _ => Lbl.clrR))
  | Lbl.clrR =>
    TM2.Stmt.pop (Sum.inr true) (rd M)
      (TM2.Stmt.branch (regSome M) (TM2.Stmt.goto fun _ => Lbl.clrR)
        (TM2.Stmt.goto fun _ => Lbl.fin))
  | Lbl.fin =>
    TM2.Stmt.pop (Sum.inr false) (rd M)
      (TM2.Stmt.branch (regSome M)
        (match d with
          | some b₀ =>
            TM2.Stmt.push (Sum.inl true) (fun s => dec M b₀ s.2) (TM2.Stmt.goto fun _ => Lbl.fin)
          | none => TM2.Stmt.goto fun _ => Lbl.fin)
        (TM2.Stmt.load (fun _ => (default, none)) TM2.Stmt.halt))

/-- The multi-stack machine. -/
noncomputable def tm2 (d : Option B) : FinTM2 where
  K := SK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl false
  k₁ := Sum.inl true
  Γ := SΓ M
  Λ := Lbl
  main := Lbl.ld1
  ΛFin := inferInstance
  σ := Sσ M
  initialState := (default, none)
  σFin := by
    letI i1 : Fintype M.Λ := M.fintypeΛ
    letI i2 : Fintype M.Γ := M.fintypeΓ
    exact inferInstance
  Γk₀Fin := @Fintype.ofInjective A M.Γ M.fintypeΓ M.inp M.inp_injective
  m := prog M d

/-- `n` steps of the machine lead from `c` to `c'`. -/
def Reach (d : Option B) (n : ℕ) (c c' : SCfg M) : Prop :=
  (flip bind (TM2.step (prog M d)))^[n] (some c) = some c'

variable {M}

theorem Reach.one {d : Option B} {c c' : SCfg M} (h : TM2.step (prog M d) c = some c') :
    Reach M d 1 c c' := h

theorem Reach.trans {d : Option B} {n m : ℕ} {a b c : SCfg M} (h₁ : Reach M d n a b)
    (h₂ : Reach M d m b c) : Reach M d (n + m) a c := by
  unfold Reach at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem Reach.step {d : Option B} {m : ℕ} {a b c : SCfg M}
    (h₁ : TM2.step (prog M d) a = some b) (h₂ : Reach M d m b c) : Reach M d (m + 1) a c := by
  rw [Nat.add_comm]
  exact (Reach.one h₁).trans h₂

variable (M)

/-! ### Loading the input -/

theorem ld1_cons (d : Option B) (q : M.Λ) (reg : Option M.Γ) (a : A) (i : List A) (o : List B)
    (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.ld1, (q, reg), stk M (a :: i) o l r⟩ : SCfg M) =
      some ⟨some Lbl.ld1, (q, some (M.inp a)), stk M i o (M.inp a :: l) r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_i, stk_l, stk_set_i, stk_set_l, regSome, top]

theorem ld1_nil (d : Option B) (q : M.Λ) (reg : Option M.Γ) (o : List B) (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.ld1, (q, reg), stk M [] o l r⟩ : SCfg M) =
      some ⟨some Lbl.ld2, (q, none), stk M [] o l r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_i, stk_l, stk_set_i, stk_set_l, regSome, top]

theorem ld2_cons (d : Option B) (q : M.Λ) (reg : Option M.Γ) (i : List A) (o : List B) (x : M.Γ)
    (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.ld2, (q, reg), stk M i o (x :: l) r⟩ : SCfg M) =
      some ⟨some Lbl.ld2, (q, some x), stk M i o l (x :: r)⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_r, stk_l, stk_set_r, stk_set_l, regSome, top, rd]

theorem ld2_nil (d : Option B) (q : M.Λ) (reg : Option M.Γ) (i : List A) (o : List B)
    (r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.ld2, (q, reg), stk M i o [] r⟩ : SCfg M) =
      some ⟨some Lbl.sim, (q, none), stk M i o [] r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_r, stk_l, stk_set_r, stk_set_l, regSome, top, rd]

theorem load1 (d : Option B) (q : M.Λ) (o : List B) (r : List M.Γ) :
    ∀ (i : List A) (l : List M.Γ) (reg : Option M.Γ),
      Reach M d (i.length + 1) ⟨some Lbl.ld1, (q, reg), stk M i o l r⟩
        ⟨some Lbl.ld2, (q, none), stk M [] o ((i.map M.inp).reverse ++ l) r⟩ := by
  intro i
  induction i with
  | nil => intro l reg; exact Reach.one (ld1_nil M d q reg o l r)
  | cons a i ih =>
    intro l reg
    have h := Reach.step (ld1_cons M d q reg a i o l r) (ih (M.inp a :: l) (some (M.inp a)))
    simpa using h

theorem load2 (d : Option B) (q : M.Λ) (i : List A) (o : List B) :
    ∀ (l r : List M.Γ) (reg : Option M.Γ),
      Reach M d (l.length + 1) ⟨some Lbl.ld2, (q, reg), stk M i o l r⟩
        ⟨some Lbl.sim, (q, none), stk M i o [] (l.reverse ++ r)⟩ := by
  intro l
  induction l with
  | nil => intro r reg; exact Reach.one (ld2_nil M d q reg i o r)
  | cons x l ih =>
    intro r reg
    have h := Reach.step (ld2_cons M d q reg i o x l r) (ih (x :: r) (some x))
    simpa using h

/-! ### Simulating the single-tape machine -/

/-- The tape the two tape stacks stand for. -/
def tapeOf (l r : List M.Γ) : Tape M.Γ := Tape.mk' (ListBlank.mk l) (ListBlank.mk r)

theorem tapeOf_head (l r : List M.Γ) : (tapeOf M l r).head = r.head?.getD default := by
  unfold tapeOf
  rw [Tape.mk'_head, ListBlank.head_mk, headI_eq]

theorem tm0_step_eq (q : M.Λ) (l r : List M.Γ) (p : Option (M.Λ × TM0.Stmt M.Γ))
    (hδ : M.δ q (r.head?.getD default) = p) :
    TM0.step M.δ ⟨q, tapeOf M l r⟩ =
      p.map fun x => ⟨x.1, match x.2 with
        | TM0.Stmt.move dir => (tapeOf M l r).move dir
        | TM0.Stmt.write a => (tapeOf M l r).write a⟩ := by
  subst hδ
  rw [← tapeOf_head M l r]
  show Option.map _ (M.δ q (tapeOf M l r).head) = _
  congr 1
  funext x
  obtain ⟨q', a⟩ := x
  cases a <;> rfl

theorem sim_step (d : Option B) (q : M.Λ) (l r : List M.Γ) (c' : TM0.Cfg M.Γ M.Λ)
    (h : TM0.step M.δ ⟨q, tapeOf M l r⟩ = some c') :
    ∃ l' r', TM2.step (prog M d) (⟨some Lbl.sim, (q, none), stk M [] [] l r⟩ : SCfg M) =
        some ⟨some Lbl.sim, (c'.q, none), stk M [] [] l' r'⟩ ∧
      c'.Tape = tapeOf M l' r' ∧ l'.length + r'.length ≤ l.length + r.length + 1 := by
  cases hδ : M.δ q (r.head?.getD default) with
  | none =>
    rw [tm0_step_eq M q l r none hδ] at h
    exact absurd h (by simp)
  | some p =>
    obtain ⟨q', a⟩ := p
    rw [tm0_step_eq M q l r _ hδ] at h
    cases a with
    | write b =>
      have e : (⟨q', (tapeOf M l r).write b⟩ : TM0.Cfg M.Γ M.Λ) = c' := Option.some.inj h
      subst e
      refine ⟨l, b :: r.tail, ?_, ?_, ?_⟩
      · simp [TM2.step, prog, TM2.stepAux, stk_r, stk_l, stk_set_r, stk_set_l, rd, halts,
          isWrite, isLeft, nextq, wsym, act, top, hδ]
      · show (tapeOf M l r).write b = tapeOf M l (b :: r.tail)
        unfold tapeOf
        rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]
      · simp only [List.length_cons, List.length_tail]; omega
    | move dir =>
      cases dir with
      | left =>
        have e : (⟨q', (tapeOf M l r).move Dir.left⟩ : TM0.Cfg M.Γ M.Λ) = c' :=
          Option.some.inj h
        subst e
        refine ⟨l.tail, l.head?.getD default :: r, ?_, ?_, ?_⟩
        · simp [TM2.step, prog, TM2.stepAux, stk_r, stk_l, stk_set_r, stk_set_l, rd, halts,
            isWrite, isLeft, nextq, wsym, act, top, hδ]
        · show (tapeOf M l r).move Dir.left = tapeOf M l.tail (l.head?.getD default :: r)
          unfold tapeOf
          rw [Tape.move_left_mk', ListBlank.tail_mk, ListBlank.head_mk, ListBlank.cons_mk,
            headI_eq]
        · simp only [List.length_cons, List.length_tail]; omega
      | right =>
        have e : (⟨q', (tapeOf M l r).move Dir.right⟩ : TM0.Cfg M.Γ M.Λ) = c' :=
          Option.some.inj h
        subst e
        refine ⟨r.head?.getD default :: l, r.tail, ?_, ?_, ?_⟩
        · simp [TM2.step, prog, TM2.stepAux, stk_r, stk_l, stk_set_r, stk_set_l, rd, halts,
            isWrite, isLeft, nextq, wsym, act, top, hδ]
        · show (tapeOf M l r).move Dir.right = tapeOf M (r.head?.getD default :: l) r.tail
          unfold tapeOf
          rw [Tape.move_right_mk', ListBlank.tail_mk, ListBlank.head_mk, ListBlank.cons_mk,
            headI_eq]
        · simp only [List.length_cons, List.length_tail]; omega

theorem sim_halt (d : Option B) (q : M.Λ) (l r : List M.Γ)
    (h : TM0.step M.δ ⟨q, tapeOf M l r⟩ = none) :
    TM2.step (prog M d) (⟨some Lbl.sim, (q, none), stk M [] [] l r⟩ : SCfg M) =
      some ⟨some Lbl.clrL, (q, r.head?), stk M [] [] l r⟩ := by
  cases hδ : M.δ q (r.head?.getD default) with
  | none =>
    simp [TM2.step, prog, TM2.stepAux, stk_r, rd, halts, act, hδ]
  | some p =>
    rw [tm0_step_eq M q l r _ hδ] at h
    exact absurd h (by simp)

theorem sim_run (d : Option B) : ∀ (n : ℕ) (q : M.Λ) (l r : List M.Γ) (c' : TM0.Cfg M.Γ M.Λ),
    (flip bind (TM0.step M.δ))^[n] (some ⟨q, tapeOf M l r⟩) = some c' →
    ∃ l' r', Reach M d n ⟨some Lbl.sim, (q, none), stk M [] [] l r⟩
        ⟨some Lbl.sim, (c'.q, none), stk M [] [] l' r'⟩ ∧
      c'.Tape = tapeOf M l' r' ∧ l'.length + r'.length ≤ l.length + r.length + n := by
  intro n
  induction n with
  | zero =>
    intro q l r c' h
    have h' : (⟨q, tapeOf M l r⟩ : TM0.Cfg M.Γ M.Λ) = c' := Option.some.inj h
    subst h'
    exact ⟨l, r, rfl, rfl, le_rfl⟩
  | succ n ih =>
    intro q l r c' h
    rw [Function.iterate_succ_apply] at h
    cases hs : TM0.step M.δ ⟨q, tapeOf M l r⟩ with
    | none =>
      have e : flip bind (TM0.step M.δ) (some ⟨q, tapeOf M l r⟩) = none := hs
      rw [e, iterate_none] at h
      exact absurd h (by simp)
    | some c1 =>
      have e : flip bind (TM0.step M.δ) (some ⟨q, tapeOf M l r⟩) = some c1 := hs
      rw [e] at h
      obtain ⟨l1, r1, hst, ht, hlen⟩ := sim_step M d q l r c1 hs
      obtain ⟨q1, T1⟩ := c1
      change T1 = tapeOf M l1 r1 at ht
      subst ht
      obtain ⟨l2, r2, hr, ht2, hlen2⟩ := ih q1 l1 r1 c' h
      exact ⟨l2, r2, Reach.step hst hr, ht2, by omega⟩

/-! ### Writing the output -/

theorem clrL_cons (d : Option B) (q : M.Λ) (reg : Option M.Γ) (x : M.Γ) (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.clrL, (q, reg), stk M [] [] (x :: l) r⟩ : SCfg M) =
      some ⟨some Lbl.clrL, (q, some x), stk M [] [] l r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_set_l, regSome, rd]

theorem clrL_nil (d : Option B) (q : M.Λ) (reg : Option M.Γ) (r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.clrL, (q, reg), stk M [] [] [] r⟩ : SCfg M) =
      some ⟨some Lbl.mvOut, (q, none), stk M [] [] [] r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_set_l, regSome, rd]

theorem clrL_loop (d : Option B) (q : M.Λ) (r : List M.Γ) :
    ∀ (l : List M.Γ) (reg : Option M.Γ),
      Reach M d (l.length + 1) ⟨some Lbl.clrL, (q, reg), stk M [] [] l r⟩
        ⟨some Lbl.mvOut, (q, none), stk M [] [] [] r⟩ := by
  intro l
  induction l with
  | nil => intro reg; exact Reach.one (clrL_nil M d q reg r)
  | cons x l ih =>
    intro reg
    exact Reach.step (clrL_cons M d q reg x l r) (ih (some x))

theorem mvOut_cons (d : Option B) (q : M.Λ) (reg : Option M.Γ) (b : B) (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.mvOut, (q, reg), stk M [] [] l (M.out b :: r)⟩ : SCfg M) =
      some ⟨some Lbl.mvOut, (q, some (M.out b)), stk M [] [] (M.out b :: l) r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_r, stk_set_l, stk_set_r, rd, top, isOut_out]

theorem mvOut_stop (d : Option B) (q : M.Λ) (reg : Option M.Γ) (l r : List M.Γ)
    (h : isOut M r.head? = false) :
    TM2.step (prog M d) (⟨some Lbl.mvOut, (q, reg), stk M [] [] l r⟩ : SCfg M) =
      some ⟨some Lbl.clrR, (q, r.head?), stk M [] [] l r.tail⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_r, stk_set_l, stk_set_r, rd, top, h]

theorem mvOut_loop (d : Option B) (q : M.Λ) (rest : List M.Γ) (h : isOut M rest.head? = false) :
    ∀ (w : List B) (l : List M.Γ) (reg : Option M.Γ),
      Reach M d (w.length + 1) ⟨some Lbl.mvOut, (q, reg), stk M [] [] l (w.map M.out ++ rest)⟩
        ⟨some Lbl.clrR, (q, rest.head?), stk M [] [] ((w.map M.out).reverse ++ l) rest.tail⟩ := by
  intro w
  induction w with
  | nil => intro l reg; exact Reach.one (mvOut_stop M d q reg l rest h)
  | cons b w ih =>
    intro l reg
    have h' := Reach.step (mvOut_cons M d q reg b l (w.map M.out ++ rest))
      (ih (M.out b :: l) (some (M.out b)))
    simpa using h'

theorem clrR_cons (d : Option B) (q : M.Λ) (reg : Option M.Γ) (x : M.Γ) (l r : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.clrR, (q, reg), stk M [] [] l (x :: r)⟩ : SCfg M) =
      some ⟨some Lbl.clrR, (q, some x), stk M [] [] l r⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_r, stk_set_r, regSome, rd]

theorem clrR_nil (d : Option B) (q : M.Λ) (reg : Option M.Γ) (l : List M.Γ) :
    TM2.step (prog M d) (⟨some Lbl.clrR, (q, reg), stk M [] [] l []⟩ : SCfg M) =
      some ⟨some Lbl.fin, (q, none), stk M [] [] l []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_r, stk_set_r, regSome, rd]

theorem clrR_loop (d : Option B) (q : M.Λ) (l : List M.Γ) :
    ∀ (r : List M.Γ) (reg : Option M.Γ),
      Reach M d (r.length + 1) ⟨some Lbl.clrR, (q, reg), stk M [] [] l r⟩
        ⟨some Lbl.fin, (q, none), stk M [] [] l []⟩ := by
  intro r
  induction r with
  | nil => intro reg; exact Reach.one (clrR_nil M d q reg l)
  | cons x r ih =>
    intro reg
    exact Reach.step (clrR_cons M d q reg x l r) (ih (some x))

theorem fin_cons (b₀ : B) (q : M.Λ) (reg : Option M.Γ) (b : B) (o : List B) (l : List M.Γ) :
    TM2.step (prog M (some b₀)) (⟨some Lbl.fin, (q, reg), stk M [] o (M.out b :: l) []⟩ : SCfg M) =
      some ⟨some Lbl.fin, (q, some (M.out b)), stk M [] (b :: o) l []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_o, stk_set_l, stk_set_o, regSome, rd, dec_out]

theorem fin_nil (d : Option B) (q : M.Λ) (reg : Option M.Γ) (o : List B) :
    TM2.step (prog M d) (⟨some Lbl.fin, (q, reg), stk M [] o [] []⟩ : SCfg M) =
      some ⟨none, (default, none), stk M [] o [] []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, stk_l, stk_set_l, regSome, rd]

theorem fin_loop (d : Option B) (hd : ∀ _ : B, ∃ b₀, d = some b₀) (q : M.Λ) :
    ∀ (w : List B) (o : List B) (reg : Option M.Γ),
      Reach M d (w.length + 1) ⟨some Lbl.fin, (q, reg), stk M [] o (w.map M.out) []⟩
        ⟨none, (default, none), stk M [] (w.reverse ++ o) [] []⟩ := by
  intro w
  induction w with
  | nil => intro o reg; exact Reach.one (fin_nil M d q reg o)
  | cons b w ih =>
    intro o reg
    obtain ⟨b₀, hb₀⟩ := hd b
    subst hb₀
    have h' := Reach.step (fin_cons M b₀ q reg b o (w.map M.out)) (ih (b :: o) (some (M.out b)))
    simpa using h'

/-- A right stack that shows `w` is `w` followed by a rest that starts with no output letter. -/
theorem shows_split : ∀ (w : List B) (r : List M.Γ),
    (∀ (i : ℕ) (h : i < w.length), r.getI i = M.out (w[i]'h)) →
    (∀ b : B, r.getI w.length ≠ M.out b) →
    ∃ rest, r = w.map M.out ++ rest ∧ isOut M rest.head? = false := by
  intro w
  induction w with
  | nil =>
    intro r _ h2
    refine ⟨r, rfl, ?_⟩
    rw [Bool.eq_false_iff]
    intro hc
    obtain ⟨b, hb⟩ := (isOut_iff M _).mp hc
    apply h2 b
    cases r with
    | nil => exact absurd hb (by simp)
    | cons x r =>
      have hx : x = M.out b := Option.some.inj hb
      rw [hx]
      exact List.getI_cons_zero _ _
  | cons b w ih =>
    intro r h1 h2
    cases r with
    | nil =>
      have h0 := h1 0 (Nat.succ_pos _)
      rw [List.getI_nil] at h0
      exact absurd h0.symm (M.out_ne_blank b)
    | cons x r =>
      have hx : x = M.out b := by
        have h0 := h1 0 (Nat.succ_pos _)
        rw [List.getI_cons_zero] at h0
        exact h0
      have h1' : ∀ (i : ℕ) (h : i < w.length), r.getI i = M.out (w[i]'h) := by
        intro i h
        have hi := h1 (i + 1) (Nat.succ_lt_succ h)
        rw [List.getI_cons_succ] at hi
        exact hi
      have h2' : ∀ b' : B, r.getI w.length ≠ M.out b' := by
        intro b'
        have hi := h2 b'
        rw [List.length_cons, List.getI_cons_succ] at hi
        exact hi
      obtain ⟨rest, hr, ho⟩ := ih r h1' h2'
      refine ⟨rest, ?_, ho⟩
      rw [hx, hr]
      rfl

/-! ### The whole run -/

theorem run (d : Option B) (hd : ∀ _ : B, ∃ b₀, d = some b₀) (s : List A) (w : List B) (t : ℕ)
    (h : M.OutputsInTime s w t) :
    ∃ N, N ≤ 4 * s.length + 3 * t + 7 ∧
      Reach M d N ⟨some Lbl.ld1, (default, none), stk M s [] [] []⟩
        ⟨none, (default, none), stk M [] w [] []⟩ := by
  obtain ⟨c, ⟨ev⟩, hhalt, hshow⟩ := h
  have hrun : (flip bind (TM0.step M.δ))^[ev.steps]
      (some ⟨default, tapeOf M [] (s.map M.inp)⟩) = some c := ev.evals_in_steps
  obtain ⟨l', r', hsim, htape, hlen⟩ := sim_run M d ev.steps default [] (s.map M.inp) c hrun
  have hle := ev.steps_le_m
  obtain ⟨qc, Tc⟩ := c
  change Tc = tapeOf M l' r' at htape
  subst htape
  have hstop := sim_halt M d qc l' r' hhalt
  have hr0 : (tapeOf M l' r').right₀ = ListBlank.mk r' := Tape.mk'_right₀ _ _
  have hs1 : ∀ (i : ℕ) (h : i < w.length), r'.getI i = M.out (w[i]'h) := by
    intro i hi
    have h0 := hshow.1 i hi
    change (tapeOf M l' r').right₀.nth i = _ at h0
    rw [hr0, ListBlank.nth_mk] at h0
    exact h0
  have hs2 : ∀ b : B, r'.getI w.length ≠ M.out b := by
    intro b
    have h0 := hshow.2 b
    change (tapeOf M l' r').right₀.nth w.length ≠ _ at h0
    rw [hr0, ListBlank.nth_mk] at h0
    exact h0
  obtain ⟨rest, hr, hrest⟩ := shows_split M w r' hs1 hs2
  subst hr
  have h1 : Reach M d (s.length + 1) ⟨some Lbl.ld1, (default, none), stk M s [] [] []⟩
      ⟨some Lbl.ld2, (default, none), stk M [] [] (s.map M.inp).reverse []⟩ := by
    simpa using load1 M d default [] [] s [] none
  have h2 : Reach M d (s.length + 1)
      ⟨some Lbl.ld2, (default, none), stk M [] [] (s.map M.inp).reverse []⟩
      ⟨some Lbl.sim, (default, none), stk M [] [] [] (s.map M.inp)⟩ := by
    simpa using load2 M d default [] [] (s.map M.inp).reverse [] none
  have h3 := clrL_loop M d qc (w.map M.out ++ rest) l' ((w.map M.out ++ rest).head?)
  have h4 : Reach M d (w.length + 1)
      ⟨some Lbl.mvOut, (qc, none), stk M [] [] [] (w.map M.out ++ rest)⟩
      ⟨some Lbl.clrR, (qc, rest.head?), stk M [] [] (w.reverse.map M.out) rest.tail⟩ := by
    simpa using mvOut_loop M d qc rest hrest w [] none
  have h5 := clrR_loop M d qc (w.reverse.map M.out) rest.tail rest.head?
  have h6 : Reach M d (w.length + 1)
      ⟨some Lbl.fin, (qc, none), stk M [] [] (w.reverse.map M.out) []⟩
      ⟨none, (default, none), stk M [] w [] []⟩ := by
    simpa using fin_loop M d hd qc w.reverse [] none
  refine ⟨_, ?_, ((((((h1.trans h2).trans hsim).trans (Reach.one hstop)).trans h3).trans
    h4).trans h5).trans h6⟩
  simp only [List.length_append, List.length_map, List.length_nil, List.length_tail] at hlen ⊢
  omega

theorem init_eq (d : Option B) (s : List A) :
    initList (tm2 M d) s =
      (⟨some Lbl.ld1, (default, none), stk M s [] [] []⟩ : SCfg M) := by
  unfold initList
  congr 1
  funext k
  rcases k with (_ | _) | (_ | _) <;> rfl

theorem halt_eq (d : Option B) (w : List B) :
    haltList (tm2 M d) w =
      (⟨none, (default, none), stk M [] w [] []⟩ : SCfg M) := by
  unfold haltList
  congr 1
  funext k
  rcases k with (_ | _) | (_ | _) <;> rfl

theorem outputs (d : Option B) (s : List A) (w : List B) (N t : ℕ) (hN : N ≤ t)
    (h : Reach M d N ⟨some Lbl.ld1, (default, none), stk M s [] [] []⟩
      ⟨none, (default, none), stk M [] w [] []⟩) :
    Nonempty (TM2OutputsInTime (tm2 M d) (List.map (Equiv.refl A).invFun s)
      (some (List.map (Equiv.refl B).invFun w)) t) := by
  have e1 : (List.map (Equiv.refl A).invFun s : List ((tm2 M d).Γ (tm2 M d).k₀)) = s :=
    List.map_id s
  have e2 : (List.map (Equiv.refl B).invFun w : List ((tm2 M d).Γ (tm2 M d).k₁)) = w :=
    List.map_id w
  rw [e1, e2]
  refine ⟨⟨⟨N, ?_⟩, hN⟩⟩
  show (flip bind (TM2.step (prog M d)))^[N] (some (initList (tm2 M d) s)) =
    some (haltList (tm2 M d) w)
  rw [init_eq, halt_eq]
  exact h

theorem polyTime {α β : Type} (ea : α → List A) (eb : β → List B) (f : α → β)
    (p : Polynomial ℕ)
    (hM : ∀ a : α, M.OutputsInTime (ea a) (eb (f a)) (p.eval (ea a).length)) :
    PvsNP.PolyTimeComputable ea eb f := by
  obtain ⟨d, hd⟩ : ∃ d : Option B, ∀ _ : B, ∃ b₀, d = some b₀ := by
    by_cases hB : Nonempty B
    · obtain ⟨b⟩ := hB
      exact ⟨some b, fun _ => ⟨b, rfl⟩⟩
    · exact ⟨none, fun b => absurd ⟨b⟩ hB⟩
  have key : ∀ a : α, ∃ N,
      N ≤ (Polynomial.C 4 * Polynomial.X + Polynomial.C 3 * p + Polynomial.C 7).eval
        (ea a).length ∧
      Reach M d N ⟨some Lbl.ld1, (default, none), stk M (ea a) [] [] []⟩
        ⟨none, (default, none), stk M [] (eb (f a)) [] []⟩ := by
    intro a
    obtain ⟨N, hN, hr⟩ := run M d hd (ea a) (eb (f a)) _ (hM a)
    refine ⟨N, ?_, hr⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  exact ⟨{
    tm := tm2 M d
    inputAlphabet := Equiv.refl A
    outputAlphabet := Equiv.refl B
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 3 * p + Polynomial.C 7
    outputsFun := fun a =>
      Classical.choice (outputs M d (ea a) (eb (f a)) _ _ (Classical.choose_spec (key a)).1
        (Classical.choose_spec (key a)).2) }⟩

end machine

end PvsNP.Units.m1_st_to_tm2

/-- A function a single-tape machine computes in polynomial time is computed in polynomial time
by a multi-stack machine of Mathlib: the tape is kept on two stacks, and each step of the
single-tape machine is one step of the multi-stack machine. -/
theorem PvsNP.Units.m1_st_to_tm2 :
    ∀ {α β A B : Type} (ea : α → List A) (eb : β → List B) (f : α → β),
      PvsNP.SingleTape.PolyTimeComputable ea eb f → PvsNP.PolyTimeComputable ea eb f := by
  intro α β A B ea eb f h
  obtain ⟨M, p, hM⟩ := h
  exact PvsNP.Units.m1_st_to_tm2.polyTime M ea eb f p hM
