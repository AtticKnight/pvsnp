import Mathlib
import PvsNP.Defs
import CookLevin

/-
Original proof of `PvsNP.Units.m2_join_compl_self_dual`. The reduction flips the first bit of its
input and sends the empty string (in neither half of the join) to a one-bit string inside the join,
`[false]` when `[] ∈ L` and `[true]` otherwise. A three-stack TM2 machine computes it in two passes
(input to a scratch stack negating the first bit, then scratch to output) within `2 * n + 2`
steps. The two-pass layout follows the one-pass reversal machine of
`PvsNP/Units/m2_reverse_polytime.lean` in this repository.
-/

namespace PvsNP.Units.m2_join_compl_self_dual

open Turing

/-- Flip the first bit; the empty string goes to `[e]`. -/
def flipHead (e : Bool) : List Bool → List Bool
  | [] => [e]
  | b :: y => (!b) :: y

/-- Stack contents: `a` on the input stack `0`, `b` on the output stack `1`, `c` on scratch `2`. -/
def stk (a b c : List Bool) : Fin 3 → List Bool
  | 0 => a
  | 1 => b
  | 2 => c

/-- The state holds the last popped bit and whether no bit has been popped yet. -/
abbrev St := Option Bool × Bool

/-- Label `false` is pass 1 (input to scratch, negating the first bit), label `true` is pass 2
(scratch to output; on an empty input, `e` is written). The state is reset before halting. -/
def prog (e : Bool) : Bool → TM2.Stmt (fun _ : Fin 3 => Bool) Bool St
  | false =>
    .pop 0 (fun s o => (o, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 2 (fun s => xor s.2 (s.1.getD false)) (.load (fun s => (s.1, false))
          (.goto fun _ => false)))
        (.goto fun _ => true))
  | true =>
    .pop 2 (fun s o => (o, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 1 (fun s => s.1.getD false) (.goto fun _ => true))
        (.branch (fun s => s.2)
          (.push 1 (fun _ => e) (.load (fun _ => (none, true)) .halt))
          (.load (fun _ => (none, true)) .halt)))

/-- The flipping machine. -/
def tm (e : Bool) : FinTM2 :=
  { K := Fin 3
    k₀ := 0
    k₁ := 1
    Γ := fun _ => Bool
    Λ := Bool
    main := false
    σ := St
    initialState := (none, true)
    Γk₀Fin := inferInstance
    m := prog e }

abbrev Cfg (e : Bool) := TM2.Cfg (tm e).Γ (tm e).Λ (tm e).σ

variable (e : Bool)

theorem initList_tm (x : List Bool) :
    initList (tm e) x = (⟨some false, (none, true), stk x [] []⟩ : Cfg e) := by
  unfold initList
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem haltList_tm (y : List Bool) :
    haltList (tm e) y = (⟨none, (none, true), stk [] y []⟩ : Cfg e) := by
  unfold haltList
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem step1_cons (f : Bool) (d : Bool) (a c : List Bool) (v : Option Bool) :
    TM2.step (tm e).m (⟨some false, (v, f), stk (d :: a) [] c⟩ : Cfg e) =
      some ⟨some false, (some d, false), stk a [] (xor f d :: c)⟩ := by
  simp only [TM2.step, tm, prog, TM2.stepAux, stk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 2
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem step1_nil (f : Bool) (c : List Bool) (v : Option Bool) :
    TM2.step (tm e).m (⟨some false, (v, f), stk [] [] c⟩ : Cfg e) =
      some ⟨some true, (none, f), stk [] [] c⟩ := by
  simp only [TM2.step, tm, prog, TM2.stepAux, stk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  congr 2
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem step2_cons (f : Bool) (d : Bool) (b c : List Bool) (v : Option Bool) :
    TM2.step (tm e).m (⟨some true, (v, f), stk [] b (d :: c)⟩ : Cfg e) =
      some ⟨some true, (some d, f), stk [] (d :: b) c⟩ := by
  simp only [TM2.step, tm, prog, TM2.stepAux, stk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 2
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem step2_nil_false (b : List Bool) (v : Option Bool) :
    TM2.step (tm e).m (⟨some true, (v, false), stk [] b []⟩ : Cfg e) =
      some ⟨none, (none, true), stk [] b []⟩ := by
  simp only [TM2.step, tm, prog, TM2.stepAux, stk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  congr 2
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem step2_nil_true (b : List Bool) (v : Option Bool) :
    TM2.step (tm e).m (⟨some true, (v, true), stk [] b []⟩ : Cfg e) =
      some ⟨none, (none, true), stk [] (e :: b) []⟩ := by
  simp only [TM2.step, tm, prog, TM2.stepAux, stk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Bool.cond_true]
  congr 2
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem loop2 : ∀ (c b : List Bool) (v : Option Bool),
    (flip bind (TM2.step (tm e).m))^[c.length + 1]
        (some (⟨some true, (v, false), stk [] b c⟩ : Cfg e)) =
      some ⟨none, (none, true), stk [] (c.reverse ++ b) []⟩ := by
  intro c
  induction c with
  | nil => intro b v; exact step2_nil_false e b v
  | cons d c ih =>
    intro b v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h : flip bind (TM2.step (tm e).m) (some (⟨some true, (v, false), stk [] b (d :: c)⟩ : Cfg e)) =
        some ⟨some true, (some d, false), stk [] (d :: b) c⟩ := step2_cons e false d b c v
    rw [h, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem loop1 : ∀ (a c : List Bool) (v : Option Bool),
    (flip bind (TM2.step (tm e).m))^[a.length + 1]
        (some (⟨some false, (v, false), stk a [] c⟩ : Cfg e)) =
      some ⟨some true, (none, false), stk [] [] (a.reverse ++ c)⟩ := by
  intro a
  induction a with
  | nil => intro c v; exact step1_nil e false c v
  | cons d a ih =>
    intro c v
    rw [List.length_cons, Function.iterate_succ_apply]
    have h : flip bind (TM2.step (tm e).m) (some (⟨some false, (v, false), stk (d :: a) [] c⟩ : Cfg e)) =
        some ⟨some false, (some d, false), stk a [] (xor false d :: c)⟩ := step1_cons e false d a c v
    rw [h, ih]
    simp only [Bool.false_xor, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem run (x : List Bool) :
    (flip bind (TM2.step (tm e).m))^[2 * x.length + 2]
        (some (⟨some false, (none, true), stk x [] []⟩ : Cfg e)) =
      some ⟨none, (none, true), stk [] (flipHead e x) []⟩ := by
  rcases x with _ | ⟨d, a⟩
  · show (flip bind (TM2.step (tm e).m))^[1 + 1] _ = _
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]
    have h1 : flip bind (TM2.step (tm e).m) (some (⟨some false, (none, true), stk [] [] []⟩ : Cfg e)) =
        some ⟨some true, (none, true), stk [] [] []⟩ := step1_nil e true [] none
    rw [h1]
    exact step2_nil_true e [] none
  · have hsplit : 2 * (d :: a).length + 2 = (a.reverse ++ [xor true d]).length + 1 + (a.length + 1 + 1) := by
      simp only [List.length_cons, List.length_append, List.length_reverse, List.length_singleton,
        List.length_nil]; omega
    rw [hsplit, Function.iterate_add_apply, Function.iterate_succ_apply _ (a.length + 1)]
    have h1 : flip bind (TM2.step (tm e).m) (some (⟨some false, (none, true), stk (d :: a) [] []⟩ : Cfg e)) =
        some ⟨some false, (some d, false), stk a [] (xor true d :: [])⟩ := step1_cons e true d a [] none
    rw [h1, loop1, loop2]
    simp [flipHead]

def inEquiv : (tm e).Γ (tm e).k₀ ≃ Bool := Equiv.refl Bool

def outEquiv : (tm e).Γ (tm e).k₁ ≃ Bool := Equiv.refl Bool

noncomputable def outputs (x : List Bool) :
    TM2OutputsInTime (tm e)
      (List.map (inEquiv e).invFun (PvsNP.encodeString x))
      (some (List.map (outEquiv e).invFun (PvsNP.encodeString (flipHead e x))))
      ((2 * Polynomial.X + Polynomial.C 2).eval (PvsNP.encodeString x).length) :=
  { steps := 2 * x.length + 2
    evals_in_steps := by
      have h1 : List.map (inEquiv e).invFun (PvsNP.encodeString x) = x := List.map_id x
      have h2 : List.map (outEquiv e).invFun (PvsNP.encodeString (flipHead e x)) = flipHead e x :=
        List.map_id _
      show (flip bind (TM2.step (tm e).m))^[2 * x.length + 2]
          (some (initList (tm e) (List.map (inEquiv e).invFun (PvsNP.encodeString x)))) =
        some (haltList (tm e) (List.map (outEquiv e).invFun (PvsNP.encodeString (flipHead e x))))
      rw [h1, h2, initList_tm, haltList_tm]
      exact run e x
    steps_le_m := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_ofNat, PvsNP.encodeString,
        Computability.encodingList, id_eq]
      norm_num }

theorem flip_polytime : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (flipHead e) :=
  ⟨{ tm := tm e
     inputAlphabet := inEquiv e
     outputAlphabet := outEquiv e
     time := 2 * Polynomial.X + Polynomial.C 2
     outputsFun := outputs e }⟩

end PvsNP.Units.m2_join_compl_self_dual

open Classical in
theorem PvsNP.Units.m2_join_compl_self_dual :
    ∀ L : Language Bool,
      PvsNP.KarpReducible
        ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool)ᶜ := by
  intro L
  refine ⟨PvsNP.Units.m2_join_compl_self_dual.flipHead (decide ([] ∉ L)),
    PvsNP.Units.m2_join_compl_self_dual.flip_polytime _, fun x => ?_⟩
  have hc : ∀ y : List Bool, y ∈ Lᶜ ↔ y ∉ L := fun _ => Iff.rfl
  show _ ↔ ¬ ((∃ y ∈ L, _ = false :: y) ∨ (∃ y ∈ Lᶜ, _ = true :: y))
  show ((∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)) ↔ _
  rcases x with _ | ⟨b, y⟩
  · by_cases h : [] ∈ L
    · simp only [PvsNP.Units.m2_join_compl_self_dual.flipHead, h]
      simp [h]
    · simp only [PvsNP.Units.m2_join_compl_self_dual.flipHead]
      simp [h, hc]
  · cases b <;> simp [PvsNP.Units.m2_join_compl_self_dual.flipHead, hc]
