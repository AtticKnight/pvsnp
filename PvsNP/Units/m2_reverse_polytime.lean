import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_reverse_polytime

open Turing

/-- Stack state with `a` on stack `false` (input) and `b` on stack `true` (output). -/
def revStk (a b : List Bool) : Bool → List Bool
  | false => a
  | true => b

/-- Single-label statement: pop a bit from stack `false` and push it onto stack `true`,
or halt when stack `false` is empty. -/
def revStmt : TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool) :=
  .pop false (fun _ o => o)
    (.branch Option.isSome
      (.push true (fun o => o.getD false) (.goto fun _ => ()))
      .halt)

/-- Two-stack TM2 that reverses its binary input string. -/
def revTM : FinTM2 :=
  { K := Bool
    k₀ := false
    k₁ := true
    Γ := fun _ => Bool
    Λ := Unit
    main := ()
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstance
    m := fun _ => revStmt }

theorem initList_revTM (x : List Bool) :
    initList revTM x = (⟨some (), none, revStk x []⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_revTM (y : List Bool) :
    haltList revTM y = (⟨none, none, revStk [] y⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

theorem revStep_cons (c : Bool) (a b : List Bool) (v : Option Bool) :
    TM2.step revTM.m (⟨some (), v, revStk (c :: a) b⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ) =
      some ⟨some (), some c, revStk a (c :: b)⟩ := by
  simp only [TM2.step, revTM, revStmt, TM2.stepAux, revStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 2
  funext k
  cases k <;> rfl

theorem revStep_nil (b : List Bool) (v : Option Bool) :
    TM2.step revTM.m (⟨some (), v, revStk [] b⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ) =
      some ⟨none, none, revStk [] b⟩ := by
  simp only [TM2.step, revTM, revStmt, TM2.stepAux, revStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  congr 2
  funext k
  cases k <;> rfl

theorem revLoop : ∀ (a b : List Bool) (v : Option Bool),
    (flip bind (TM2.step revTM.m))^[a.length + 1]
        (some (⟨some (), v, revStk a b⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ)) =
      some ⟨none, none, revStk [] (a.reverse ++ b)⟩ := by
  intro a
  induction a with
  | nil =>
    intro b v
    exact revStep_nil b v
  | cons c a ih =>
    intro b v
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step revTM.m)
        (some (⟨some (), v, revStk (c :: a) b⟩ : TM2.Cfg revTM.Γ revTM.Λ revTM.σ)) =
        some ⟨some (), some c, revStk a (c :: b)⟩ :=
      revStep_cons c a b v
    rw [hstep, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def inEquiv : revTM.Γ revTM.k₀ ≃ Bool := Equiv.refl Bool

def outEquiv : revTM.Γ revTM.k₁ ≃ Bool := Equiv.refl Bool

noncomputable def rev_outputs (x : List Bool) :
    TM2OutputsInTime revTM
      (List.map inEquiv.invFun (PvsNP.encodeString x))
      (some (List.map outEquiv.invFun (PvsNP.encodeString x.reverse)))
      ((Polynomial.X + Polynomial.C 1).eval (PvsNP.encodeString x).length) :=
  { steps := x.length + 1
    evals_in_steps := by
      have h1 : List.map inEquiv.invFun (PvsNP.encodeString x) = x :=
        List.map_id x
      have h2 : List.map outEquiv.invFun (PvsNP.encodeString x.reverse) = x.reverse :=
        List.map_id x.reverse
      show (flip bind (TM2.step revTM.m))^[x.length + 1]
          (some (initList revTM (List.map inEquiv.invFun (PvsNP.encodeString x)))) =
        some (haltList revTM (List.map outEquiv.invFun (PvsNP.encodeString x.reverse)))
      rw [h1, h2, initList_revTM, haltList_revTM]
      have h := revLoop x [] none
      rw [List.append_nil] at h
      exact h
    steps_le_m := by
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        PvsNP.encodeString, Computability.encodingList, id_eq]
      exact le_refl _ }

end PvsNP.Units.m2_reverse_polytime

theorem PvsNP.Units.m2_reverse_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse) :=
  ⟨{ tm := PvsNP.Units.m2_reverse_polytime.revTM
     inputAlphabet := PvsNP.Units.m2_reverse_polytime.inEquiv
     outputAlphabet := PvsNP.Units.m2_reverse_polytime.outEquiv
     time := Polynomial.X + Polynomial.C 1
     outputsFun := PvsNP.Units.m2_reverse_polytime.rev_outputs }⟩
