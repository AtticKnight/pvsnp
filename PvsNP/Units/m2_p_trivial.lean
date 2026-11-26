import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_p_trivial

open Turing

/-- One stack of bits: pop until the stack is empty, then push `c` and halt. The state records
whether the last pop found a symbol; it is `false`, the initial state, when the machine halts. -/
def constTM (c : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun _ => TM2.Stmt.pop () (fun _ o => o.isSome)
    (TM2.Stmt.branch id (TM2.Stmt.goto fun _ => ())
      (TM2.Stmt.push () (fun _ => c) TM2.Stmt.halt))

/-- A configuration of `constTM c` at its one label, with state `v` and stack `l`. -/
def cfgAt (c : Bool) (v : Bool) (l : List Bool) : (constTM c).Cfg :=
  ⟨some (), v, fun _ => l⟩

/-- The halted configuration with state `false` and stack `[c]`. -/
def cfgDone (c : Bool) : (constTM c).Cfg :=
  ⟨none, false, fun _ => [c]⟩

theorem step_cons (c v b : Bool) (l : List Bool) :
    (constTM c).step (cfgAt c v (b :: l)) = some (cfgAt c true l) := by
  simp only [FinTM2.step, cfgAt, constTM, TM2.step, TM2.stepAux, List.head?_cons,
    Option.isSome_some, id, Bool.cond_true, List.tail_cons]
  all_goals (congr 2 <;> funext k <;> simp [Function.update])

theorem step_nil (c v : Bool) :
    (constTM c).step (cfgAt c v []) = some (cfgDone c) := by
  simp only [FinTM2.step, cfgAt, cfgDone, constTM, TM2.step, TM2.stepAux, List.head?_nil,
    Option.isSome_none, id, Bool.cond_false, List.tail_nil]
  all_goals (congr 2 <;> funext k <;> simp [Function.update])

theorem iter (c : Bool) : ∀ (l : List Bool) (v : Bool),
    (flip bind (constTM c).step)^[l.length + 1] (some (cfgAt c v l)) = some (cfgDone c)
  | [], v => by
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
      exact step_nil c v
  | b :: l, v => by
      rw [List.length_cons, Function.iterate_succ_apply]
      show (flip bind (constTM c).step)^[l.length + 1] ((constTM c).step (cfgAt c v (b :: l))) = _
      rw [step_cons]
      exact iter c l true

theorem initList_eq (c : Bool) (s : List Bool) : initList (constTM c) s = cfgAt c false s := by
  simp only [initList, cfgAt]
  all_goals (congr 1 <;> funext k <;> cases k <;> rfl)

theorem haltList_eq (c : Bool) : haltList (constTM c) [c] = cfgDone c := by
  simp only [haltList, cfgDone]
  all_goals (congr 1 <;> funext k <;> cases k <;> rfl)

/-- From the initial configuration on any input, the machine halts with [c] in |s| + 1 steps. -/
theorem iterInit (c : Bool) (s : List Bool) :
    (flip bind (constTM c).step)^[s.length + 1] (some (initList (constTM c) s)) =
      some (haltList (constTM c) [c]) := by
  rw [initList_eq, haltList_eq]
  exact iter c s false

/-- A constant answer is computable in polynomial time: `|x| + 1` steps. -/
noncomputable def constPoly (c : Bool) :
    TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer (fun _ : List Bool => c) where
  tm := constTM c
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun x :=
    { steps := x.length + 1
      evals_in_steps := by
        have h := iterInit c (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x))
        rw [List.length_map] at h
        exact h
      steps_le_m := by
        simp [PvsNP.encodeString, Computability.encodingList] }

theorem constant_polyTime (c : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun _ : List Bool => c) :=
  ⟨constPoly c⟩

end PvsNP.Units.m2_p_trivial


theorem PvsNP.Units.m2_p_trivial :
    (∅ : Set (List Bool)) ∈ PvsNP.P ∧ (Set.univ : Set (List Bool)) ∈ PvsNP.P :=
  ⟨⟨fun _ => false, PvsNP.Units.m2_p_trivial.constant_polyTime false, fun _ => ⟨fun h => (h : False).elim, fun h => by simp at h⟩⟩,
   ⟨fun _ => true, PvsNP.Units.m2_p_trivial.constant_polyTime true, fun _ => ⟨fun _ => rfl, fun _ => trivial⟩⟩⟩

