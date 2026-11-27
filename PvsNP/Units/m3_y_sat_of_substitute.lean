import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_sat_of_substitute :
  ∀ (N : cnf) (x : var) (m : literal),
    SAT (N.map (fun C => C.map (fun l => if l.2 = x then (if l.1 then m else (!m.1, m.2)) else l))) → SAT N := by
  intro N x m hsat
  obtain ⟨a, ha⟩ := hsat
  let a' : assgn := if evalLiteral a m = true then x :: a else a.filter (fun v => decide (v ≠ x))
  have hvar : ∀ v : var, evalVar a' v = if v = x then evalLiteral a m else evalVar a v := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      cases hm : evalLiteral a m <;> simp [a', hm, evalVar]
    · cases hm : evalLiteral a m <;> simp [a', hm, evalVar, hvx]
  have hlit : ∀ l : literal,
      evalLiteral a' l = evalLiteral a (if l.2 = x then (if l.1 then m else (!m.1, m.2)) else l) := by
    rintro ⟨s, v⟩
    by_cases hvx : v = x
    · subst hvx
      rcases m with ⟨ms, mv⟩
      cases s <;> simp only [evalLiteral, hvar v, ↓reduceIte, Bool.false_eq_true] <;>
        cases evalVar a mv <;> cases ms <;> rfl
    · simp only [evalLiteral, hvar v, hvx, ↓reduceIte]
  have hcl : ∀ C : clause,
      evalClause a' C = evalClause a (C.map (fun l => if l.2 = x then (if l.1 then m else (!m.1, m.2)) else l)) := by
    intro C
    induction C with
    | nil => rfl
    | cons l C ih =>
      simp only [evalClause, List.map_cons, List.any_cons]
      rw [hlit l]
      congr 1
  have hcnf : ∀ M : cnf, evalCnf a' M =
      evalCnf a (M.map (fun C => C.map (fun l => if l.2 = x then (if l.1 then m else (!m.1, m.2)) else l))) := by
    intro M
    induction M with
    | nil => rfl
    | cons C M ih =>
      simp only [evalCnf, List.map_cons, List.all_cons]
      rw [hcl C]
      congr 1
  exact ⟨a', by rw [satisfiesCnf, hcnf N]; exact ha⟩
