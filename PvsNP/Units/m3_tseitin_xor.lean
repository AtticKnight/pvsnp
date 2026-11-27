import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_tseitin_xor

theorem sat_cons_iff (a : assgn) (C : clause) (N : cnf) :
    satisfiesCnf a (C :: N) ↔ evalClause a C = true ∧ satisfiesCnf a N := by
  simp [satisfiesCnf, evalCnf, Bool.and_eq_true]

theorem evalLiteral_neg (a : assgn) (l : literal) :
    evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  cases s <;> cases h : evalVar a v <;> simp [evalLiteral, h]

/-- The modified assignment: `z` is set to `b`, all other variables keep their values. -/
def setZ (a : assgn) (z : var) (b : Bool) : assgn :=
  if b then z :: a else a.filter (fun u => decide (u ≠ z))

theorem evalVar_setZ_z (a : assgn) (z : var) (b : Bool) : evalVar (setZ a z b) z = b := by
  cases b <;> simp [setZ, evalVar, List.mem_filter]

theorem evalVar_setZ_ne (a : assgn) (z : var) (b : Bool) (u : var) (hu : u ≠ z) :
    evalVar (setZ a z b) u = evalVar a u := by
  cases b <;> simp [setZ, evalVar, List.mem_filter, hu]

theorem evalLiteral_setZ_z (a : assgn) (z : var) (b s : Bool) :
    evalLiteral (setZ a z b) (s, z) = decide (b = s) := by
  simp only [evalLiteral, evalVar_setZ_z]

theorem evalLiteral_setZ_ne (a : assgn) (z : var) (b : Bool) (l : literal) (hl : l.2 ≠ z) :
    evalLiteral (setZ a z b) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  simp only [evalLiteral]
  rw [evalVar_setZ_ne a z b v hl]

theorem evalClause_setZ (a : assgn) (z : var) (b : Bool) (C : clause)
    (hC : ∀ l ∈ C, l.2 ≠ z) : evalClause (setZ a z b) C = evalClause a C := by
  unfold evalClause
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [List.any_cons]
    rw [evalLiteral_setZ_ne a z b l (hC l (by simp)),
      ih (fun l' hl' => hC l' (List.mem_cons_of_mem _ hl'))]

theorem evalCnf_setZ (a : assgn) (z : var) (b : Bool) (N : cnf)
    (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) : evalCnf (setZ a z b) N = evalCnf a N := by
  unfold evalCnf
  induction N with
  | nil => rfl
  | cons C N ih =>
    simp only [List.all_cons]
    rw [evalClause_setZ a z b C (hN C (by simp)),
      ih (fun C' hC' => hN C' (List.mem_cons_of_mem _ hC'))]

end PvsNP.Units.m3_tseitin_xor

open PvsNP.Units.m3_tseitin_xor in
theorem PvsNP.Units.m3_tseitin_xor :
    ∀ (N : cnf) (z : var) (l₁ l₂ : literal), l₁.2 ≠ z → l₂.2 ≠ z → (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT ([(false, z), l₁, l₂] :: [(false, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] ::
          [(true, z), (!l₁.1, l₁.2), l₂] :: [(true, z), l₁, (!l₂.1, l₂.2)] :: N) ↔ SAT N) := by
  intro N z l₁ l₂ h₁ h₂ hN
  constructor
  · rintro ⟨a, ha⟩
    simp only [sat_cons_iff] at ha
    exact ⟨a, ha.2.2.2.2⟩
  · rintro ⟨a, ha⟩
    refine ⟨setZ a z (xor (evalLiteral a l₁) (evalLiteral a l₂)), ?_⟩
    simp only [sat_cons_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    rotate_left 4
    · unfold satisfiesCnf at ha ⊢
      rw [evalCnf_setZ a z _ N hN]
      exact ha
    all_goals
      simp only [evalClause, List.any_cons, List.any_nil, evalLiteral_neg,
        evalLiteral_setZ_ne a z _ l₁ h₁, evalLiteral_setZ_ne a z _ l₂ h₂]
      rw [evalLiteral_setZ_z]
      generalize evalLiteral a l₁ = x₁
      generalize evalLiteral a l₂ = x₂
      cases x₁ <;> cases x₂ <;> decide
