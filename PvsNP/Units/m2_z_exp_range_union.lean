import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_union
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_p_trivial

/-- Induct on the finite index bound, adjoining one language with binary union. -/
theorem PvsNP.Units.m2_z_exp_range_union :
    ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ F i ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro F m
  induction m with
  | zero =>
    intro _
    have base : ({x : List Bool | ∃ i < 0, x ∈ F i} : Language Bool) =
        (∅ : Set (List Bool)) := by
      ext x
      simp
    rw [base]
    exact PvsNP.Units.m2_p_subset_exp _ PvsNP.Units.m2_p_trivial.1
  | succ m ih =>
    intro h
    have split : ({x : List Bool | ∃ i < m + 1, x ∈ F i} : Language Bool) =
        ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ⊔ F m := by
      ext x
      change (∃ i < m + 1, x ∈ F i) ↔ (∃ i < m, x ∈ F i) ∨ x ∈ F m
      constructor
      · rintro ⟨i, hi, member⟩
        by_cases h : i = m
        · exact Or.inr (by simpa [h] using member)
        · exact Or.inl ⟨i, by omega, member⟩
      · rintro (⟨i, hi, member⟩ | last)
        · exact ⟨i, by omega, member⟩
        · exact ⟨m, by omega, last⟩
    rw [split]
    exact PvsNP.Units.m2_exp_union _ _ (ih (fun i hi => h i (by omega))) (h m (by omega))
