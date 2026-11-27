import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_exp_union

theorem PvsNP.Units.m2_exp_finite_patch :
    ∀ (L L' : Language Bool) (S : Finset (List Bool)), (∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  classical
  intro L L' S hPatch hLexp
  have hSexp := PvsNP.Units.m2_p_subset_exp _ (PvsNP.Units.m2_p_finite S)
  have hScexp := PvsNP.Units.m2_exp_compl _ hSexp
  have hLSc := PvsNP.Units.m2_exp_inter L _ hLexp hScexp
  have hTexp := PvsNP.Units.m2_p_subset_exp _ (PvsNP.Units.m2_p_finite (S.filter (· ∈ L')))
  have hUnion := PvsNP.Units.m2_exp_union _ _ hLSc hTexp
  have hEq : ∀ x : List Bool,
      x ∈ L' ↔
        x ∈ (L ⊓ ({x : List Bool | x ∈ S} : Language Bool)ᶜ) ⊔
          ({x : List Bool | x ∈ S.filter (· ∈ L')} : Language Bool) := by
    intro x
    constructor
    · intro hx
      by_cases hxs : x ∈ S
      · right
        exact Finset.mem_filter.mpr ⟨hxs, hx⟩
      · left
        exact ⟨(hPatch x hxs).2 hx, hxs⟩
    · intro hx
      rcases hx with ⟨hxL, hxS⟩ | hxT
      · exact (hPatch x hxS).1 hxL
      · exact (Finset.mem_filter.mp hxT).2
  obtain ⟨k, f, M, hf, ht⟩ := hUnion
  exact ⟨k, f, M, fun x => (hEq x).trans (hf x), ht⟩
