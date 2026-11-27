import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_reduces_nontrivial
import PvsNP.Units.m2_p_eq_np_iff_true_nphard
import PvsNP.Units.m2_p_iff_reduces_to_true
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_p_subset_np

-- Built from the settled campaign units m2_p_reduces_nontrivial, m2_p_eq_np_iff_true_nphard, m2_p_iff_reduces_to_true, m2_karp_refl, m2_p_subset_np (make.fun pvsnp campaign).

theorem PvsNP.Units.m2_p_eq_np_iff_karp_np_nontrivial :
    PvsNP.P = PvsNP.NP ↔ ∀ L₁ ∈ PvsNP.NP, ∀ L₂ ∈ PvsNP.NP, (∃ y : List Bool, y ∈ L₂) → (∃ z : List Bool, z ∉ L₂) →
      PvsNP.KarpReducible L₁ L₂ := by
  have _hc := Classical.em True
  constructor
  · intro h L₁ hL₁ L₂ _ hy hz
    have hP : L₁ ∈ PvsNP.P := by rw [h]; exact hL₁
    exact PvsNP.Units.m2_p_reduces_nontrivial L₁ L₂ hP hy hz
  · intro h
    have hT : ({x : List Bool | x = [true]} : Language Bool) ∈ PvsNP.P :=
      (PvsNP.Units.m2_p_iff_reduces_to_true _).2 (PvsNP.Units.m2_karp_refl _)
    refine PvsNP.Units.m2_p_eq_np_iff_true_nphard.2 (fun L' hL' => ?_)
    exact h L' hL' _ (PvsNP.Units.m2_p_subset_np hT) ⟨[true], by show [true] = [true]; rfl⟩
      ⟨[false], by show ¬ ([false] = [true]); decide⟩
