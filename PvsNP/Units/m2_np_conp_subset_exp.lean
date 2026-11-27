import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_np_in_exp
import PvsNP.Units.m2_conp_in_exp
import PvsNP.Units.m2_eb_final

namespace PvsNP.Units.m2_np_conp_subset_exp

theorem exp_bound (k n : ℕ) : n ^ k + k ≤ (k + 1) * (n + 1) ^ k := by
  have h1 : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
  have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
  nlinarith

theorem norm {L : Language Bool}
    (h : ∃ f : List Bool → Bool, (∀ x, x ∈ L ↔ f x = true) ∧
      ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (k : ℕ),
        ∀ n, h.time n ≤ 2 ^ (n ^ k + k)) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨f, hf, M, k, hk⟩ := h
  obtain ⟨j, hj⟩ := PvsNP.Units.m2_eb_final M.time ⟨k + 1, k, fun n =>
    (hk n).trans (Nat.pow_le_pow_right (by norm_num) (exp_bound k n))⟩
  exact ⟨j, f, M, hf, hj⟩

end PvsNP.Units.m2_np_conp_subset_exp

theorem PvsNP.Units.m2_np_conp_subset_exp : ∀ L : Language Bool, L ∈ PvsNP.NP ∨ L ∈ PvsNP.coNP →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  rcases hL with h | h
  · exact PvsNP.Units.m2_np_conp_subset_exp.norm (PvsNP.Units.fr_np_in_exp L h)
  · exact PvsNP.Units.m2_np_conp_subset_exp.norm (PvsNP.Units.m2_conp_in_exp L h)
