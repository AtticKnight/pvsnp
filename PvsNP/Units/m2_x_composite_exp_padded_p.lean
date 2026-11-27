import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_composite_np
import PvsNP.Units.m2_np_conp_subset_exp
import PvsNP.Units.m2_exp_iff_padded_p

/-- Some exponential padding of the composites is in P (TM2): the composites are in NP
    (settled unit `tl_lang_composite_np`), hence decided in time `2 ^ (n ^ k) + k`
    (settled unit `m2_np_conp_subset_exp`), and the exponential padding of a language so
    decided is in P (settled unit `m2_exp_iff_padded_p`). -/
theorem PvsNP.Units.m2_x_composite_exp_padded_p :
    ∃ k : ℕ, ({s : List Bool | ∃ x : List Bool, (∃ a b : ℕ, 1 < a ∧ 1 < b ∧
        a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ∧
        s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈
      PvsNP.P := by
  have hNP : ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧
        a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.tl_lang_composite_np
  obtain ⟨k, f, M, hf, hM⟩ :=
    PvsNP.Units.m2_np_conp_subset_exp _ (Or.inl hNP)
  exact (PvsNP.Units.m2_exp_iff_padded_p _).mp ⟨k, f, M, hf, hM⟩
