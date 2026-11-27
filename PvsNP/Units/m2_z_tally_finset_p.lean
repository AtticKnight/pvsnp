import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite

theorem PvsNP.Units.m2_z_tally_finset_p :
    ∀ A : Finset ℕ, ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.P := by
  intro A
  have h := PvsNP.Units.m2_p_finite (A.image (fun n => List.replicate n true))
  convert h using 2
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
