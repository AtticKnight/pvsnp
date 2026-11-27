import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_honest_image
import PvsNP.Units.tf_fun_self_append

/-- NP is closed under doubling (TM2): the image of `L` under the honest
polytime map `u ↦ u ++ u`. -/
theorem PvsNP.Units.tc_closure_double_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have h := PvsNP.Units.m2_np_honest_image (fun x : List Bool => x ++ x) L
    PvsNP.Units.tf_fun_self_append
    (fun x => by simp) hL
  have e : ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) =
      ({y : List Bool | ∃ x ∈ L, (fun x : List Bool => x ++ x) x = y} : Language Bool) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [e]
  exact h
