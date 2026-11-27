import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_np_honest_image

theorem PvsNP.Units.tc_closure_hom_np :
    ∀ h : Bool → List Bool, (∀ b, h b ≠ []) → ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({y : List Bool | ∃ x ∈ L, y = x.flatMap h} : Language Bool) ∈ PvsNP.NP := by
  intro h hne L hL
  have hhonest : ∀ x : List Bool, x.length ≤ (x.flatMap h).length := by
    intro x
    induction x with
    | nil => simp
    | cons b xs ih =>
        have hb : 1 ≤ (h b).length := List.length_pos_iff.mpr (hne b)
        simp only [List.flatMap_cons, List.length_cons, List.length_append]
        omega
  have heq : ({y : List Bool | ∃ x ∈ L, y = x.flatMap h} : Language Bool) =
      ({y : List Bool | ∃ x ∈ L, x.flatMap h = y} : Language Bool) := by
    ext y
    exact ⟨fun ⟨x, hx, hy⟩ => ⟨x, hx, hy.symm⟩, fun ⟨x, hx, hy⟩ => ⟨x, hx, hy.symm⟩⟩
  rw [heq]
  exact PvsNP.Units.m2_np_honest_image (fun x => x.flatMap h) L
    (PvsNP.Units.m2_inv_hom_closed.cpt_flatMap h) hhonest hL
