import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_p_subset_np_conp
import PvsNP.Units.m2_conp_inter

open PvsNP.Units.m2_np_poly_padding_iff (padPoly cpt_padPoly shape_in_P)
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal (dropN dropN_un cpt_dropN)

/-- Recognize the padding shape and test the decoded suffix in the original language. -/
theorem PvsNP.Units.m2_z_padded_conp :
    ∀ (L : Language Bool) (k : ℕ), L ∈ PvsNP.coNP →
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
        s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.coNP := by
  intro L k hL
  let shape : Language Bool := {s | ∃ x : List Bool, s = padPoly k x}
  let decoded : Language Bool := {s | dropN s ∈ L}
  have hs : shape ∈ PvsNP.coNP := (PvsNP.Units.m2_p_subset_np_conp (shape_in_P k)).2
  have hd : decoded ∈ PvsNP.coNP :=
    PvsNP.Units.m2_conp_down_closed decoded L ⟨dropN, cpt_dropN, fun _ => Iff.rfl⟩ hL
  have undo (x : List Bool) : dropN (padPoly k x) = x := dropN_un (x.length ^ k) x
  have same : shape ⊓ decoded = ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
        s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) := by
    ext s
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      change dropN (padPoly k x) ∈ L at hx
      exact ⟨x, undo x ▸ hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      change dropN (padPoly k x) ∈ L
      rwa [undo]
  exact same ▸ PvsNP.Units.m2_conp_inter shape decoded hs hd
