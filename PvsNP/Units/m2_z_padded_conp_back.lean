import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_conp_down_closed

open PvsNP.Units.m2_np_poly_padding_iff (padPoly cpt_padPoly shape_in_P)
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal (dropN dropN_un cpt_dropN)

/-- Padded words decode to their unique source, so padding is a Karp reduction. -/
theorem PvsNP.Units.m2_z_padded_conp_back :
    ∀ (L : Language Bool) (k : ℕ),
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
        s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.coNP → L ∈ PvsNP.coNP := by
  intro L k padded
  have undo (x : List Bool) : dropN (padPoly k x) = x := dropN_un (x.length ^ k) x
  refine PvsNP.Units.m2_conp_down_closed L _ ⟨padPoly k, cpt_padPoly k, fun x => ?_⟩ padded
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, eq⟩
    change padPoly k x = padPoly k y at eq
    have decoded := congrArg dropN eq
    rw [undo, undo] at decoded
    exact decoded.symm ▸ hy
