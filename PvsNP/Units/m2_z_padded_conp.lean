import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union

set_option autoImplicit false

/-- Polynomial padding by `|x|^k` trues preserves membership in coNP (TM2). -/
theorem PvsNP.Units.m2_z_padded_conp :
    ∀ (L : Language Bool) (k : ℕ), L ∈ PvsNP.coNP →
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.coNP := by
  intro L k hL
  have hLc : Lᶜ ∈ PvsNP.NP := hL
  have hShapeComplNP :
      ({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool)ᶜ ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np
      (PvsNP.Units.m2_p_compl _ (PvsNP.Units.m2_np_poly_padding_iff.shape_in_P k))
  have hPadLcNP :
      ({s : List Bool | ∃ x : List Bool, x ∈ Lᶜ ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.NP :=
    (PvsNP.Units.m2_np_poly_padding_iff Lᶜ k).mp hLc
  have hUnion :
      (({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool)ᶜ ⊔
        ({s : List Bool | ∃ x : List Bool, x ∈ Lᶜ ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool)) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_union _ _ hShapeComplNP hPadLcNP
  have heq :
      (({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool)ᶜ ⊔
        ({s : List Bool | ∃ x : List Bool, x ∈ Lᶜ ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool)) =
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool)ᶜ := by
    ext s
    constructor
    · rintro (hNotShape | ⟨y, hy, rfl⟩)
      · rintro ⟨x, _, rfl⟩
        exact hNotShape ⟨x, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        have hd := congrArg PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN hxy
        have hdy : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (List.replicate (y.length ^ k) true ++ false :: y) = y :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (y.length ^ k) y
        have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (List.replicate (x.length ^ k) true ++ false :: x) = x :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
        rw [hdy, hdx] at hd
        subst hd
        exact hy hx
    · intro hs
      by_cases hShape : s ∈ ({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool)
      · rcases hShape with ⟨x, rfl⟩
        refine Or.inr ⟨x, ?_, rfl⟩
        intro hx
        exact hs ⟨x, hx, rfl⟩
      · exact Or.inl hShape
  show ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool)ᶜ ∈ PvsNP.NP
  rw [← heq]
  exact hUnion
