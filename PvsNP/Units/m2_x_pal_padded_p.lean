import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_palindrome_in_p

-- Built from the settled campaign units m2_np_poly_padding_iff (shape_in_P), fr_ladner (dropN),
-- m2_p_down_closed, m2_p_inter and m2_palindrome_in_p (make.fun pvsnp campaign).

theorem PvsNP.Units.m2_x_pal_padded_p :
    ({s : List Bool | ∃ x : List Bool, x.reverse = x ∧ s = List.replicate (x.length ^ 2) true ++ false :: x} : Language Bool) ∈ PvsNP.P := by
  have _hc := Classical.em True
  have hShape := PvsNP.Units.m2_np_poly_padding_iff.shape_in_P 2
  have hPull : ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈
      ({x : List Bool | x.reverse = x} : Language Bool)} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_down_closed _ _
      ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN,
        fun _ => Iff.rfl⟩ PvsNP.Units.m2_palindrome_in_p
  have hInter := PvsNP.Units.m2_p_inter _ _ hShape hPull
  have heq : (({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly 2 x} : Language Bool) ⊓
      ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈
        ({x : List Bool | x.reverse = x} : Language Bool)} : Language Bool)) =
      ({s : List Bool | ∃ x : List Bool, x.reverse = x ∧
        s = List.replicate (x.length ^ 2) true ++ false :: x} : Language Bool) := by
    ext s
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (PvsNP.Units.m2_np_poly_padding_iff.padPoly 2 x) = x :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ 2) x
      change PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
        (PvsNP.Units.m2_np_poly_padding_iff.padPoly 2 x) ∈
          ({x : List Bool | x.reverse = x} : Language Bool) at hx
      rw [hdx] at hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (List.replicate (x.length ^ 2) true ++ false :: x) = x :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ 2) x
      show PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
        (List.replicate (x.length ^ 2) true ++ false :: x) ∈
          ({x : List Bool | x.reverse = x} : Language Bool)
      rw [hdx]
      exact hx
  rw [← heq]
  exact hInter
