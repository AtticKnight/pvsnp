import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_some_prefix
import PvsNP.Units.m2_p_all_suffixes

namespace PvsNP.Units.m2_p_all_factors

theorem eq_all_suffixes_no_bad_prefix (L : Language Bool) :
    ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) =
      {x : List Bool | ∀ z : List Bool, z <:+ x →
        z ∈ ({z : List Bool | ∃ y : List Bool, y <+: z ∧ y ∈ Lᶜ} : Language Bool)ᶜ} := by
  ext x
  constructor
  · intro hx z hzx hzBad
    rcases hzBad with ⟨y, ⟨t, rfl⟩, hynL⟩
    rcases hzx with ⟨s, rfl⟩
    exact hynL (hx y ⟨s, t, by simp [List.append_assoc]⟩)
  · intro hx y hyx
    rcases hyx with ⟨s, t, hst⟩
    subst hst
    by_contra hynL
    have hzx : y ++ t <:+ s ++ y ++ t := ⟨s, by simp [List.append_assoc]⟩
    exact hx (y ++ t) hzx ⟨y, ⟨t, rfl⟩, hynL⟩

end PvsNP.Units.m2_p_all_factors

theorem PvsNP.Units.m2_p_all_factors :
    ∀ L ∈ PvsNP.P, ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  rw [PvsNP.Units.m2_p_all_factors.eq_all_suffixes_no_bad_prefix]
  exact PvsNP.Units.m2_p_all_suffixes _
    (PvsNP.Units.m2_p_compl _
      (PvsNP.Units.m2_p_some_prefix _
        (PvsNP.Units.m2_p_compl L hL)))
