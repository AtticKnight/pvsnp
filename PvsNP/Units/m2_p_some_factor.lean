import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_some_prefix
import PvsNP.Units.m2_p_all_suffixes
import PvsNP.Units.m2_p_compl

/-- P is closed under "some factor is in L" (TM2): a factor is a prefix of a suffix,
so the set is the complement of "every suffix lies in the complement of the
some-prefix language", using the settled units m2_p_some_prefix, m2_p_all_suffixes
and m2_p_compl. -/
theorem PvsNP.Units.m2_p_some_factor :
    ∀ L ∈ PvsNP.P, ({x : List Bool | ∃ y : List Bool, y <:+: x ∧ y ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  have h1 : ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_some_prefix L hL
  have h1c : ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool)ᶜ ∈ PvsNP.P :=
    PvsNP.Units.m2_p_compl _ h1
  have hA : ({x : List Bool | ∀ s : List Bool, s <:+ x →
      s ∈ ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool)ᶜ} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_all_suffixes _ h1c
  have hSeq : ({x : List Bool | ∃ y : List Bool, y <:+: x ∧ y ∈ L} : Language Bool) =
      ({x : List Bool | ∀ s : List Bool, s <:+ x →
        s ∈ ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool)ᶜ} : Language Bool)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro ⟨y, hy, hyL⟩ hA'
      obtain ⟨a, b, hab⟩ := hy
      exact hA' (y ++ b) ⟨a, by rw [← List.append_assoc]; exact hab⟩ ⟨y, ⟨b, rfl⟩, hyL⟩
    · intro h
      rw [not_forall] at h
      obtain ⟨s, hs⟩ := h
      rw [not_imp] at hs
      obtain ⟨hsx, hsnot⟩ := hs
      have hex : ∃ y : List Bool, y <+: s ∧ y ∈ L := not_not.mp hsnot
      obtain ⟨y, hys, hyL⟩ := hex
      obtain ⟨a, ha⟩ := hsx
      obtain ⟨b, hb⟩ := hys
      exact ⟨y, ⟨a, b, by rw [List.append_assoc, hb]; exact ha⟩, hyL⟩
  rw [hSeq]
  exact PvsNP.Units.m2_p_compl _ hA
