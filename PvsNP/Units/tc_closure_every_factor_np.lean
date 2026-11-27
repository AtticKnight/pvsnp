import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_all_prefixes
import PvsNP.Units.tc_closure_every_suffix_np

/-- Every factor is a prefix of a suffix, and all such prefixes are factors. -/
theorem PvsNP.Units.tc_closure_every_factor_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  let prefixes : Language Bool := {z | ∀ w : List Bool, w <+: z → w ∈ L}
  have hp : prefixes ∈ PvsNP.NP := PvsNP.Units.m2_np_all_prefixes L hL
  have hs := PvsNP.Units.tc_closure_every_suffix_np prefixes hp
  have same : ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) =
      {x : List Bool | ∀ z : List Bool, z <:+ x → z ∈ prefixes} := by
    ext x
    constructor
    · intro hall z hz w hw
      obtain ⟨left, rfl⟩ := hz
      obtain ⟨right, rfl⟩ := hw
      exact hall w ⟨left, right, by simp [List.append_assoc]⟩
    · intro hall w hw
      obtain ⟨left, right, rfl⟩ := hw
      have htail := hall (w ++ right) ⟨left, by simp [List.append_assoc]⟩
      exact htail w ⟨right, rfl⟩
  rw [same]
  exact hs
