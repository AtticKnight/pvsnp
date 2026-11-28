import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_pshuffle_p
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_p_subset_np_conp

open PvsNP.Units.tc_closure_pshuffle_p in
/-- Separate the alternating input tracks, and use parity to reject a last unpaired bit. -/
theorem PvsNP.Units.tc_closure_pshuffle_np :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧
        x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) ∈ PvsNP.NP := by
  intro L R hL hR
  let parity : Language Bool := {s | even s}
  let track (b : Bool) (A : Language Bool) : Language Bool := {s | pick b s ∈ A}
  have regular : parity ∈ PvsNP.P := m2_dfa_in_p Bool (fun state _ => !state) true id
  have preimage (b : Bool) (A : Language Bool) (hA : A ∈ PvsNP.NP) :
      track b A ∈ PvsNP.NP :=
    m2_np_down_closed _ A ⟨pick b, poly b, fun _ => Iff.rfl⟩ hA
  have both := m2_np_inter _ _ (preimage true L hL) (preimage false R hR)
  have accepted := m2_np_inter parity _ (m2_p_subset_np_conp regular).1 both
  suffices same : ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧
      x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L ∧ v ∈ R} : Language Bool) =
      parity ⊓ (track true L ⊓ track false R) by
    simpa only [same] using accepted
  ext s
  change (∃ u v : List Bool, u.length = v.length ∧ s = (List.zipWith (fun a b => [a,b]) u v).flatten ∧
    u ∈ L ∧ v ∈ R) ↔ even s ∧ pick true s ∈ L ∧ pick false s ∈ R
  constructor
  · rintro ⟨u, v, lengths, rfl, left, right⟩
    obtain ⟨shape, hu, hv⟩ := recover u v lengths
    exact ⟨shape, hu.symm ▸ left, hv.symm ▸ right⟩
  · rintro ⟨shape, left, right⟩
    obtain ⟨lengths, rebuild⟩ := unzip s shape
    exact ⟨_, _, lengths, rebuild, left, right⟩
