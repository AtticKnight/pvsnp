import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_down_closed

theorem PvsNP.Units.m2_p_eq_np_iff_finite_nphard : PvsNP.P = PvsNP.NP ↔ ∃ S : Finset (List Bool), PvsNP.NPHard ({x : List Bool | x ∈ S} : Language Bool) := by
  constructor
  · intro hEq
    refine ⟨{[]}, ?_⟩
    intro L' hL'
    have hP : L' ∈ PvsNP.P := hEq ▸ hL'
    obtain ⟨f, hf, hiff⟩ := hP
    refine ⟨fun x => if f x = true then [] else [true], ?_, ?_⟩
    · exact PvsNP.Units.m2_ite_polytime f (fun _ => []) (fun _ => [true]) hf (PvsNP.Units.m2_const_polytime []) (PvsNP.Units.m2_const_polytime [true])
    · intro x
      constructor
      · intro hx
        have : f x = true := (hiff x).mp hx
        show (if f x = true then ([] : List Bool) else [true]) ∈ _
        rw [if_pos this]
        exact Finset.mem_singleton_self _
      · intro hx
        by_cases hfx : f x = true
        · exact (hiff x).mpr hfx
        · have hx' : (if f x = true then ([] : List Bool) else [true]) ∈
              ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool) := hx
          rw [if_neg hfx] at hx'
          have hcontra := Finset.mem_singleton.mp hx'
          exact absurd hcontra (by decide)
  · rintro ⟨S, hHard⟩
    apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
    intro L' hL'
    exact PvsNP.Units.m2_p_down_closed L' _ (hHard L' hL') (PvsNP.Units.m2_p_finite S)
