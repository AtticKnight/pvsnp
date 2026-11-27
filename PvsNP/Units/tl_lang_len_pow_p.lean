import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_mul_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Every possible cube root is bounded by the input length. Check each unary candidate. -/
theorem PvsNP.Units.tl_lang_len_pow_p :
    ({x : List Bool | ∃ k : ℕ, x.length = k ^ 3} : Language Bool) ∈ PvsNP.P := by
  let V : List Bool × List Bool → Bool := fun p => decide (p.1.length = p.2.length ^ 3)
  have fstP : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) := cpt_fst
  have sndP : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2) := cpt_snd
  have unary : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) := by
    simpa only [Nat.div_one] using PvsNP.Units.m2_tm_unary_div_const 1
  have square := PvsNP.Units.m2_pair_build_polytime.cpt_comp
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ sndP sndP) PvsNP.Units.m2_mul_polytime
  have cube := PvsNP.Units.m2_pair_build_polytime.cpt_comp
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ square sndP) PvsNP.Units.m2_mul_polytime
  have compV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V := by
    have h := PvsNP.Units.m2_pair_build_polytime.cpt_comp
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ (PvsNP.Units.m2_pair_build_polytime.cpt_comp fstP unary) cube)
      PvsNP.Units.m2_eq_polytime
    convert h using 1
    funext p
    simp [V, pow_succ]
  refine ⟨_, PvsNP.Units.m2_bounded_unary_search_polytime V compV, fun x => ?_⟩
  change (∃ k : ℕ, x.length = k ^ 3) ↔ _
  simp only [List.any_eq_true, List.mem_range, V, List.length_replicate, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    have lower : k ≤ k ^ 3 := by
      by_cases hz : k = 0
      · simp [hz]
      · have hpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hz
        calc
          k = k * 1 := (Nat.mul_one k).symm
          _ ≤ k * k^2 := Nat.mul_le_mul_left k (by positivity)
          _ = k^3 := by ring
    omega
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩
