import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_hamming_unary
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_tm_pair_swap_polytime

open PvsNP.Units

/-- Compare the unary mismatch count with a fixed unary threshold. A separate
two-way length check accounts for zip truncating its longer input. -/
theorem PvsNP.Units.tr_rel_hamming_le_all :
    ∀ d : ℕ, ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool, (p.1.length = p.2.length ∧
        (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d) ↔ f p = true := by
  intro d
  have withLimit := m2_pair_build_polytime _ _ m2_pair_build_polytime.cpt_id
    (m2_const_polytime (List.replicate d true))
  have limit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun w : List Bool => decide (w.length ≤ d)) := by
    simpa only [Function.comp_def, List.length_replicate] using
      (m2_polytime_comp _ _ _ _ _ withLimit m2_len_le_polytime)
  have mismatches : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide ((List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d)) := by
    simpa only [Function.comp_def, List.length_replicate] using
      (m2_polytime_comp _ _ _ _ _ m2_tm_hamming_unary limit)
  have opposite : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    m2_polytime_comp _ _ _ _ _ m2_tm_pair_swap_polytime m2_len_le_polytime
  have equalLength := m2_tm_pair_bool_combine (fun a b => a && b) _ _ m2_len_le_polytime opposite
  have check := m2_tm_pair_bool_combine (fun a b => a && b) _ _ equalLength mismatches
  refine ⟨_, check, fun p => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hBound⟩
    exact ⟨⟨h.le, h.ge⟩, hBound⟩
  · rintro ⟨⟨hl, hr⟩, hBound⟩
    exact ⟨Nat.le_antisymm hl hr, hBound⟩
