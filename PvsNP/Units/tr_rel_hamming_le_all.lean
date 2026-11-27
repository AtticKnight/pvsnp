import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_hamming_unary
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.tr_rel_hamming_le_all :
    ∀ d : ℕ, ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧ (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d) ↔
          f p = true := by
  intro d
  have sized := m2_pair_build_polytime (fun x : List Bool => x)
    (fun _ : List Bool => List.replicate d true) m2_pair_build_polytime.cpt_id
    (m2_const_polytime (List.replicate d true))
  have bound := m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x : List Bool => (x, List.replicate d true))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) sized m2_len_le_polytime
  have count := m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => List.replicate ((List.zipWith (fun a b => a != b) p.1 p.2).count true) true)
    (fun x : List Bool => decide (x.length ≤ d)) m2_tm_hamming_unary
    (by simpa only [Function.comp_apply, List.length_replicate] using bound)
  have reversed : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    fr_ladner.PEqualNP.Library.Machines.cpt_comp m2_tm_pair_swap_polytime.swap m2_len_le_polytime
  have same := m2_tm_pair_bool_combine (· && ·) _ _ m2_len_le_polytime reversed
  have within : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide ((List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d)) := by
    simpa only [Function.comp_apply, List.length_replicate] using count
  refine ⟨_, m2_tm_pair_bool_combine (· && ·) _ _ same within, ?_⟩
  intro p
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
