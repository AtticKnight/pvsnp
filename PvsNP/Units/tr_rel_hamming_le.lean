import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_pair_build_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Compare lengths in both directions, and compare the unary count of pointwise mismatches with one. -/
theorem PvsNP.Units.tr_rel_hamming_le :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (p.1.length = p.2.length ∧ (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ 1) ↔ f p = true := by
  have equalLength := PvsNP.Units.m2_tm_pair_bool_combine (fun x y => x && y) _ _
    PvsNP.Units.m2_len_le_polytime
    (PvsNP.Units.m2_pair_build_polytime.cpt_comp PvsNP.Units.m2_tm_pair_swap_polytime
      PvsNP.Units.m2_len_le_polytime)
  have count := PvsNP.Units.m2_pair_build_polytime.cpt_comp PvsNP.Units.m2_zip_bne_polytime
    PvsNP.Units.tf_fun_ones_unary
  have paired := PvsNP.Units.m2_pair_build_polytime _ _ cpt_id (cpt_const [true])
  have atMostOne := PvsNP.Units.m2_pair_build_polytime.cpt_comp
    (PvsNP.Units.m2_pair_build_polytime.cpt_comp count paired) PvsNP.Units.m2_len_le_polytime
  refine ⟨_, PvsNP.Units.m2_tm_pair_bool_combine (fun x y => x && y) _ _ equalLength atMostOne, ?_⟩
  intro p
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_replicate, List.length_cons,
    List.length_nil]
  omega
