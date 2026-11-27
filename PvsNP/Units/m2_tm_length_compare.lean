import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_length_compare

theorem hle : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) :=
  PvsNP.Units.m2_len_le_polytime

theorem hge : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.2, p.1))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    PvsNP.Units.m2_tm_pair_swap_polytime hle
  exact h

theorem heq : (fun p : List Bool × List Bool => decide (p.1.length = p.2.length)) =
    (fun p : List Bool × List Bool =>
      (fun a b : Bool => a && b) (decide (p.1.length ≤ p.2.length)) (decide (p.2.length ≤ p.1.length))) := by
  funext p
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩

theorem hlt : (fun p : List Bool × List Bool => decide (p.1.length < p.2.length)) =
    (fun p : List Bool × List Bool =>
      (fun a _ : Bool => !a) (decide (p.2.length ≤ p.1.length)) (decide (p.2.length ≤ p.1.length))) := by
  funext p
  apply Bool.eq_iff_iff.2
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  exact ⟨fun h => by omega, fun h => by omega⟩

end PvsNP.Units.m2_tm_length_compare

theorem PvsNP.Units.m2_tm_length_compare :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1.length = p.2.length)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1.length < p.2.length)) := by
  constructor
  · rw [PvsNP.Units.m2_tm_length_compare.heq]
    exact PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b) _ _
      PvsNP.Units.m2_tm_length_compare.hle PvsNP.Units.m2_tm_length_compare.hge
  · rw [PvsNP.Units.m2_tm_length_compare.hlt]
    exact PvsNP.Units.m2_tm_pair_bool_combine (fun a _ : Bool => !a) _ _
      PvsNP.Units.m2_tm_length_compare.hge PvsNP.Units.m2_tm_length_compare.hge
