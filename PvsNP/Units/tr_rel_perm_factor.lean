import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_perm
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tr_rel_perm_factor

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private abbrev Word := List Bool
private abbrev Inputs := Word × Word

/-- The input to one probe is a packed (needle, text) and a unary starting index. -/
private def probe (q : Inputs) : Inputs :=
  let p := unpairB q.1
  (((p.2.drop q.2.length).take p.1.length), p.1)

private theorem probe_time :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair probe := by
  have left := m2_pair_split_polytime.1
  have right := m2_pair_split_polytime.2.1
  have unpack := m2_polytime_comp _ _ _ _ _ left m2_tm_self_delimiting_pair.2
  have patternTime := m2_polytime_comp _ _ _ _ _ unpack left
  have textTime := m2_polytime_comp _ _ _ _ _ unpack right
  have offsetAndText := m2_tm_pair_fork_polytime _ _ right textTime
  have tailTime := m2_polytime_comp _ _ _ _ _ offsetAndText m2_take_drop_length_polytime.2
  have lengthAndTail := m2_tm_pair_fork_polytime _ _ patternTime tailTime
  have sliceTime := m2_polytime_comp _ _ _ _ _ lengthAndTail m2_take_drop_length_polytime.1
  exact m2_tm_pair_fork_polytime _ _ sliceTime patternTime

private theorem slice_infix (text : Word) (i k : ℕ) :
    (text.drop i).take k <:+: text := by
  refine ⟨text.take i, (text.drop i).drop k, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

end PvsNP.Units.tr_rel_perm_factor

open PvsNP.Units.tr_rel_perm_factor PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
/-- Only the starting index must be searched: a permutation fixes the length of a factor. -/
theorem PvsNP.Units.tr_rel_perm_factor :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (∃ y : List Bool, y <:+: p.2 ∧ List.Perm y p.1) ↔ f p = true := by
  obtain ⟨perm, cost, correct⟩ := tr_rel_perm
  let test := fun q : List Bool × List Bool => perm (probe q)
  have testTime : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer test :=
    m2_polytime_comp _ _ _ _ _ probe_time cost
  let search := fun s : List Bool =>
    (List.range (s.length + 1)).any (fun i => test (s, List.replicate i true))
  have searchTime := m2_bounded_unary_search_polytime test testTime
  refine ⟨fun p => search (pairB p.1 p.2),
    m2_polytime_comp _ _ _ _ _ m2_tm_self_delimiting_pair.1 searchTime, ?_⟩
  rintro ⟨u, text⟩
  have atIndex (i : ℕ) : test (pairB u text, List.replicate i true) = true ↔
      ((text.drop i).take u.length).Perm u := by
    change perm (probe _) = true ↔ _
    rw [← correct]
    simp [probe, unpairB_pairB]
  change (∃ y : List Bool, y <:+: text ∧ y.Perm u) ↔ (List.range (_ + 1)).any _ = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, ⟨pre, post, h⟩, permutes⟩
    have preBound : pre.length ≤ text.length := by
      rw [← h]
      simp only [List.length_append]
      omega
    refine ⟨pre.length, List.mem_range.mpr ?_, (atIndex _).2 ?_⟩
    · change pre.length < (pairB u text).length + 1
      rw [pairB_length]
      omega
    · rw [← h, List.append_assoc, List.drop_left, ← permutes.length_eq, List.take_left]
      exact permutes
  · rintro ⟨i, _, success⟩
    exact ⟨_, slice_infix text i u.length, (atIndex i).1 success⟩
