import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_len_square_p
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime

namespace PvsNP.Units.tl_lang_len_two_squares_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private def firstSquare (u : List Bool) : List Bool := mulU u u
private def probe (p : List Bool × List Bool) := (firstSquare p.2, p.1)

private theorem probe_time :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair probe := by
  have squareTime : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString firstSquare :=
    cpt_mulU2 cpt_id cpt_id
  have pairTime := PvsNP.Units.m2_prod_map_polytime firstSquare id squareTime
    PvsNP.Units.m2_prod_map_polytime.ident
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.m2_prod_map_polytime.swap pairTime

private def check (square : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide ((probe p).1.length ≤ p.1.length) && square (p.1.drop (probe p).1.length)

private theorem check_time (square : List Bool → Bool)
    (hs : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer square) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (check square) := by
  have bound := PvsNP.Units.m2_polytime_comp _ _ _ _ _ probe_time PvsNP.Units.m2_len_le_polytime
  have tail := PvsNP.Units.m2_polytime_comp _ _ _ _ _ probe_time PvsNP.Units.m2_take_drop_length_polytime.2
  have rest := PvsNP.Units.m2_polytime_comp _ _ _ _ _ tail hs
  exact PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ bound rest

end PvsNP.Units.tl_lang_len_two_squares_p

open PvsNP.Units.tl_lang_len_two_squares_p in
theorem PvsNP.Units.tl_lang_len_two_squares_p :
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = x.length} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨square, cost, spec⟩ := PvsNP.Units.tl_lang_len_square_p
  let decideSum := fun x : List Bool =>
    (List.range (x.length + 1)).any (fun a => check square (x, List.replicate a true))
  refine ⟨decideSum, PvsNP.Units.m2_bounded_unary_search_polytime _ (check_time square cost), ?_⟩
  intro x
  have checks (a : ℕ) : check square (x, List.replicate a true) = true ↔
      a ^ 2 ≤ x.length ∧ ∃ b : ℕ, x.length - a ^ 2 = b ^ 2 := by
    have size : (probe (x, List.replicate a true)).1.length = a ^ 2 := by
      simp [probe, firstSquare, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.un, pow_two]
    change (decide ((probe (x, List.replicate a true)).1.length ≤ x.length) && square (x.drop (probe (x, List.replicate a true)).1.length)) = true ↔ _
    rw [size, Bool.and_eq_true, decide_eq_true_eq]
    have h := spec (x.drop (a ^ 2))
    change (∃ b : ℕ, (x.drop (a ^ 2)).length = b ^ 2) ↔ square (x.drop (a ^ 2)) = true at h
    rw [← h, List.length_drop]
  change (∃ a b : ℕ, a ^ 2 + b ^ 2 = x.length) ↔ (List.range (x.length + 1)).any _ = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, b, total⟩
    have ha : a ≤ a ^ 2 := by
      cases a with
      | zero => simp
      | succ k => simp [sq]
    exact ⟨a, List.mem_range.mpr (by omega), (checks a).2 ⟨by omega, b, by omega⟩⟩
  · rintro ⟨a, _, valid⟩
    obtain ⟨bound, b, rest⟩ := (checks a).1 valid
    exact ⟨a, b, by omega⟩
