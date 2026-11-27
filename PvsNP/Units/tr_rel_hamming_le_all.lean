import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_p_finite

namespace PvsNP.Units.tr_rel_hamming_le_all

/-- One step of the capped counter: on `true` the count rises by one,
capped at `d + 1` (the first value that already refutes `count ≤ d`). -/
def cntStep (d : ℕ) (q : Fin (d + 2)) (b : Bool) : Fin (d + 2) :=
  if b then ⟨min (q.1 + 1) (d + 1), by omega⟩ else q

/-- Accept exactly when the capped count never passed `d`. -/
def cntAcc (d : ℕ) (q : Fin (d + 2)) : Bool :=
  decide (q.1 ≤ d)

theorem cntStep_foldl (d : ℕ) (z : List Bool) :
    ∀ q : Fin (d + 2), (z.foldl (cntStep d) q).1 = min (q.1 + z.count true) (d + 1) := by
  induction z with
  | nil =>
    intro q
    simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
    have hq := q.2
    omega
  | cons b t ih =>
    intro q
    rw [List.foldl_cons, ih]
    cases b with
    | false =>
      simp only [cntStep, Bool.false_eq_true, ↓reduceIte, List.count_cons_of_ne (by decide : false ≠ true)]
    | true =>
      simp only [cntStep, ↓reduceIte, List.count_cons_self]
      omega

theorem cntAcc_eq (d : ℕ) (z : List Bool) :
    cntAcc d (z.foldl (cntStep d) ⟨0, by omega⟩) = decide (z.count true ≤ d) := by
  unfold cntAcc
  rw [cntStep_foldl]
  simp only [Nat.zero_add]
  by_cases h : z.count true ≤ d
  · have h1 : min (z.count true) (d + 1) ≤ d := by omega
    simp [h, h1]
  · have h1 : ¬ (min (z.count true) (d + 1) ≤ d) := by omega
    simp [h, h1]

/-- Counting the `true`s of one string and comparing against `d` is
polynomial-time (TM2): a finite automaton with `d + 2` states. -/
theorem cpt_count_le (d : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun z : List Bool => decide (z.count true ≤ d)) := by
  have h := PvsNP.Units.m2_p_finite.dfa_comp (Fin (d + 2)) (cntStep d) ⟨0, by omega⟩ (cntAcc d)
  have heq : (fun z : List Bool => cntAcc d (z.foldl (cntStep d) ⟨0, by omega⟩)) =
      (fun z : List Bool => decide (z.count true ≤ d)) := funext (cntAcc_eq d)
  rw [heq] at h
  exact h

end PvsNP.Units.tr_rel_hamming_le_all

/-- Whether two strings of one length differ in at most `d` places is
decidable in polynomial time (TM2), for every `d`: check the lengths
both ways, zip the strings with `≠`, and count the differences with a
capped counter. -/
theorem PvsNP.Units.tr_rel_hamming_le_all :
    ∀ d : ℕ, ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧ (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d) ↔
          f p = true := by
  intro d
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) :=
    PvsNP.Units.m2_len_le_polytime
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_tm_pair_swap_polytime.swap
      PvsNP.Units.m2_len_le_polytime
  have h3 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide ((List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_zip_bne_polytime
      (PvsNP.Units.tr_rel_hamming_le_all.cpt_count_le d)
  have heqLen := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ h1 h2
  have hall := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ heqLen h3
  refine ⟨_, hall, fun p => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨⟨by omega, by omega⟩, hc⟩
  · rintro ⟨⟨hl1, hl2⟩, hc⟩
    exact ⟨by omega, hc⟩
