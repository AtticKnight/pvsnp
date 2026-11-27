import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_p_finite

namespace PvsNP.Units.tr_rel_hamming_le

def cntStep (q : Fin 3) (b : Bool) : Fin 3 :=
  if b then ⟨min (q.1 + 1) 2, by omega⟩ else q

def cntAcc (q : Fin 3) : Bool :=
  decide (q.1 ≤ 1)

theorem cntStep_foldl (z : List Bool) :
    ∀ q : Fin 3, (z.foldl cntStep q).1 = min (q.1 + z.count true) 2 := by
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

theorem cntAcc_eq (z : List Bool) :
    cntAcc (z.foldl cntStep ⟨0, by decide⟩) = decide (z.count true ≤ 1) := by
  unfold cntAcc
  rw [cntStep_foldl]
  simp only [Nat.zero_add]
  by_cases h : z.count true ≤ 1
  · have h1 : min (z.count true) 2 ≤ 1 := by omega
    simp [h, h1]
  · have h1 : ¬ (min (z.count true) 2 ≤ 1) := by omega
    simp [h, h1]

theorem cpt_count_le_one :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun z : List Bool => decide (z.count true ≤ 1)) := by
  have h := PvsNP.Units.m2_p_finite.dfa_comp (Fin 3) cntStep ⟨0, by decide⟩ cntAcc
  have heq : (fun z : List Bool => cntAcc (z.foldl cntStep ⟨0, by decide⟩)) =
      (fun z : List Bool => decide (z.count true ≤ 1)) := funext cntAcc_eq
  rw [heq] at h
  exact h

end PvsNP.Units.tr_rel_hamming_le

/-- Whether two strings of one length differ in at most 1 place is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_hamming_le :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧ (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ 1) ↔
          f p = true := by
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
        decide ((List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ 1)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_zip_bne_polytime
      PvsNP.Units.tr_rel_hamming_le.cpt_count_le_one
  have heqLen := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ h1 h2
  have hall := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ heqLen h3
  refine ⟨_, hall, fun p => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨⟨by omega, by omega⟩, hc⟩
  · rintro ⟨⟨hl1, hl2⟩, hc⟩
    exact ⟨by omega, hc⟩
