import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_p_finite
import PvsNP.Units.tf_fun_interleave

namespace PvsNP.Units.tr_rel_bit_le

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem pair_bool_combine (op : Bool → Bool → Bool) (c d : List Bool × List Bool → Bool)
    (hc : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer c)
    (hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer d) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => op (c p) (d p)) := by
  have hC : ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodeAnswer
      (fun s : List Bool => c (unpairB s)) :=
    cpt_comp cpt_unpairB hc
  have hD : ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodeAnswer
      (fun s : List Bool => d (unpairB s)) :=
    cpt_comp cpt_unpairB hd
  have hB := PvsNP.Units.m2_bool_combine_polytime op
    (fun s : List Bool => c (unpairB s)) (fun s : List Bool => d (unpairB s)) hC hD
  have h2 : ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        op (c (unpairB (pairB p.1 p.2))) (d (unpairB (pairB p.1 p.2)))) :=
    cpt_comp cpt_pairB hB
  have e : (fun p : List Bool × List Bool =>
        op (c (unpairB (pairB p.1 p.2))) (d (unpairB (pairB p.1 p.2))))
      = (fun p : List Bool × List Bool => op (c p) (d p)) := by
    funext p
    rw [unpairB_pairB]
  rwa [e] at h2

inductive St
  | first
  | sawTrue
  | skip
  | dead
  deriving DecidableEq

instance : Fintype St :=
  ⟨{St.first, St.sawTrue, St.skip, St.dead}, by intro x; cases x <;> simp⟩

def step : St → Bool → St
  | St.first, true => St.sawTrue
  | St.first, false => St.skip
  | St.sawTrue, true => St.first
  | St.sawTrue, false => St.dead
  | St.skip, _ => St.first
  | St.dead, _ => St.dead

def acc : St → Bool
  | St.dead => false
  | _ => true

theorem foldl_dead (l : List Bool) : l.foldl step St.dead = St.dead := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [List.foldl_cons]; exact ih

theorem key (x : List Bool) :
    ∀ y : List Bool, x.length = y.length →
      ((∀ i : ℕ, x[i]? = some true → y[i]? = some true) ↔
        acc (((List.zipWith (fun a b => [a, b]) x y).flatten).foldl step St.first) = true) := by
  induction x with
  | nil => intro y _; simp [acc]
  | cons a x ih =>
    intro y hl
    cases y with
    | nil => simp at hl
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [List.zipWith_cons_cons, List.flatten_cons, List.foldl_append]
      cases a <;> cases b
      · simp only [List.foldl_cons, List.foldl_nil, step]
        rw [← ih y hl]
        constructor
        · intro h i hi; exact h (i + 1) (by simpa using hi)
        · intro h i hi
          cases i with
          | zero => simp at hi
          | succ i => simpa using h i (by simpa using hi)
      · simp only [List.foldl_cons, List.foldl_nil, step]
        rw [← ih y hl]
        constructor
        · intro h i hi; exact h (i + 1) (by simpa using hi)
        · intro h i hi
          cases i with
          | zero => simp
          | succ i => simpa using h i (by simpa using hi)
      · simp only [List.foldl_cons, List.foldl_nil, step, foldl_dead, acc]
        simp only [Bool.false_eq_true, iff_false, not_forall]
        exact ⟨0, by simp, by simp⟩
      · simp only [List.foldl_cons, List.foldl_nil, step]
        rw [← ih y hl]
        constructor
        · intro h i hi; exact h (i + 1) (by simpa using hi)
        · intro h i hi
          cases i with
          | zero => simp
          | succ i => simpa using h i (by simpa using hi)

theorem interleave_eq (x y : List Bool) (hl : x.length = y.length) :
    (List.zipWith (fun a b => [a, b]) ((x ++ y).take ((x ++ y).length / 2))
      ((x ++ y).drop ((x ++ y).length / 2))).flatten =
      (List.zipWith (fun a b => [a, b]) x y).flatten := by
  have h : (x ++ y).length / 2 = x.length := by
    rw [List.length_append]; omega
  rw [h, List.take_left' rfl, List.drop_left' rfl]

theorem cpt_scan :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        acc (((List.zipWith (fun a b => [a, b]) ((p.1 ++ p.2).take ((p.1 ++ p.2).length / 2))
          ((p.1 ++ p.2).drop ((p.1 ++ p.2).length / 2))).flatten).foldl step St.first)) := by
  have hd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => acc (x.foldl step St.first)) :=
    PvsNP.Units.m2_p_finite.dfa_comp St step St.first acc
  have hi : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => acc (((List.zipWith (fun a b => [a, b]) (x.take (x.length / 2))
          (x.drop (x.length / 2))).flatten).foldl step St.first)) :=
    cpt_comp (g := fun x : List Bool => acc (x.foldl step St.first))
      PvsNP.Units.tf_fun_interleave hd
  have ha : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ p.2) :=
    PvsNP.Units.m2_pair_split_polytime.2.2
  exact cpt_comp (f := fun p : List Bool × List Bool => p.1 ++ p.2)
    (g := fun x : List Bool => acc (((List.zipWith (fun a b => [a, b]) (x.take (x.length / 2))
          (x.drop (x.length / 2))).flatten).foldl step St.first)) ha hi

end PvsNP.Units.tr_rel_bit_le

/-- Whether one string's trues are among another's is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_bit_le :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧ ∀ i : ℕ, p.1[i]? = some true → p.2[i]? = some true) ↔
          f p = true := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) :=
    PvsNP.Units.m2_len_le_polytime
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_swap
      PvsNP.Units.m2_len_le_polytime
  have heqLen := PvsNP.Units.tr_rel_bit_le.pair_bool_combine (fun a b => a && b) _ _ h1 h2
  have hall := PvsNP.Units.tr_rel_bit_le.pair_bool_combine (fun a b => a && b) _ _ heqLen
    PvsNP.Units.tr_rel_bit_le.cpt_scan
  refine ⟨_, hall, fun p => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hc⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [PvsNP.Units.tr_rel_bit_le.interleave_eq p.1 p.2 hl]
    exact (PvsNP.Units.tr_rel_bit_le.key p.1 p.2 hl).1 hc
  · rintro ⟨⟨hl1, hl2⟩, hc⟩
    have hl : p.1.length = p.2.length := by omega
    rw [PvsNP.Units.tr_rel_bit_le.interleave_eq p.1 p.2 hl] at hc
    exact ⟨hl, (PvsNP.Units.tr_rel_bit_le.key p.1 p.2 hl).2 hc⟩
