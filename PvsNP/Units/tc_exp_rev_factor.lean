import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_padded_test_exp
import PvsNP.Units.m2_exp_iff_padded_p
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.tc_closure_del_one_p

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_rev_factor

/-- Decidable within `2 ^ (n ^ K) + K` steps. -/
def IsExpK (K : ℕ) (L : Language Bool) : Prop :=
  ∃ (f : List Bool → Bool)
    (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
    (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ K) + K

/-- The padding of `x` at level `K`. -/
def padOf (K : ℕ) (x : List Bool) : List Bool :=
  List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x

/-- The padded language. -/
def PadSet (K : ℕ) (S : Language Bool) : Language Bool :=
  {s | ∃ x : List Bool, x ∈ S ∧ s = padOf K x}

/-- `x` with one factor reversed lands in `L`. -/
def RevFac (L : Language Bool) : Language Bool :=
  {x | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L}

theorem bound_mono (k K n : ℕ) (hK : 1 ≤ K) (hk : k ≤ K) :
    2 ^ (n ^ k) + k ≤ 2 ^ (n ^ K) + K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : (0 : ℕ) ^ K = 0 := Nat.zero_pow (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h2]
      simp
      omega
    · have h1 : (0 : ℕ) ^ k = 0 := Nat.zero_pow hk0
      rw [h1, h2]
      simp
      omega
  · have h1 : n ^ k ≤ n ^ K := Nat.pow_le_pow_right hn hk
    have h2 : 2 ^ (n ^ k) ≤ 2 ^ (n ^ K) := Nat.pow_le_pow_right (by norm_num) h1
    omega

theorem expK_mono {k K : ℕ} {L : Language Bool} (h : IsExpK k L) (hk : k ≤ K) (hK : 1 ≤ K) :
    IsExpK K L := by
  obtain ⟨f, M, h1, h2⟩ := h
  exact ⟨f, M, h1, fun n => (h2 n).trans (bound_mono k K n hK hk)⟩

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : PvsNP.PolyTimeComputable ea eb f) (heq : ∀ x, f x = g x) :
    PvsNP.PolyTimeComputable ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

/-- Self-delimiting pair encoding (copied from the settled `tc_exp_rotate`). -/
def encPair (u v : List Bool) : List Bool :=
  List.replicate u.length true ++ false :: (u ++ v)

def decPair (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.takeWhile_cons, id_eq, ↓reduceIte, ih]

theorem dropWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.dropWhile_cons, id_eq, ↓reduceIte, ih]

theorem decPair_encPair (u v : List Bool) : decPair (encPair u v) = (u, v) := by
  simp only [decPair, encPair, takeWhile_rep_false, dropWhile_rep_false, List.tail_cons,
    List.length_replicate, List.take_left, List.drop_left]

theorem encPair_length (u v : List Bool) :
    (encPair u v).length = 2 * u.length + 1 + v.length := by
  simp only [encPair, List.length_append, List.length_replicate, List.length_cons]
  omega

def takeWhileTrue (s : List Bool) : List Bool := s.takeWhile id

theorem cpt_decPair :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair :=
  cpt_congr PvsNP.Units.m2_tm_self_delimiting_pair.2 (fun _ => by simp only [decPair])

theorem cpt_takeWhileTrue :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString takeWhileTrue :=
  cpt_congr
    (PvsNP.Units.m2_transducer_polytime Bool
      (fun q b => if q && b then (true, some true) else (false, none))
      (fun _ => none)
      (fun q l => if q then l.takeWhile id else [])
      (fun q => by cases q <;> rfl)
      (fun q b l => by cases q <;> cases b <;> rfl)
      true)
    (fun _ => rfl)

/-- Split `p.1` at position `p.2.length`. -/
def splitAt (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1.take p.2.length, p.1.drop p.2.length)

/-- Splitting at a unary position is polynomial-time: mark the position with
    `1 ^ |c| 0` in front of the string and read it back with `decPair`
    (same trick as `tc_closure_del_one_p.cpt_ins`). -/
theorem cpt_splitAt :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1.take p.2.length, p.1.drop p.2.length)) := by
  have h1 := PvsNP.Units.m2_tm_pair_swap_polytime
  have h2 := PvsNP.Units.m2_prod_map_polytime _ _
    PvsNP.Units.tc_closure_del_one_p.cpt_mark PvsNP.Units.tc_closure_del_one_p.cpt_id
  have h3 := PvsNP.Units.m2_pair_split_polytime.2.2
  have h4 := PvsNP.Units.tc_exp_rev_factor.cpt_decPair
  have c12 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 h2
  have c13 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c12 h3
  have c14 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c13 h4
  refine cpt_congr c14 (fun p => ?_)
  simp only [Function.comp_apply, PvsNP.Units.tc_exp_rev_factor.decPair,
    PvsNP.Units.tc_closure_del_one_p.takeWhile_mark,
    PvsNP.Units.tc_closure_del_one_p.dropWhile_mark, List.length_replicate,
    List.tail_cons]

/-- The candidate string for cut points `|ci|`, `|cj|`: `x` with the factor
    `x[|ci| .. |cj|)` reversed. -/
def cand (x ci cj : List Bool) : List Bool :=
  (splitAt (x, ci)).1 ++
    ((splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).1).reverse ++
    (splitAt (x, cj)).2

theorem cand_length (x ci cj : List Bool) :
    (cand x ci cj).length =
      min ci.length x.length + min (cj.length - ci.length) (x.length - ci.length) +
        (x.length - cj.length) := by
  simp only [cand, splitAt, List.length_append, List.length_take, List.length_drop,
    List.length_reverse]

/-- If the candidate has the same length as `x`, it comes from a genuine pair of
    cut points `i' ≤ j' ≤ |x|`: either `|ci| ≤ |cj|` already, or the length equation
    forces `|ci| > |x|` and `|cj| = |x|`, in which case the candidate is `x` itself. -/
theorem cand_witness (x ci cj : List Bool) (hlen : (cand x ci cj).length = x.length) :
    ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w = cand x ci cj := by
  by_cases hle : ci.length ≤ cj.length
  · refine ⟨(splitAt (x, ci)).1,
      (splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).1,
      (splitAt (x, cj)).2, ?_, rfl⟩
    have h1 : x = (splitAt (x, ci)).1 ++ (splitAt (x, ci)).2 := by
      simp only [splitAt, List.take_append_drop]
    have h2 : (splitAt (x, ci)).2 =
        (splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).1 ++
          (splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).2 := by
      simp only [splitAt, List.take_append_drop]
    have h3 : (splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).2 =
        (splitAt (x, cj)).2 := by
      simp only [splitAt, List.length_drop]
      rw [List.drop_drop, Nat.add_sub_cancel' hle]
    rw [List.append_assoc, ← h3, ← h2]
    exact h1
  · push_neg at hle
    have hlen2 := cand_length x ci cj
    rw [hlen] at hlen2
    have hi : x.length < ci.length := by
      by_contra hcon
      push_neg at hcon
      have hmin : min ci.length x.length = ci.length := Nat.min_eq_left hcon
      have h0 : min (cj.length - ci.length) (x.length - ci.length) = 0 := by
        have hsub : cj.length - ci.length = 0 :=
          Nat.sub_eq_zero_of_le (Nat.le_of_lt hle)
        omega
      omega
    have hj : x.length ≤ cj.length := by
      have h1 : min ci.length x.length = x.length := Nat.min_eq_right (Nat.le_of_lt hi)
      have h2 : min (cj.length - ci.length) (x.length - ci.length) = 0 := by
        have hsub : cj.length - ci.length = 0 :=
          Nat.sub_eq_zero_of_le (Nat.le_of_lt hle)
        omega
      omega
    refine ⟨x, [], [], by simp, ?_⟩
    have hA : (splitAt (x, ci)).1 = x := by
      simp only [splitAt, List.take_of_length_le (Nat.le_of_lt hi)]
    have hM : (splitAt ((splitAt (x, ci)).2, (splitAt (cj, ci)).2)).1 = [] := by
      have hdrop : x.drop ci.length = [] := by
        have hl : (x.drop ci.length).length = 0 := by
          simp only [List.length_drop]; omega
        exact List.length_eq_zero_iff.mp hl
      simp only [splitAt, hdrop, List.take_nil]
    have hC : (splitAt (x, cj)).2 = [] := by
      have hdrop : x.drop cj.length = [] := by
        have hl : (x.drop cj.length).length = 0 := by
          simp only [List.length_drop]; omega
        exact List.length_eq_zero_iff.mp hl
      simp only [splitAt, hdrop]
    simp only [cand, hA, hM, hC, List.reverse_nil, List.append_nil]

/-- Accessors for the packed test input `u = encPair (encPair (encPair padded x) ci) cj`. -/
def getT (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair u).1

theorem cpt_getT : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getT :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      PvsNP.Units.tc_exp_rev_factor.decPair (fun q : List Bool × List Bool => q.1)
      PvsNP.Units.tc_exp_rev_factor.cpt_decPair PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

def getCJ (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair u).2

theorem cpt_getCJ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getCJ :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      PvsNP.Units.tc_exp_rev_factor.decPair (fun q : List Bool × List Bool => q.2)
      PvsNP.Units.tc_exp_rev_factor.cpt_decPair PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getS0 (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair (getT u)).1

theorem cpt_getS0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getS0 := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getT u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodePair getT PvsNP.Units.tc_exp_rev_factor.decPair cpt_getT
        PvsNP.Units.tc_exp_rev_factor.cpt_decPair)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getT u))
      (fun q : List Bool × List Bool => q.1) h1 PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

def getCI (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair (getT u)).2

theorem cpt_getCI : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getCI := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getT u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodePair getT PvsNP.Units.tc_exp_rev_factor.decPair cpt_getT
        PvsNP.Units.tc_exp_rev_factor.cpt_decPair)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getT u))
      (fun q : List Bool × List Bool => q.2) h1 PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getPadS (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u)).1

theorem cpt_getPadS :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getPadS := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodePair getS0 PvsNP.Units.tc_exp_rev_factor.decPair cpt_getS0
        PvsNP.Units.tc_exp_rev_factor.cpt_decPair)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u))
      (fun q : List Bool × List Bool => q.1) h1 PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

def getX (u : List Bool) : List Bool :=
  (PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u)).2

theorem cpt_getX : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getX := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodePair getS0 PvsNP.Units.tc_exp_rev_factor.decPair cpt_getS0
        PvsNP.Units.tc_exp_rev_factor.cpt_decPair)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => PvsNP.Units.tc_exp_rev_factor.decPair (getS0 u))
      (fun q : List Bool × List Bool => q.2) h1 PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getPad (u : List Bool) : List Bool :=
  PvsNP.Units.tc_exp_rev_factor.takeWhileTrue (getPadS u)

theorem cpt_getPad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getPad :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeString getPadS PvsNP.Units.tc_exp_rev_factor.takeWhileTrue cpt_getPadS
      PvsNP.Units.tc_exp_rev_factor.cpt_takeWhileTrue)
    (fun _ => rfl)

def getA (u : List Bool) : List Bool :=
  (splitAt (getX u, getCI u)).1

theorem cpt_getA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getA := by
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getX u, getCI u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ cpt_getX cpt_getCI
  have hSplit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => splitAt (getX u, getCI u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodePair (fun u : List Bool => (getX u, getCI u)) splitAt hPair
        cpt_splitAt)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => splitAt (getX u, getCI u))
      (fun q : List Bool × List Bool => q.1) hSplit
      PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

def getD (u : List Bool) : List Bool :=
  (splitAt (getX u, getCI u)).2

theorem cpt_getD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getD := by
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getX u, getCI u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ cpt_getX cpt_getCI
  have hSplit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => splitAt (getX u, getCI u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodePair (fun u : List Bool => (getX u, getCI u)) splitAt hPair
        cpt_splitAt)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => splitAt (getX u, getCI u))
      (fun q : List Bool × List Bool => q.2) hSplit
      PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getDiff (u : List Bool) : List Bool :=
  (splitAt (getCJ u, getCI u)).2

theorem cpt_getDiff :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getDiff := by
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getCJ u, getCI u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ cpt_getCJ cpt_getCI
  have hSplit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => splitAt (getCJ u, getCI u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodePair (fun u : List Bool => (getCJ u, getCI u)) splitAt hPair
        cpt_splitAt)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => splitAt (getCJ u, getCI u))
      (fun q : List Bool × List Bool => q.2) hSplit
      PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getM (u : List Bool) : List Bool :=
  (splitAt (getD u, getDiff u)).1

theorem cpt_getM : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getM := by
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getD u, getDiff u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ cpt_getD cpt_getDiff
  have hSplit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => splitAt (getD u, getDiff u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodePair (fun u : List Bool => (getD u, getDiff u)) splitAt hPair
        cpt_splitAt)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => splitAt (getD u, getDiff u))
      (fun q : List Bool × List Bool => q.1) hSplit
      PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

def getC (u : List Bool) : List Bool :=
  (splitAt (getX u, getCJ u)).2

theorem cpt_getC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getC := by
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getX u, getCJ u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ cpt_getX cpt_getCJ
  have hSplit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => splitAt (getX u, getCJ u)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodePair (fun u : List Bool => (getX u, getCJ u)) splitAt hPair
        cpt_splitAt)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => splitAt (getX u, getCJ u))
      (fun q : List Bool × List Bool => q.2) hSplit
      PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

def getCand (u : List Bool) : List Bool :=
  getA u ++ (getM u).reverse ++ getC u

theorem cpt_getCand :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getCand := by
  have hRev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => (getM u).reverse) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodeString getM List.reverse cpt_getM
        PvsNP.Units.m2_reverse_polytime)
      (fun _ => rfl)
  have hApp1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => getA u ++ (getM u).reverse) := by
    have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun u : List Bool => (getA u, (getM u).reverse)) :=
      PvsNP.Units.m2_pair_build_polytime _ _ cpt_getA hRev
    exact cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodeString (fun u : List Bool => (getA u, (getM u).reverse))
        (fun q : List Bool × List Bool => q.1 ++ q.2) hPair
        PvsNP.Units.m2_pair_split_polytime.2.2)
      (fun _ => rfl)
  have hPair2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun u : List Bool => (getA u ++ (getM u).reverse, getC u)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ hApp1 cpt_getC
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString (fun u : List Bool => (getA u ++ (getM u).reverse, getC u))
      (fun q : List Bool × List Bool => q.1 ++ q.2) hPair2
      PvsNP.Units.m2_pair_split_polytime.2.2)
    (fun _ => rfl)

/-- Test one pair of cut points: does the padded candidate lie in `PadSet K L`? -/
def testOne (g : List Bool → Bool) (u : List Bool) : Bool :=
  g (getPad u ++ false :: getCand u)

theorem cpt_testOne (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (testOne g) := by
  have hCons : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => false :: getCand u) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
        PvsNP.encodeString getCand (fun x : List Bool => false :: x) cpt_getCand
        (PvsNP.Units.tc_closure_del_one_p.cpt_cons false))
      (fun _ => rfl)
  have hApp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => getPad u ++ false :: getCand u) := by
    have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun u : List Bool => (getPad u, false :: getCand u)) :=
      PvsNP.Units.m2_pair_build_polytime _ _ cpt_getPad hCons
    exact cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
        PvsNP.encodeString (fun u : List Bool => (getPad u, false :: getCand u))
        (fun q : List Bool × List Bool => q.1 ++ q.2) hPair
        PvsNP.Units.m2_pair_split_polytime.2.2)
      (fun _ => rfl)
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeAnswer (fun u : List Bool => getPad u ++ false :: getCand u) g hApp hg)
    (fun _ => rfl)

theorem cpt_encPairFn : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2) :=
  cpt_congr PvsNP.Units.m2_tm_self_delimiting_pair.1 (fun _ => rfl)

/-- The `j`-test as a function of a pair `(t, cj)`. -/
def Vj (g : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  testOne g (PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)

theorem cpt_Vj (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (Vj g) :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
      PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)
      (testOne g) cpt_encPairFn (cpt_testOne g hg))
    (fun _ => rfl)

/-- Bounded search over the second cut point `j`. -/
def searchJ (g : List Bool → Bool) (t : List Bool) : Bool :=
  (List.range (t.length + 1)).any (fun j => Vj g (t, List.replicate j true))

theorem cpt_searchJ (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (searchJ g) :=
  PvsNP.Units.m2_bounded_unary_search_polytime (Vj g) (cpt_Vj g hg)

/-- The `i`-test as a function of a pair `(s, ci)`. -/
def Vout (g : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  searchJ g (PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)

theorem cpt_Vout (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (Vout g) :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
      PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)
      (searchJ g) cpt_encPairFn (cpt_searchJ g hg))
    (fun _ => rfl)

/-- Bounded search over the first cut point `i`. -/
def searchI (g : List Bool → Bool) (s : List Bool) : Bool :=
  (List.range (s.length + 1)).any (fun i => Vout g (s, List.replicate i true))

theorem cpt_searchI (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (searchI g) :=
  PvsNP.Units.m2_bounded_unary_search_polytime (Vout g) (cpt_Vout g hg)

/-- The padded test fed to `m2_padded_test_exp`: search both cut points. -/
def hTest (g : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  searchI g (PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)

theorem cpt_hTest (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (hTest g) :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
      PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        PvsNP.Units.tc_exp_rev_factor.encPair p.1 p.2)
      (searchI g) cpt_encPairFn (cpt_searchI g hg))
    (fun _ => rfl)

theorem testOne_enc (g : List Bool → Bool) (padded x ci cj : List Bool) :
    testOne g (PvsNP.Units.tc_exp_rev_factor.encPair
        (PvsNP.Units.tc_exp_rev_factor.encPair
          (PvsNP.Units.tc_exp_rev_factor.encPair padded x) ci) cj) =
      g (PvsNP.Units.tc_exp_rev_factor.takeWhileTrue padded ++ false ::
        cand x ci cj) := by
  simp only [testOne, getPad, getCand, getA, getD, getDiff, getM, getC, getX, getPadS,
    getS0, getCI, getT, getCJ, cand, splitAt,
    PvsNP.Units.tc_exp_rev_factor.decPair_encPair]

theorem searchJ_true (g : List Bool → Bool) (t : List Bool) :
    searchJ g t = true ↔
      ∃ j : ℕ, j ≤ t.length ∧
        testOne g (PvsNP.Units.tc_exp_rev_factor.encPair t (List.replicate j true)) = true := by
  simp only [searchJ, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, hj, hV⟩
    exact ⟨j, by omega, hV⟩
  · rintro ⟨j, hj, hV⟩
    exact ⟨j, by omega, hV⟩

theorem searchI_true (g : List Bool → Bool) (s : List Bool) :
    searchI g s = true ↔
      ∃ i : ℕ, i ≤ s.length ∧
        searchJ g (PvsNP.Units.tc_exp_rev_factor.encPair s (List.replicate i true)) = true := by
  simp only [searchI, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hV⟩
    exact ⟨i, by omega, hV⟩
  · rintro ⟨i, hi, hV⟩
    exact ⟨i, by omega, hV⟩

theorem hTest_true (g : List Bool → Bool) (padded x : List Bool) :
    hTest g (padded, x) = true ↔
      ∃ i j : ℕ, i ≤ (PvsNP.Units.tc_exp_rev_factor.encPair padded x).length ∧
        j ≤ (PvsNP.Units.tc_exp_rev_factor.encPair
          (PvsNP.Units.tc_exp_rev_factor.encPair padded x)
          (List.replicate i true)).length ∧
        g (PvsNP.Units.tc_exp_rev_factor.takeWhileTrue padded ++ false ::
          cand x (List.replicate i true) (List.replicate j true)) = true := by
  simp only [hTest]
  rw [searchI_true]
  constructor
  · rintro ⟨i, hi, hJ⟩
    rw [searchJ_true] at hJ
    obtain ⟨j, hj, hT⟩ := hJ
    exact ⟨i, j, hi, hj, by rwa [testOne_enc] at hT⟩
  · rintro ⟨i, j, hi, hj, hG⟩
    refine ⟨i, hi, ?_⟩
    rw [searchJ_true]
    exact ⟨j, hj, by rwa [testOne_enc]⟩

end PvsNP.Units.tc_exp_rev_factor

/-- Exponential time is closed under reversing a block (TM2): pad `L` into P via
    `m2_upward_padding`, test every pair of cut points with the padded decider via
    two bounded unary searches, and convert back to EXP via `m2_padded_test_exp`.
    With `K ≥ 1` the pad-length equation forces every accepted candidate to have
    the same length as the input, so out-of-range cut points can never cheat. -/
theorem PvsNP.Units.tc_exp_rev_factor :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, htime⟩
  set K := max k 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hL' : PvsNP.Units.tc_exp_rev_factor.IsExpK K L :=
    PvsNP.Units.tc_exp_rev_factor.expK_mono ⟨f, M, hf, htime⟩ (le_max_left _ _) hK1
  obtain ⟨g, hg, hpad⟩ := PvsNP.Units.m2_upward_padding L K hL'
  obtain ⟨j, M', hM'⟩ := PvsNP.Units.m2_padded_test_exp K (fun x : List Bool => x)
    (fun x : List Bool => x) (PvsNP.Units.tc_exp_rev_factor.hTest g)
    PvsNP.Units.m2_prod_map_polytime.ident PvsNP.Units.m2_prod_map_polytime.ident
    (PvsNP.Units.tc_exp_rev_factor.cpt_hTest g hg)
  refine ⟨j, fun z => PvsNP.Units.tc_exp_rev_factor.hTest g
    (PvsNP.Units.tc_exp_rev_factor.padOf K z, z), M', fun x => ?_, hM'⟩
  show (∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L) ↔
    PvsNP.Units.tc_exp_rev_factor.hTest g
      (PvsNP.Units.tc_exp_rev_factor.padOf K x, x) = true
  rw [PvsNP.Units.tc_exp_rev_factor.hTest_true]
  constructor
  · rintro ⟨u, v, w, rfl, hyL⟩
    have htw : PvsNP.Units.tc_exp_rev_factor.takeWhileTrue
        (PvsNP.Units.tc_exp_rev_factor.padOf K (u ++ v ++ w)) =
        List.replicate (2 ^ ((u ++ v ++ w).length ^ K) + K) true := by
      show (List.replicate (2 ^ ((u ++ v ++ w).length ^ K) + K) true ++
        false :: (u ++ v ++ w)).takeWhile id = _
      exact PvsNP.Units.tc_exp_rev_factor.takeWhile_rep_false _ _
    have hcand : PvsNP.Units.tc_exp_rev_factor.cand (u ++ v ++ w)
        (List.replicate u.length true) (List.replicate (u.length + v.length) true) =
        u ++ v.reverse ++ w := by
      have hA : (PvsNP.Units.tc_exp_rev_factor.splitAt
          (u ++ v ++ w, List.replicate u.length true)).1 = u := by
        show (u ++ v ++ w).take (List.replicate u.length true).length = u
        rw [List.length_replicate]
        have hx : u ++ v ++ w = u ++ (v ++ w) := List.append_assoc u v w
        rw [hx, List.take_left]
      have hD : (PvsNP.Units.tc_exp_rev_factor.splitAt
          (u ++ v ++ w, List.replicate u.length true)).2 = v ++ w := by
        show (u ++ v ++ w).drop (List.replicate u.length true).length = v ++ w
        rw [List.length_replicate]
        have hx : u ++ v ++ w = u ++ (v ++ w) := List.append_assoc u v w
        rw [hx, List.drop_left]
      have hdiff : (PvsNP.Units.tc_exp_rev_factor.splitAt
          (List.replicate (u.length + v.length) true,
            List.replicate u.length true)).2 = List.replicate v.length true := by
        show (List.replicate (u.length + v.length) true).drop
          (List.replicate u.length true).length = List.replicate v.length true
        rw [List.replicate_add, List.drop_left]
      have hM : (PvsNP.Units.tc_exp_rev_factor.splitAt
          (v ++ w, List.replicate v.length true)).1 = v := by
        show (v ++ w).take (List.replicate v.length true).length = v
        rw [List.length_replicate, List.take_left]
      have hC : (PvsNP.Units.tc_exp_rev_factor.splitAt
          (u ++ v ++ w, List.replicate (u.length + v.length) true)).2 = w := by
        show (u ++ v ++ w).drop (List.replicate (u.length + v.length) true).length = w
        rw [List.length_replicate]
        rw [← List.length_append, List.drop_left]
      simp only [PvsNP.Units.tc_exp_rev_factor.cand, hA, hD, hdiff, hM, hC]
    have hlen : (u ++ v.reverse ++ w).length = (u ++ v ++ w).length := by
      simp [List.length_append, List.length_reverse]
    have hEq : (List.replicate (2 ^ ((u ++ v ++ w).length ^ K) + K) true ++
        false :: (u ++ v.reverse ++ w)) =
        PvsNP.Units.tc_exp_rev_factor.padOf K (u ++ v.reverse ++ w) := by
      show (List.replicate (2 ^ ((u ++ v ++ w).length ^ K) + K) true ++
        false :: (u ++ v.reverse ++ w)) =
        (List.replicate (2 ^ ((u ++ v.reverse ++ w).length ^ K) + K) true ++
          false :: (u ++ v.reverse ++ w))
      rw [hlen]
    have e1 := PvsNP.Units.tc_exp_rev_factor.encPair_length
      (PvsNP.Units.tc_exp_rev_factor.padOf K (u ++ v ++ w)) (u ++ v ++ w)
    have e2 := PvsNP.Units.tc_exp_rev_factor.encPair_length
      (PvsNP.Units.tc_exp_rev_factor.encPair
        (PvsNP.Units.tc_exp_rev_factor.padOf K (u ++ v ++ w)) (u ++ v ++ w))
      (List.replicate u.length true)
    have er : (List.replicate u.length true).length = u.length := by simp
    have hx : u.length ≤ (u ++ v ++ w).length := by
      simp only [List.length_append]; omega
    have hy : v.length ≤ (u ++ v ++ w).length := by
      simp only [List.length_append]; omega
    refine ⟨u.length, u.length + v.length, by omega, by omega, ?_⟩
    rw [htw, hcand]
    exact (hpad _).1 ⟨u ++ v.reverse ++ w, hyL, hEq⟩
  · rintro ⟨i, j, hi, hj, htest⟩
    have htw : PvsNP.Units.tc_exp_rev_factor.takeWhileTrue
        (PvsNP.Units.tc_exp_rev_factor.padOf K x) =
        List.replicate (2 ^ (x.length ^ K) + K) true := by
      show (List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x).takeWhile id = _
      exact PvsNP.Units.tc_exp_rev_factor.takeWhile_rep_false _ _
    rw [htw] at htest
    have hmem : (List.replicate (2 ^ (x.length ^ K) + K) true ++
        false :: PvsNP.Units.tc_exp_rev_factor.cand x (List.replicate i true)
          (List.replicate j true)) ∈
        PvsNP.Units.tc_exp_rev_factor.PadSet K L :=
      (hpad _).2 htest
    obtain ⟨y, hyL, hEq⟩ := hmem
    have hEq' : (List.replicate (2 ^ (x.length ^ K) + K) true ++
        false :: PvsNP.Units.tc_exp_rev_factor.cand x (List.replicate i true)
          (List.replicate j true)) =
        List.replicate (2 ^ (y.length ^ K) + K) true ++ false :: y := hEq
    have hrep := PvsNP.Units.m2_exp_iff_padded_p.rep_inj _ _ _ _ hEq'
    obtain ⟨hexp, hcy⟩ := hrep
    have hxy : x.length = y.length := by
      have e1 : 2 ^ (x.length ^ K) = 2 ^ (y.length ^ K) := by omega
      have e2 : x.length ^ K = y.length ^ K :=
        Nat.pow_right_injective (by norm_num) e1
      exact Nat.pow_left_injective (by omega : K ≠ 0) e2
    have hclen : (PvsNP.Units.tc_exp_rev_factor.cand x (List.replicate i true)
        (List.replicate j true)).length = x.length := by
      rw [hcy]; exact hxy.symm
    obtain ⟨u, v, w, hxu, huv⟩ := PvsNP.Units.tc_exp_rev_factor.cand_witness x
      (List.replicate i true) (List.replicate j true) hclen
    exact ⟨u, v, w, hxu, by rw [huv, hcy]; exact hyL⟩
