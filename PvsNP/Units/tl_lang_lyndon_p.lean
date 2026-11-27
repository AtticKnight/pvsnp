import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.tf_fun_rotate
import PvsNP.Units.tf_fun_rotate_all
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.tl_lang_len_square_p

/-
Built on the settled units fr_ladner (cpt_pairG, cpt_fst, cpt_snd, cpt_comp), m2_bounded_unary_search_polytime,
tf_fun_rotate, tf_fun_rotate_all (rotate_iter), m2_iterate_polytime, m2_reverse_polytime, m2_binary_le_polytime,
m2_len_le_polytime, m2_tm_pair_bool_combine, m2_bool_combine_polytime and tl_lang_len_square_p (cpt_nonEmpty)
of github.com/makedotfun/pvsnp. For words of equal length the lexicographic order is the order of the binary
values of the reversed words, so a bad rotation k (0 < k < |x|, not x < rotate k x) is found by a bounded
unary search; x is a Lyndon word iff x is nonempty and the search fails.
-/

namespace PvsNP.Units.tl_lang_lyndon_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

def val (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem val_cons (c : Bool) (l : List Bool) : val (c :: l) = c.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val]
  | cons c l ih =>
    rw [val_cons, List.length_cons, pow_succ]
    cases c <;> (first | omega | (simp only [Bool.toNat_false, Bool.toNat_true]; omega) | (simp; omega))

theorem val_rev_cons (c : Bool) (l : List Bool) :
    val (c :: l).reverse = val l.reverse + 2 ^ l.length * c.toNat := by
  first
  | (unfold val
     rw [List.reverse_cons, List.map_append, Nat.ofDigits_append]
     simp [Nat.ofDigits_singleton])
  | simp [val, Nat.ofDigits_append, Nat.ofDigits_singleton]
  | simp [val, Nat.ofDigits_append, Nat.ofDigits_cons]

theorem cons_lt_iff (x y : Bool) (as bs : List Bool) :
    (x :: as) < (y :: bs) ↔ x < y ∨ x = y ∧ as < bs := by
  first
  | exact List.cons_lt_cons_iff
  | (constructor
     · intro h
       cases h with
       | cons h => exact Or.inr ⟨rfl, h⟩
       | rel h => exact Or.inl h
     · rintro (h | ⟨rfl, h⟩)
       · exact List.Lex.rel h
       · exact List.Lex.cons h)
  | simp

theorem lt_iff_val : ∀ a b : List Bool, a.length = b.length →
    (a < b ↔ val a.reverse < val b.reverse)
  | [], [], _ => by
      constructor
      · intro h
        first
        | exact absurd h (List.lt_irrefl _)
        | (cases h)
        | simp at h
      · intro h
        simp [val] at h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: as, y :: bs, h => by
      have hl : as.length = bs.length := by simpa using h
      rw [cons_lt_iff, lt_iff_val as bs hl, val_rev_cons, val_rev_cons]
      have h1 := val_lt as.reverse
      have h2 := val_lt bs.reverse
      rw [List.length_reverse] at h1 h2
      rw [hl] at h1 ⊢
      have b1 : ¬ (true < false) := by
        first | decide | (intro hc; cases hc) | simp | exact fun hc => absurd hc (by decide)
      have b2 : ¬ (false < false) := by
        first | decide | (intro hc; cases hc) | simp | exact lt_irrefl _
      have b3 : ¬ (true < true) := by
        first | decide | (intro hc; cases hc) | simp | exact lt_irrefl _
      have b4 : false < true := by
        first | decide | rfl | simp | exact Bool.false_lt_true
      cases x <;> cases y <;> simp [b1, b2, b3, b4] <;> omega

def R (p : List Bool × List Bool) : List Bool := (fun y : List Bool => y.rotate 1)^[p.2.length] p.1

def cmpF (p : List Bool × List Bool) : Bool := decide (val (R p).reverse ≤ val p.1.reverse)

def ltF (p : List Bool × List Bool) : Bool := !decide (p.1.length ≤ p.2.length)

def neF (p : List Bool × List Bool) : Bool := !p.2.isEmpty

def W (p : List Bool × List Bool) : Bool := (ltF p && neF p) && cmpF p

theorem cpt_R : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    (fun x : List Bool => x) R := by
  have hlen : ∀ y : List Bool, ((fun x : List Bool => x.rotate 1) y).length ≤ y.length + 0 := by
    intro y
    simp [List.length_rotate]
  have h := PvsNP.Units.m2_iterate_polytime (fun x : List Bool => x.rotate 1) 0
    PvsNP.Units.tf_fun_rotate hlen
  rw [encodePair_eq]
  exact h

theorem cpt_cmp : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    Computability.encodeBool cmpF := by
  have hrev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.reverse) :=
    PvsNP.Units.m2_reverse_polytime
  have h1 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => (R p).reverse) :=
    cpt_comp cpt_R hrev
  have h2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1.reverse) :=
    cpt_comp cpt_fst hrev
  have hp : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => ((R p).reverse, p.1.reverse)) :=
    cpt_pairG h1 h2
  have hle : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun q : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (q.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (q.2.map Bool.toNat))) := by
    rw [encodePair_eq]
    exact PvsNP.Units.m2_binary_le_polytime
  have h := cpt_comp hp hle
  exact h

theorem pt_cmp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer cmpF := by
  rw [← encodePair_eq]
  exact cpt_cmp

theorem pt_ne : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer neF := by
  have h := cpt_comp cpt_snd PvsNP.Units.tl_lang_len_square_p.cpt_nonEmpty
  rw [← encodePair_eq]
  exact h

theorem pt_lt : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer ltF := by
  have h := PvsNP.Units.m2_tm_pair_bool_combine (fun a _ => !a)
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    PvsNP.Units.m2_len_le_polytime PvsNP.Units.m2_len_le_polytime
  exact h

theorem pt_W : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer W := by
  have h1 := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) ltF neF pt_lt pt_ne
  have h2 := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b)
    (fun p : List Bool × List Bool => (fun a b : Bool => a && b) (ltF p) (neF p)) cmpF h1 pt_cmp
  exact h2

theorem W_iff (x : List Bool) (i : ℕ) :
    W (x, List.replicate i true) = true ↔ (0 < i ∧ i < x.length ∧ ¬ x < x.rotate i) := by
  have hR : R (x, List.replicate i true) = x.rotate i := by
    show (fun y : List Bool => y.rotate 1)^[(List.replicate i true).length] x = x.rotate i
    rw [List.length_replicate]
    exact PvsNP.Units.tf_fun_rotate_all.rotate_iter i x
  have hk := lt_iff_val x (x.rotate i) (by simp)
  unfold W ltF neF cmpF
  rw [hR, hk, not_lt]
  clear hR hk
  cases i with
  | zero => simp
  | succ n =>
    first
    | simp [List.replicate_succ]
    | (simp [List.replicate_succ]; omega)
    | (simp [List.replicate_succ]; tauto)

theorem S_iff (x : List Bool) :
    (List.range (x.length + 1)).any (fun i => W (x, List.replicate i true)) = true ↔
      ∃ k, 0 < k ∧ k < x.length ∧ ¬ x < x.rotate k := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, _, hw⟩
    exact ⟨i, (W_iff x i).1 hw⟩
  · rintro ⟨k, hk0, hk1, hk2⟩
    refine ⟨k, ?_, (W_iff x k).2 ⟨hk0, hk1, hk2⟩⟩
    rw [List.mem_range]
    omega

end PvsNP.Units.tl_lang_lyndon_p

theorem PvsNP.Units.tl_lang_lyndon_p :
    ({x : List Bool | x ≠ [] ∧ ∀ k : ℕ, 0 < k → k < x.length → x < x.rotate k} : Language Bool) ∈ PvsNP.P := by
  have hS := PvsNP.Units.m2_bounded_unary_search_polytime PvsNP.Units.tl_lang_lyndon_p.W PvsNP.Units.tl_lang_lyndon_p.pt_W
  have hne : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => !x.isEmpty) :=
    PvsNP.Units.tl_lang_len_square_p.cpt_nonEmpty
  have hD := PvsNP.Units.m2_bool_combine_polytime (fun a b => a && !b) (fun x : List Bool => !x.isEmpty)
    (fun x : List Bool => (List.range (x.length + 1)).any (fun i => PvsNP.Units.tl_lang_lyndon_p.W (x, List.replicate i true)))
    hne hS
  refine ⟨_, hD, fun x => ?_⟩
  have hSx := PvsNP.Units.tl_lang_lyndon_p.S_iff x
  change (x ≠ [] ∧ ∀ k : ℕ, 0 < k → k < x.length → x < x.rotate k) ↔
    ((!x.isEmpty) && !((List.range (x.length + 1)).any
      (fun i => PvsNP.Units.tl_lang_lyndon_p.W (x, List.replicate i true)))) = true
  cases hb : (List.range (x.length + 1)).any (fun i => PvsNP.Units.tl_lang_lyndon_p.W (x, List.replicate i true))
  · have hno : ¬ ∃ k, 0 < k ∧ k < x.length ∧ ¬ x < x.rotate k := by
      intro h
      rw [hSx.2 h] at hb
      exact absurd hb (by decide)
    constructor
    · rintro ⟨hx, _⟩
      cases x with
      | nil => exact absurd rfl hx
      | cons _ _ => rfl
    · intro h1
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact absurd h1 (by decide)
      · intro k hk0 hk1
        by_contra hc
        exact hno ⟨k, hk0, hk1, hc⟩
  · obtain ⟨k, hk0, hk1, hk2⟩ := hSx.1 hb
    constructor
    · rintro ⟨_, hall⟩
      exact absurd (hall k hk0 hk1) hk2
    · intro h
      simp at h
