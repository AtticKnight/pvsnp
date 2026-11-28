import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_tm_infix_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_bool_combine

-- Built on the settled campaign units m2_polytime_comp, m2_pair_split_polytime, tf_fun_self_append,
-- m2_tm_pair_fork_polytime, m2_tm_infix_polytime, m2_len_le_polytime and m2_tm_pair_bool_combine
-- (as the settled tr_rel_rotation): x occurs in some rotation of y exactly when |x| <= |y| and x is a factor of y ++ y.

namespace PvsNP.Units.tr_rel_cyclic_infix

theorem self_append_split (x : List Bool) (m : ℕ) :
    x.take m ++ (x.drop m ++ x.take m) ++ x.drop m = x ++ x := by
  calc x.take m ++ (x.drop m ++ x.take m) ++ x.drop m
      = (x.take m ++ x.drop m) ++ (x.take m ++ x.drop m) := by simp only [List.append_assoc]
    _ = x ++ x := by rw [List.take_append_drop]

theorem rot_infix (y : List Bool) (k : ℕ) : y.rotate k <:+: y ++ y := by
  rcases Nat.eq_zero_or_pos y.length with h0 | hpos
  · have hy : y = [] := List.eq_nil_of_length_eq_zero h0
    subst hy
    simp
  · have hm : k % y.length ≤ y.length := (Nat.mod_lt _ hpos).le
    rw [← List.rotate_mod, List.rotate_eq_drop_append_take hm]
    exact ⟨y.take (k % y.length), y.drop (k % y.length), self_append_split y _⟩

theorem cyc_iff (x y : List Bool) :
    (∃ k : ℕ, x <:+: y.rotate k) ↔ (x.length ≤ y.length ∧ x <:+: y ++ y) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨?_, hk.trans (rot_infix y k)⟩
    have := hk.length_le
    simpa using this
  · rintro ⟨hl, s, t, hst⟩
    by_cases hs : s.length ≤ y.length
    · refine ⟨s.length, ?_⟩
      rw [List.rotate_eq_drop_append_take hs]
      have e : s ++ (x ++ t) =
          y.take s.length ++ ((y.drop s.length ++ y.take s.length) ++ y.drop s.length) := by
        rw [← List.append_assoc, hst, ← List.append_assoc]
        exact (self_append_split y s.length).symm
      have e1 := List.append_inj e (by simp only [List.length_take]; omega)
      have h1 : x <+: (y.drop s.length ++ y.take s.length) ++ y.drop s.length := by
        rw [← e1.2]
        exact List.prefix_append x t
      have h2 : x <+: y.drop s.length ++ y.take s.length :=
        List.prefix_of_prefix_length_le h1 (List.prefix_append _ _) (by
          simp only [List.length_append, List.length_drop, List.length_take]
          omega)
      exact h2.isInfix
    · have hsp : s <+: y ++ y := ⟨x ++ t, by rw [← List.append_assoc]; exact hst⟩
      have hys : y <+: s := List.prefix_of_prefix_length_le (List.prefix_append y y) hsp (by omega)
      obtain ⟨s', rfl⟩ := hys
      have e : y ++ (s' ++ (x ++ t)) = y ++ y := by
        simpa only [List.append_assoc] using hst
      have e2 : s' ++ (x ++ t) = y := List.append_cancel_left e
      refine ⟨0, ?_⟩
      rw [List.rotate_zero]
      exact ⟨s', t, by simpa only [List.append_assoc] using e2⟩

end PvsNP.Units.tr_rel_cyclic_infix

/-- Cyclic occurrence is decided by one length test and one factor test against y ++ y. -/
theorem PvsNP.Units.tr_rel_cyclic_infix :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (∃ k : ℕ, p.1 <:+: p.2.rotate k) ↔ f p = true := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) :=
    PvsNP.Units.m2_pair_split_polytime.1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2 ++ p.2) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => p.2)
      (fun x : List Bool => x ++ x) PvsNP.Units.m2_pair_split_polytime.2.1
      PvsNP.Units.tf_fun_self_append
  have hF : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2 ++ p.2)) :=
    PvsNP.Units.m2_tm_pair_fork_polytime _ _ hA hB
  have hI : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1 <:+: p.2 ++ p.2)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => (p.1, p.2 ++ p.2))
      (fun q : List Bool × List Bool => decide (q.1 <:+: q.2)) hF
      PvsNP.Units.m2_tm_infix_polytime
  have hAll := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b) _ _
    PvsNP.Units.m2_len_le_polytime hI
  refine ⟨_, hAll, ?_⟩
  intro p
  rw [PvsNP.Units.tr_rel_cyclic_infix.cyc_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
