import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_tm_infix_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine

/-
Built on the settled units m2_polytime_comp, m2_pair_split_polytime, tf_fun_self_append,
m2_tm_pair_fork_polytime, m2_tm_infix_polytime, m2_len_le_polytime, m2_tm_pair_swap_polytime and
m2_tm_pair_bool_combine of github.com/makedotfun/pvsnp (Apache License 2.0), which this file imports.
y is a rotation of x exactly when the lengths agree and y is a factor of x ++ x.
-/

namespace PvsNP.Units.tr_rel_rotation

theorem self_append_split (x : List Bool) (m : ℕ) :
    x.take m ++ (x.drop m ++ x.take m) ++ x.drop m = x ++ x := by
  calc x.take m ++ (x.drop m ++ x.take m) ++ x.drop m
      = (x.take m ++ x.drop m) ++ (x.take m ++ x.drop m) := by simp only [List.append_assoc]
    _ = x ++ x := by rw [List.take_append_drop]

theorem rot_iff (x y : List Bool) :
    (∃ k : ℕ, x.rotate k = y) ↔
      (x.length ≤ y.length ∧ y.length ≤ x.length) ∧ y <:+: x ++ x := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    rcases Nat.eq_zero_or_pos x.length with h0 | hpos
    · have hx : x = [] := List.eq_nil_of_length_eq_zero h0
      subst hx
      simp
    · have hm : k % x.length ≤ x.length := (Nat.mod_lt _ hpos).le
      rw [← List.rotate_mod, List.rotate_eq_drop_append_take hm]
      exact ⟨x.take (k % x.length), x.drop (k % x.length), self_append_split x _⟩
  · rintro ⟨⟨h1, h2⟩, s, t, hst⟩
    have hlen := congrArg List.length hst
    simp only [List.length_append] at hlen
    have hm : s.length ≤ x.length := by omega
    refine ⟨s.length, ?_⟩
    rw [List.rotate_eq_drop_append_take hm]
    rw [← self_append_split x s.length] at hst
    have e1 := List.append_inj hst (by
      simp only [List.length_append, List.length_take, List.length_drop]; omega)
    have e2 := List.append_inj e1.1 (by
      simp only [List.length_take]; omega)
    exact e2.2.symm

end PvsNP.Units.tr_rel_rotation

/-- Rotation is decided by two length tests and one factor test against x ++ x. -/
theorem PvsNP.Units.tr_rel_rotation :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (∃ k : ℕ, p.1.rotate k = p.2) ↔ f p = true := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2) :=
    PvsNP.Units.m2_pair_split_polytime.2.1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ p.1) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => p.1)
      (fun x : List Bool => x ++ x) PvsNP.Units.m2_pair_split_polytime.1
      PvsNP.Units.tf_fun_self_append
  have hF : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.2, p.1 ++ p.1)) :=
    PvsNP.Units.m2_tm_pair_fork_polytime _ _ hA hB
  have hI : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2 <:+: p.1 ++ p.1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => (p.2, p.1 ++ p.1))
      (fun q : List Bool × List Bool => decide (q.1 <:+: q.2)) hF
      PvsNP.Units.m2_tm_infix_polytime
  have hL2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => (p.2, p.1))
      (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length))
      PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_len_le_polytime
  have hL := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b) _ _
    PvsNP.Units.m2_len_le_polytime hL2
  have hAll := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b) _ _ hL hI
  refine ⟨_, hAll, ?_⟩
  intro p
  rw [PvsNP.Units.tr_rel_rotation.rot_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
