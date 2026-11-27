import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_tm_empty_test
import PvsNP.Units.m2_tm_pair_bool_combine

-- Built on the settled campaign units m2_prefix_polytime, m2_tm_empty_test, m2_tm_pair_fork_polytime,
-- m2_pair_split_polytime, m2_polytime_comp and m2_tm_pair_bool_combine.
-- For a nonempty x, w is a prefix of x x x ... exactly when w is a prefix of x ++ w.

namespace PvsNP.Units.tr_rel_period_of

theorem T_add (x : List Bool) (m n : ℕ) :
    (List.replicate (m + n) x).flatten =
      (List.replicate m x).flatten ++ (List.replicate n x).flatten := by
  rw [List.replicate_add, List.flatten_append]

theorem T_succ (x : List Bool) (n : ℕ) :
    (List.replicate (n + 1) x).flatten = x ++ (List.replicate n x).flatten := by
  rw [List.replicate_succ, List.flatten_cons]

theorem T_mono (x : List Bool) {m n : ℕ} (h : m ≤ n) :
    (List.replicate m x).flatten <+: (List.replicate n x).flatten := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [T_add]
  exact List.prefix_append _ _

theorem fwd (x w : List Bool) (h : w <+: (List.replicate w.length x).flatten) :
    w <+: x ++ w := by
  have h1 : x ++ w <+: (List.replicate (w.length + 1) x).flatten := by
    rw [T_succ]
    exact (List.prefix_append_right_inj x).mpr h
  have h2 : w <+: (List.replicate (w.length + 1) x).flatten :=
    h.trans (T_mono x (Nat.le_succ _))
  exact List.prefix_of_prefix_length_le h2 h1 (by simp)

theorem bwd (x : List Bool) : ∀ n : ℕ, ∀ w : List Bool, w <+: x ++ w →
    w.length ≤ n * x.length → w <+: (List.replicate n x).flatten := by
  intro n
  induction n with
  | zero =>
    intro w _ hl
    have h0 : w.length = 0 := by
      rw [Nat.zero_mul] at hl
      omega
    rw [List.eq_nil_of_length_eq_zero h0]
    exact List.nil_prefix
  | succ n ih =>
    intro w hw hl
    rw [T_succ]
    by_cases hle : w.length ≤ x.length
    · have hx : w <+: x := List.prefix_of_prefix_length_le hw (List.prefix_append x w) hle
      exact hx.trans (List.prefix_append _ _)
    · have hxw : x <+: w :=
        List.prefix_of_prefix_length_le (List.prefix_append x w) hw (by omega)
      obtain ⟨w', rfl⟩ := hxw
      have hw' : w' <+: x ++ w' := (List.prefix_append_right_inj x).mp hw
      have hl' : w'.length ≤ n * x.length := by
        simp only [List.length_append] at hl
        rw [Nat.add_mul, Nat.one_mul] at hl
        omega
      exact (List.prefix_append_right_inj x).mpr (ih w' hw' hl')

theorem period_iff (x w : List Bool) :
    (x ≠ [] ∧ w <+: (List.replicate w.length x).flatten) ↔ (x ≠ [] ∧ w <+: x ++ w) := by
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fwd x w h⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, bwd x w.length w h ?_⟩
    have h1 : 1 ≤ x.length := by
      rcases x with _ | ⟨a, t⟩
      · exact absurd rfl hx
      · simp
    nlinarith

end PvsNP.Units.tr_rel_period_of

/-- A string is a period of another when it is nonempty and the other is a prefix of it ++ the other. -/
theorem PvsNP.Units.tr_rel_period_of :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (p.1 ≠ [] ∧ p.2 <+: (List.replicate p.2.length p.1).flatten) ↔ f p = true := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2) :=
    PvsNP.Units.m2_pair_split_polytime.2.1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ p.2) :=
    PvsNP.Units.m2_pair_split_polytime.2.2
  have hF : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.2, p.1 ++ p.2)) :=
    PvsNP.Units.m2_tm_pair_fork_polytime _ _ hA hB
  have hPre : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => p.2.isPrefixOf (p.1 ++ p.2)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => (p.2, p.1 ++ p.2))
      (fun q : List Bool × List Bool => q.1.isPrefixOf q.2) hF
      PvsNP.Units.m2_prefix_polytime
  have hE0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (x = [])) :=
    PvsNP.Units.m2_tm_empty_test (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
  have hE : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1 = [])) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => p.1)
      (fun x : List Bool => decide (x = [])) PvsNP.Units.m2_pair_split_polytime.1 hE0
  have hAll := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => !a && b) _ _ hE hPre
  refine ⟨_, hAll, fun p => ?_⟩
  rw [PvsNP.Units.tr_rel_period_of.period_iff]
  simp [List.isPrefixOf_iff_prefix]
