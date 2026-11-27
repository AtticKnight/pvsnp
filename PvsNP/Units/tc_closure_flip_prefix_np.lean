import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_np_projection

/-
A unary certificate c chooses the prefix length |c|, through the settled bounded projection
m2_np_projection with the map (x, c) to (x.take |c|).reverse ++ x.drop |c|. Prefix lengths beyond
|x| give the same string as |x| itself, so certificates of length at most |x| lose nothing.
-/

namespace PvsNP.Units.tc_closure_flip_prefix_np

/-- Reverse the prefix of `x` of length `|c|`. -/
def g (p : List Bool × List Bool) : List Bool :=
  (p.1.take p.2.length).reverse ++ p.1.drop p.2.length

theorem g_polytime : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.2, p.1)) :=
    PvsNP.Units.m2_tm_pair_fork_polytime _ _ PvsNP.Units.m2_pair_split_polytime.2.1
      PvsNP.Units.m2_pair_split_polytime.1
  have ht : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 PvsNP.Units.m2_take_drop_length_polytime.1
  have hr : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1.take p.2.length).reverse) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ ht PvsNP.Units.m2_reverse_polytime
  have hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 PvsNP.Units.m2_take_drop_length_polytime.2
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ hr hd)
    PvsNP.Units.m2_pair_build_polytime.cpt_append

theorem flip_eq (L : Language Bool) :
    ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) =
      ({x : List Bool | ∃ c : List Bool, c.length ≤ Polynomial.eval x.length Polynomial.X ∧
          g (x, c) ∈ L} : Language Bool) := by
  ext x
  change (∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L) ↔
      ∃ c : List Bool, c.length ≤ Polynomial.eval x.length Polynomial.X ∧ g (x, c) ∈ L
  simp only [Polynomial.eval_X]
  constructor
  · rintro ⟨i, hi⟩
    rcases le_total i x.length with h | h
    · refine ⟨List.replicate i false, by simpa using h, ?_⟩
      simp only [g, List.length_replicate]
      exact hi
    · refine ⟨List.replicate x.length false, by simp, ?_⟩
      simp only [g, List.length_replicate]
      rw [List.take_of_length_le h, List.drop_of_length_le h] at hi
      rw [List.take_of_length_le (le_refl _), List.drop_of_length_le (le_refl _)]
      exact hi
  · rintro ⟨c, -, hc⟩
    exact ⟨c.length, hc⟩

end PvsNP.Units.tc_closure_flip_prefix_np

/-- NP is closed under reversing a prefix (TM2). -/
theorem PvsNP.Units.tc_closure_flip_prefix_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_flip_prefix_np.flip_eq]
  exact PvsNP.Units.m2_np_projection L PvsNP.Units.tc_closure_flip_prefix_np.g Polynomial.X hL
    PvsNP.Units.tc_closure_flip_prefix_np.g_polytime
