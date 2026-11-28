import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime

set_option autoImplicit false

/-!
With `V' (x, w) = V (x, x.drop w.length)` we get `V' (x, List.replicate i true) = V (x, x.drop i)`,
so the search is the settled bounded unary search over `V'`. `V'` is `V` after a pair fork of the
first part and `p.1.drop p.2.length` (a swap, then the settled `drop`).
-/

namespace PvsNP.Units.m2_tm_suffix_witness_search

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

lemma encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

theorem main_proof : ∀ V : List Bool × List Bool → Bool,
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => (List.range (x.length + 1)).any (fun i => V (x, x.drop i))) := by
  intro V hV
  have hfst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) := by
    rw [← encodePair_eq]
    exact cpt_fst
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.drop p.2.length) := by
    have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.2, p.1))
      (fun q : List Bool × List Bool => q.2.drop q.1.length)
      PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_take_drop_length_polytime.2
    exact h
  have hfork := PvsNP.Units.m2_tm_pair_fork_polytime
    (fun p : List Bool × List Bool => p.1)
    (fun p : List Bool × List Bool => p.1.drop p.2.length) hfst hdrop
  have hV' : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => V (p.1, p.1.drop p.2.length)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => (p.1, p.1.drop p.2.length)) V hfork hV
  have hS := PvsNP.Units.m2_bounded_unary_search_polytime
    (fun p : List Bool × List Bool => V (p.1, p.1.drop p.2.length)) hV'
  have e2 : (fun x : List Bool => (List.range (x.length + 1)).any
        (fun i => V (x, x.drop (List.replicate i true).length))) =
      (fun x : List Bool => (List.range (x.length + 1)).any (fun i => V (x, x.drop i))) := by
    funext x
    simp only [List.length_replicate]
  rw [← e2]
  exact hS

end PvsNP.Units.m2_tm_suffix_witness_search

theorem PvsNP.Units.m2_tm_suffix_witness_search :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
    (fun x : List Bool => (List.range (x.length + 1)).any (fun i => V (x, x.drop i))) :=
  PvsNP.Units.m2_tm_suffix_witness_search.main_proof
