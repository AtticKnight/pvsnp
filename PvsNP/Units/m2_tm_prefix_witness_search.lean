import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

import PvsNP.Units.m2_polytime_comp

import PvsNP.Units.m2_take_drop_length_polytime

import PvsNP.Units.m2_tm_pair_fork_polytime

import PvsNP.Units.m2_tm_pair_swap_polytime

import PvsNP.Units.m2_bounded_unary_search_polytime


set_option autoImplicit false


namespace PvsNP.Units.m2_tm_prefix_witness_search


open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines


/-- The first projection of a pair, in polynomial time. -/
theorem fst_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) :=
  cpt_fst


/-- From a pair `(x, w)`, the prefix of `x` of length `|w|`, in polynomial time:
swap the pair and use the settled take-by-length unit. -/
theorem take_by_snd_length_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.length) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.2, p.1))
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    PvsNP.Units.m2_tm_pair_swap_polytime
    (PvsNP.Units.m2_take_drop_length_polytime).1


/-- The pair map sending `(x, w)` to `(x, x.take w.length)`, in polynomial time. -/
theorem fork_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.1.take p.2.length)) :=
  PvsNP.Units.m2_tm_pair_fork_polytime _ _ fst_poly take_by_snd_length_poly


/-- Feeding `V` the pair `(x, x.take w.length)` in place of `(x, w)` stays
polynomial-time. -/
theorem subst_prefix_poly (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => V (p.1, p.1.take p.2.length)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.1, p.1.take p.2.length)) V
    fork_poly hV


end PvsNP.Units.m2_tm_prefix_witness_search


/-- Searching the prefixes of the input for one a polynomial-time test accepts
takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_prefix_witness_search :
    ∀ V : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
          (fun x : List Bool => (List.range (x.length + 1)).any (fun i => V (x, x.take i))) := by
  intro V hV
  have h := PvsNP.Units.m2_bounded_unary_search_polytime
    (fun p : List Bool × List Bool => V (p.1, p.1.take p.2.length))
    (PvsNP.Units.m2_tm_prefix_witness_search.subst_prefix_poly V hV)
  simpa only [List.length_replicate] using h
