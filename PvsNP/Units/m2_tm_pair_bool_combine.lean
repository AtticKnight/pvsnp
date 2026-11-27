import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

import PvsNP.Units.m2_bool_combine_polytime

/-
  Original work for the make.fun desk campaign `pvsnp`, unit `m2_tm_pair_bool_combine`:
  a Boolean combination of two polynomial-time tests on pairs is polynomial-time.

  Proof idea: the settled unit `m2_bool_combine_polytime` already proves this for inputs
  written by `PvsNP.encodeString`. Transport it to inputs written by `PvsNP.encodePair`
  with the settled packing `pairB` of `fr_ladner` (its `cpt_pairB` packs a pair into a
  string and `cpt_unpairB` unpacks it, with `unpainB_pairB` the round trip), composing
  with `cpt_comp`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_pair_bool_combine

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

end PvsNP.Units.m2_tm_pair_bool_combine

/-- Combining two polynomial-time tests on pairs with a Boolean operation (TM2). -/
theorem PvsNP.Units.m2_tm_pair_bool_combine :
    ∀ (op : Bool → Bool → Bool) (c d : List Bool × List Bool → Bool),
  PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer c →
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer d →
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => op (c p) (d p)) :=
  PvsNP.Units.m2_tm_pair_bool_combine.pair_bool_combine
