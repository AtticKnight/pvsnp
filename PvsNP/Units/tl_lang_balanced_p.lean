import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_balanced_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def truesUnary (x : List Bool) : List Bool :=
  x.filterMap (fun b : Bool => if b then some true else none)

def falsesUnary (x : List Bool) : List Bool :=
  x.filterMap (fun b : Bool => if b then none else some true)

theorem cpt_truesUnary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString truesUnary :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) (fun _ => rfl)

theorem cpt_falsesUnary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString falsesUnary :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then none else some true) (fun _ => rfl)

theorem truesUnary_eq_replicate (x : List Bool) :
    truesUnary x = List.replicate (x.count true) true := by
  induction x with
  | nil => rfl
  | cons b l ih =>
    cases b
    · change truesUnary l = List.replicate ((false :: l).count true) true
      simp [ih]
    · change true :: truesUnary l = List.replicate ((true :: l).count true) true
      rw [ih, List.count_cons_self, List.replicate_succ]

theorem falsesUnary_eq_replicate (x : List Bool) :
    falsesUnary x = List.replicate (x.count false) true := by
  induction x with
  | nil => rfl
  | cons b l ih =>
    cases b
    · change true :: falsesUnary l = List.replicate ((false :: l).count false) true
      rw [ih, List.count_cons_self, List.replicate_succ]
    · change falsesUnary l = List.replicate ((true :: l).count false) true
      simp [ih]

theorem cpt_balDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (truesUnary x = falsesUnary x)) := by
  have hp : ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodePair
      (fun x : List Bool => (truesUnary x, falsesUnary x)) :=
    cpt_pair cpt_truesUnary cpt_falsesUnary
  exact cpt_comp hp PvsNP.Units.m2_eq_polytime

end PvsNP.Units.tl_lang_balanced_p

theorem PvsNP.Units.tl_lang_balanced_p :
    ({x : List Bool | x.count true = x.count false} : Language Bool) ∈ PvsNP.P := by
  refine ⟨fun x => decide (PvsNP.Units.tl_lang_balanced_p.truesUnary x =
      PvsNP.Units.tl_lang_balanced_p.falsesUnary x),
    PvsNP.Units.tl_lang_balanced_p.cpt_balDec, fun x => ?_⟩
  change x.count true = x.count false ↔
    decide (PvsNP.Units.tl_lang_balanced_p.truesUnary x =
      PvsNP.Units.tl_lang_balanced_p.falsesUnary x) = true
  rw [PvsNP.Units.tl_lang_balanced_p.truesUnary_eq_replicate,
    PvsNP.Units.tl_lang_balanced_p.falsesUnary_eq_replicate]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have heq := of_decide_eq_true h
    have hlen := congrArg List.length heq
    simp only [List.length_replicate] at hlen
    exact hlen
