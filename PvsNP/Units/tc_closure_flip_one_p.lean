import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime

/-
SPDX-License-Identifier: Apache-2.0
Original proof of the posted flip-one closure, using the named settled campaign
theorems as dependencies. Library interfaces inspected in makedotfun/pvsnp at
7eb344ee73b4bc4869321cf75fc74d65fbea36b1 (Apache-2.0). No imported helper body is
claimed as newly authored. We search every unary position; a nonempty-suffix
guard excludes the extra endpoint, and take/drop recovers the exact split.
-/

namespace PvsNP.Units.tc_closure_flip_one_p

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodeString_eq : PvsNP.encodeString = (fun xs : List Bool => xs) := by
  funext xs
  simp [PvsNP.encodeString, Computability.encodingList]

theorem encodePair_eq : PvsNP.encodePair =
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

def flipFirst : List Bool → List Bool
  | [] => []
  | b :: xs => (!b) :: xs

theorem flipFirst_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString flipFirst := by
  have h := PvsNP.Units.m2_transducer_polytime Bool
    (fun first b => (false, some (if first then !b else b)))
    (fun _ => none) (fun first xs => if first then flipFirst xs else xs)
    (by intro first; cases first <;> rfl)
    (by intro first b xs; cases first <;> simp [flipFirst]) true
  simpa using h

theorem nonempty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun xs : List Bool => !xs.isEmpty) := by
  have run : ∀ (q : Bool) (xs : List Bool),
      fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
        (fun q => some q) q xs = [q || !xs.isEmpty] := by
    intro q xs
    induction xs generalizing q with
    | nil => simp [fstRun]
    | cons b xs ih => simp [fstRun, ih]
  refine fst_polyTime PvsNP.encodeString PvsNP.encodeAnswer _
    (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false ?_
  intro xs
  simpa [encodeString_eq, PvsNP.encodeAnswer, Computability.encodeBool] using
    (run false xs).symm

def changeAt (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ flipFirst (p.1.drop p.2.length)

theorem pieces_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1.take p.2.length) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1.drop p.2.length) := by
  exact ⟨cpt_comp cpt_swap PvsNP.Units.m2_take_drop_length_polytime.1,
    cpt_comp cpt_swap PvsNP.Units.m2_take_drop_length_polytime.2⟩

theorem changeAt_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString changeAt := by
  have ht := cpt_comp cpt_unpairB pieces_poly.1
  have hd := cpt_comp cpt_unpairB pieces_poly.2
  have hg := cpt_app2 ht (cpt_comp hd flipFirst_poly)
  have h := cpt_comp cpt_pairB hg
  change PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      p.1.take p.2.length ++ flipFirst (p.1.drop p.2.length))
  simpa only [unpairB_pairB, encodeString_eq, encodePair_eq, PvsNP.PolyTimeComputable,
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime] using h

def test (f : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  (!(p.1.drop p.2.length).isEmpty) && f (changeAt p)

theorem test_poly (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (test f) := by
  have hn : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => !(p.1.drop p.2.length).isEmpty) :=
    cpt_comp (f := fun p : List Bool × List Bool => p.1.drop p.2.length)
      (g := fun xs : List Bool => !xs.isEmpty) pieces_poly.2 nonempty_poly
  have hm : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => f (changeAt p)) := cpt_comp changeAt_poly hf
  exact PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ hn hm

theorem search_correct (L : Language Bool) (f : List Bool → Bool)
    (hf : ∀ x : List Bool, x ∈ L ↔ f x = true) (x : List Bool) :
    (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L) ↔
      (List.range (x.length + 1)).any (fun i => test f (x, List.replicate i true)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, v, b, rfl, h⟩
    refine ⟨u.length, List.mem_range.mpr (by simp), ?_⟩
    simpa [test, changeAt, flipFirst, List.take_append, List.drop_append] using (hf _).mp h
  · rintro ⟨i, _, h⟩
    cases hd : x.drop i with
    | nil => simp [test, hd] at h
    | cons b v =>
      refine ⟨x.take i, v, b, ?_, ?_⟩
      · simpa only [hd] using (List.take_append_drop i x).symm
      · apply (hf _).mpr
        simpa [test, changeAt, List.length_replicate, hd, flipFirst] using h

end PvsNP.Units.tc_closure_flip_one_p

/-- A polynomial-time decider can test each of the linearly many single-bit flips. -/
theorem PvsNP.Units.tc_closure_flip_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool),
        x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  rcases hL with ⟨f, hpoly, hcorrect⟩
  refine ⟨_, PvsNP.Units.m2_bounded_unary_search_polytime _
    (PvsNP.Units.tc_closure_flip_one_p.test_poly f hpoly), ?_⟩
  intro x
  exact PvsNP.Units.tc_closure_flip_one_p.search_correct L f hcorrect x
