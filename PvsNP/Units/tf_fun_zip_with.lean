import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_tm_pair_zip_polytime
import PvsNP.Units.m2_polytime_comp

/-
Closes tf_fun_zip_with: the bitwise AND of two strings takes polynomial time
(TM2). Interleave the two strings (settled m2_tm_pair_zip_polytime), then run a
two-state transducer over the interleave that ANDs consecutive bit pairs
(settled m2_transducer_polytime), and compose the two steps (settled
m2_polytime_comp).
-/

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_zip_with

/-- One step of the pairwise-AND transducer: hold the first bit of a pair, and
on the second bit output their AND. -/
def zipStep : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some a, b => (none, some (a && b))

/-- Pairwise AND of consecutive bits; a trailing lone bit is dropped. -/
def pairwiseAnd : Option Bool → List Bool → List Bool
  | _, [] => []
  | none, b :: x => pairwiseAnd (some b) x
  | some a, b :: x => (a && b) :: pairwiseAnd none x

/-- The pairwise AND of the interleave of two strings is their bitwise AND. -/
theorem pairwiseAnd_interleave : ∀ (x y : List Bool),
    pairwiseAnd none ((List.zipWith (fun a b => [a, b]) x y).flatten)
      = List.zipWith (fun a b => a && b) x y := by
  intro x
  induction x with
  | nil => intro y; cases y <;> rfl
  | cons a as ih =>
    intro y
    cases y with
    | nil => rfl
    | cons b bs =>
      have h : (List.zipWith (fun a b => [a, b]) (a :: as) (b :: bs)).flatten
          = a :: b :: (List.zipWith (fun a b => [a, b]) as bs).flatten := rfl
      rw [h]
      show (a && b) :: pairwiseAnd none ((List.zipWith (fun a b => [a, b]) as bs).flatten)
        = (a && b) :: List.zipWith (fun a b => a && b) as bs
      rw [ih bs]

/-- Pairwise AND of consecutive bits is polynomial-time: a finite-state
transducer with states `Option Bool` (no pending bit, or the pending first bit). -/
theorem pairwiseAnd_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (pairwiseAnd none) :=
  PvsNP.Units.m2_transducer_polytime (Option Bool)
    zipStep (fun _ => none) pairwiseAnd
    (by intro q; rfl)
    (by intro q b x; cases q <;> rfl)
    none

end PvsNP.Units.tf_fun_zip_with

/-- The bitwise AND of two strings takes polynomial time (TM2): interleave the
two strings, AND consecutive bit pairs with a finite-state transducer, compose. -/
theorem PvsNP.Units.tf_fun_zip_with :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) := by
  have hzip : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten) :=
    PvsNP.Units.m2_tm_pair_zip_polytime
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (PvsNP.Units.tf_fun_zip_with.pairwiseAnd none ∘ fun p : List Bool × List Bool =>
        (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      _ _ hzip PvsNP.Units.tf_fun_zip_with.pairwiseAnd_poly
  have heq : (PvsNP.Units.tf_fun_zip_with.pairwiseAnd none ∘ fun p : List Bool × List Bool =>
      (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten)
      = (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) := by
    funext ⟨x, y⟩
    simp only [Function.comp_apply]
    exact PvsNP.Units.tf_fun_zip_with.pairwiseAnd_interleave x y
  rwa [heq] at hcomp
