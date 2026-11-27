import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_tm_pair_zip_polytime
import PvsNP.Units.m2_polytime_comp

/-
Closes tf_fun_pair_lcp: the longest common prefix of two binary strings takes
polynomial time (TM2). Interleave the two strings with settled
`m2_tm_pair_zip_polytime`, then run a 4-state transducer (`Option (Option Bool)`)
over the interleave that emits matching pairs and halts on the first mismatch
(settled `m2_transducer_polytime`), and compose with `m2_polytime_comp`.
-/

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_lcp

/-- One step of the LCP transducer over interleaved bit pairs:
- `none`: already saw a mismatch, emit nothing forever;
- `some none`: ready for the first bit of the next pair;
- `some (some a)`: holding first bit `a`, emit `a` if `a == b` else stop. -/
def lcpStep : Option (Option Bool) → Bool → Option (Option Bool) × Option Bool
  | none, _ => (none, none)
  | some none, a => (some (some a), none)
  | some (some a), b => if a == b then (some none, some a) else (none, none)

/-- Transducer semantics for `lcpStep`. -/
def lcpTrans : Option (Option Bool) → List Bool → List Bool
  | _, [] => []
  | none, _ :: xs => lcpTrans none xs
  | some none, a :: xs => lcpTrans (some (some a)) xs
  | some (some a), b :: xs =>
      if a == b then a :: lcpTrans (some none) xs else lcpTrans none xs

/-- Once stopped (`none`), the transducer emits nothing. -/
theorem lcpTrans_none (xs : List Bool) : lcpTrans none xs = [] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => exact ih

/-- Running `lcpTrans (some none)` on the interleaved strings produces their
longest common prefix. -/
theorem lcpTrans_interleave : ∀ (x y : List Bool),
    lcpTrans (some none) ((List.zipWith (fun a b => [a, b]) x y).flatten)
      = ((List.zip x y).takeWhile (fun q => q.1 == q.2)).map Prod.fst := by
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
      simp only [lcpTrans, List.zip_cons_cons, List.takeWhile_cons]
      cases hab : (a == b) with
      | false =>
        simp [lcpTrans_none]
      | true =>
        simp only [↓reduceIte, List.map_cons]
        exact congrArg (List.cons a) (ih bs)

/-- `lcpTrans (some none)` is polynomial-time by `m2_transducer_polytime`. -/
theorem lcpTrans_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (lcpTrans (some none)) :=
  PvsNP.Units.m2_transducer_polytime (Option (Option Bool))
    lcpStep (fun _ => none) lcpTrans
    (by intro q; rfl)
    (by
      intro q b x
      cases q with
      | none => rfl
      | some o =>
        cases o with
        | none => rfl
        | some a =>
          simp only [lcpStep, lcpTrans]
          cases (a == b) <;> rfl)
    (some none)

end PvsNP.Units.tf_fun_pair_lcp

/-- The longest common prefix of two binary strings takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_pair_lcp :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        ((List.zip p.1 p.2).takeWhile (fun q => q.1 == q.2)).map Prod.fst) := by
  have hzip : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten) :=
    PvsNP.Units.m2_tm_pair_zip_polytime
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (PvsNP.Units.tf_fun_pair_lcp.lcpTrans (some none) ∘
        fun p : List Bool × List Bool =>
          (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      _ _ hzip PvsNP.Units.tf_fun_pair_lcp.lcpTrans_poly
  have heq : (PvsNP.Units.tf_fun_pair_lcp.lcpTrans (some none) ∘
      fun p : List Bool × List Bool =>
        (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten)
      = (fun p : List Bool × List Bool =>
          ((List.zip p.1 p.2).takeWhile (fun q => q.1 == q.2)).map Prod.fst) := by
    funext ⟨x, y⟩
    simp only [Function.comp_apply]
    exact PvsNP.Units.tf_fun_pair_lcp.lcpTrans_interleave x y
  rwa [heq] at hcomp
