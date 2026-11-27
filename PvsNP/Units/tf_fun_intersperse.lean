import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_np_projection

set_option autoImplicit false

/-
Writing `false` between the bits of a binary string takes polynomial time (TM2).
`x.intersperse false` is the tail of `x.flatMap (fun b => [false, b])`:
the flatMap writes `false` before every bit, and dropping the leading `false`
leaves exactly one `false` between consecutive bits. The flatMap step is
polynomial-time by the settled `cpt_flatMap`, the tail step by the library's
`cpt_tail`, composed by the settled `m2_polytime_comp`.
-/

/-- Writing `false` between the bits of a binary string takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_intersperse :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.intersperse false) := by
  have hflat : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.flatMap fun b => [false, b]) :=
    PvsNP.Units.m2_inv_hom_closed.cpt_flatMap (fun b => [false, b])
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.tail) :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.cpt_tail
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x.flatMap fun b => [false, b])
    List.tail hflat htail
  have key : ∀ x : List Bool,
      x.intersperse false = (x.flatMap fun b => [false, b]).tail := by
    intro x
    induction x with
    | nil => rfl
    | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l' =>
        calc (a :: b :: l').intersperse false
            = a :: false :: (b :: l').intersperse false := rfl
          _ = a :: false :: ((b :: l').flatMap fun b => [false, b]).tail := by rw [ih]
          _ = a :: ((b :: l').flatMap fun b => [false, b]) := rfl
  have heq : (fun x : List Bool => x.intersperse false)
      = List.tail ∘ (fun x : List Bool => x.flatMap fun b => [false, b]) := by
    funext x
    exact key x
  rw [heq]
  exact hcomp
