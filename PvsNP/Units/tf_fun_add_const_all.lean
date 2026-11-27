import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.tf_fun_pred
import PvsNP.Units.tf_fun_add_const

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_add_const_all

/-- Adding any fixed constant to a binary numeral is polynomial-time computable:
induction on the constant. The step composes with the successor function; the
base case is the predecessor function composed with the successor function,
which is the identity on values by `ofDigits_bits`. -/
theorem main : ∀ c : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + c)) := by
  intro c
  induction c with
  | zero =>
    have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeString _ _ PvsNP.Units.tf_fun_succ PvsNP.Units.tf_fun_pred
    have hfun : ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) - 1)) ∘
        (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1))) =
        (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 0)) := by
      funext x
      simp only [Function.comp_apply]
      rw [PvsNP.Units.tf_fun_add_const.ofDigits_bits, Nat.add_sub_cancel, Nat.add_zero]
    rw [hfun] at hcomp
    exact hcomp
  | succ c ih =>
    have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeString _ _ ih PvsNP.Units.tf_fun_succ
    have hfun : ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) ∘
        (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + c))) =
        (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + (c + 1))) := by
      funext x
      simp only [Function.comp_apply]
      rw [PvsNP.Units.tf_fun_add_const.ofDigits_bits, Nat.add_assoc]
    rw [hfun] at hcomp
    exact hcomp

end PvsNP.Units.tf_fun_add_const_all

theorem PvsNP.Units.tf_fun_add_const_all :
    ∀ c : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + c)) :=
  PvsNP.Units.tf_fun_add_const_all.main
