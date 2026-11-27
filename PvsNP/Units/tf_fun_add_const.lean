import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_succ

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_add_const

/-- The binary value of the bit list of `n` is `n` again. -/
theorem ofDigits_bits : ∀ n : ℕ, Nat.ofDigits 2 ((Nat.bits n).map Bool.toNat) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      simp [Nat.zero_bits]
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num)
      have e := Nat.div_add_mod n 2
      rcases Nat.mod_two_eq_zero_or_one n with hm | hm
      · rw [hm, add_zero] at e
        have hdiv : n / 2 ≠ 0 := by
          intro h
          omega
        rw [← e, Nat.bit0_bits _ hdiv, List.map_cons, Nat.ofDigits_cons,
          ih (n / 2) hlt, show Bool.toNat false = 0 from rfl, Nat.zero_add,
          Nat.mul_comm 2 (n / 2)]
      · rw [hm] at e
        rw [← e, Nat.bit1_bits, List.map_cons, Nat.ofDigits_cons,
          ih (n / 2) hlt, show Bool.toNat true = 1 from rfl,
          Nat.mul_comm 2 (n / 2), Nat.add_comm 1 (n / 2 * 2)]

theorem main : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
  have hs : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) :=
    PvsNP.Units.tf_fun_succ.main
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ hs hs
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ h1 hs
  have h3 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ h2 hs
  have h4 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ h3 hs
  have hfun : ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) ∘
      ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) ∘
      ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) ∘
      ((fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) ∘
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)))))) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
    funext x
    simp only [Function.comp_apply]
    rw [ofDigits_bits, ofDigits_bits, ofDigits_bits, ofDigits_bits]
  rw [← hfun]
  exact h4

end PvsNP.Units.tf_fun_add_const

theorem PvsNP.Units.tf_fun_add_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) :=
  PvsNP.Units.tf_fun_add_const.main
