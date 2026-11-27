import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.tf_fun_pair_mul

namespace PvsNP.Units.tf_fun_mul_const_all

private def val (x : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)

private theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp only [val, List.map_cons, Nat.ofDigits_cons]

private theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      set b : Bool := decide ((m + 1) % 2 = 1)
      set q : ℕ := (m + 1) / 2
      have hbit : m + 1 = Nat.bit b q := by
        cases hb : b
        · have hmod : (m + 1) % 2 = 0 := by
            have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
            omega
          change m + 1 = 2 * q
          omega
        · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
          change m + 1 = 2 * q + 1
          omega
      have hcond : q = 0 → b = true := by
        intro hq
        have hmod : (m + 1) % 2 = 1 := by omega
        exact decide_eq_true hmod
      have hlt : q < m + 1 := by omega
      rw [hbit, Nat.bits_append_bit q b hcond, val_cons, ih q hlt]
      rw [← hbit]
      cases hb : b
      · have hmod : (m + 1) % 2 = 0 := by
          have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
          omega
        simp only [Bool.toNat_false]
        omega
      · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
        simp only [Bool.toNat_true]
        omega

end PvsNP.Units.tf_fun_mul_const_all

theorem PvsNP.Units.tf_fun_mul_const_all :
    ∀ c : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) * c)) := by
  intro c
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hconst := PvsNP.Units.m2_const_polytime (Nat.bits c)
  have hpair := PvsNP.Units.m2_pair_build_polytime _ _ hid hconst
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, Nat.bits c))
    (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    hpair PvsNP.Units.tf_fun_pair_mul
  have heq :
      ((fun p : List Bool × List Bool =>
          Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) ∘
        (fun x : List Bool => (x, Nat.bits c))) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) * c)) := by
    funext x
    simp only [Function.comp_apply]
    change Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) * PvsNP.Units.tf_fun_mul_const_all.val (Nat.bits c)) = _
    rw [PvsNP.Units.tf_fun_mul_const_all.val_bits]
  rwa [heq] at hcomp
