import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_length_eq_value

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def val (x : List Bool) : ℕ := Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · rcases h with ⟨rfl, rfl⟩; simp [val]
    · have hcond : n = 0 → b = true := by intro hn; cases b <;> simp_all
      rw [Nat.bits_append_bit n b hcond, val_cons, ih, Nat.bit_val]
      omega

theorem bits_eq_iff (m n : ℕ) : Nat.bits m = Nat.bits n ↔ m = n := by
  constructor
  · intro h
    have := congrArg val h
    rwa [val_bits, val_bits] at this
  · intro h; rw [h]

def normBin (x : List Bool) : List Bool := Nat.bits (val x + val [])

theorem cpt_normBin : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString normBin :=
  cpt_comp (f := fun x : List Bool => (x, ([] : List Bool)))
    (g := fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime _ _ cpt_id (cpt_const []))
    PvsNP.Units.tf_fun_pair_add

end PvsNP.Units.m2_tm_length_eq_value

theorem PvsNP.Units.m2_tm_length_eq_value :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length = Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (Nat.bits p.1.length, PvsNP.Units.m2_tm_length_eq_value.normBin p.2)) :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => Nat.bits x.length)
      PvsNP.Units.m2_tm_length_eq_value.normBin
      PvsNP.Units.m2_unary_to_binary_polytime
      PvsNP.Units.m2_tm_length_eq_value.cpt_normBin
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.bits p.1.length = PvsNP.Units.m2_tm_length_eq_value.normBin p.2)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hmap PvsNP.Units.m2_eq_polytime
  have heq : (fun p : List Bool × List Bool =>
        decide (Nat.bits p.1.length = PvsNP.Units.m2_tm_length_eq_value.normBin p.2)) =
      (fun p : List Bool × List Bool => decide (p.1.length = Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
    funext p
    have h0 : PvsNP.Units.m2_tm_length_eq_value.val [] = 0 := rfl
    simp only [PvsNP.Units.m2_tm_length_eq_value.normBin, h0, Nat.add_zero]
    exact decide_eq_decide.2 (PvsNP.Units.m2_tm_length_eq_value.bits_eq_iff _ _)
  rw [← heq]
  exact hcomp
