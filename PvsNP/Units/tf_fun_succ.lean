import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_succ

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def val (L : List Bool) : ℕ := Nat.ofDigits 2 (L.map Bool.toNat)

theorem bits_ne (n : ℕ) (h : n ≠ 0) : Nat.bits n ≠ [] := by
  have e := Nat.div_add_mod n 2
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rw [h2, add_zero] at e
    have h' : n / 2 ≠ 0 := by omega
    rw [← e, Nat.bit0_bits _ h']
    simp
  · rw [h2] at e
    rw [← e, Nat.bit1_bits]
    simp

def T (L : List Bool) : List Bool := (L.reverse.dropWhile (fun b => !b)).reverse

theorem bits_val : ∀ L : List Bool, Nat.bits (val L) = T L
  | [] => by simp [val, T, Nat.zero_bits]
  | b :: L => by
    have ih := bits_val L
    have hv : val (b :: L) = b.toNat + 2 * val L := by
      simp [val, Nat.ofDigits_cons]
    have hT : T (b :: L) = if (L.reverse.dropWhile (fun b => !b)).isEmpty
        then ([b].dropWhile (fun b => !b)).reverse
        else b :: T L := by
      unfold T
      rw [List.reverse_cons, List.dropWhile_append]
      split
      · rfl
      · simp
    rw [hv, hT]
    by_cases h0 : val L = 0
    · have hE : (L.reverse.dropWhile (fun b => !b)).isEmpty = true := by
        rw [h0, Nat.zero_bits] at ih
        unfold T at ih
        have : L.reverse.dropWhile (fun b => !b) = [] := by
          have := congrArg List.reverse ih
          simpa using this.symm
        rw [this]; rfl
      rw [if_pos hE, h0]
      cases b
      · simp [Nat.zero_bits]
      · simp
    · have hE : (L.reverse.dropWhile (fun b => !b)).isEmpty = false := by
        have hne : Nat.bits (val L) ≠ [] := bits_ne (val L) h0
        rw [ih] at hne
        unfold T at hne
        cases hd : L.reverse.dropWhile (fun b => !b) with
        | nil => rw [hd] at hne; exact absurd rfl hne
        | cons _ _ => rfl
      rw [if_neg (by simp [hE]), ← ih]
      cases b
      · simpa using Nat.bit0_bits (val L) h0
      · show (1 + 2 * val L).bits = _
        rw [add_comm]; exact Nat.bit1_bits _

def inc : Bool → List Bool → List Bool
  | true, [] => [true]
  | false, [] => []
  | true, true :: L => false :: inc true L
  | true, false :: L => true :: inc false L
  | false, b :: L => b :: inc false L

def δi (c b : Bool) : Bool × Option Bool :=
  if c then (if b then (true, some false) else (false, some true)) else (false, some b)

theorem inc_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (inc true) :=
  PvsNP.Units.m2_transducer_polytime Bool δi (fun c => if c then some true else none) inc
    (fun q => by cases q <;> rfl) (fun q b x => by cases q <;> cases b <;> rfl) true

theorem inc_val : ∀ (c : Bool) (L : List Bool), val (inc c L) = val L + c.toNat
  | true, [] => rfl
  | false, [] => rfl
  | true, true :: L => by
    have := inc_val true L
    simp only [inc, val, List.map_cons, Nat.ofDigits_cons] at this ⊢
    simp at this ⊢
    omega
  | true, false :: L => by
    have := inc_val false L
    simp only [inc, val, List.map_cons, Nat.ofDigits_cons] at this ⊢
    simp at this ⊢
    omega
  | false, b :: L => by
    have := inc_val false L
    simp only [inc, val, List.map_cons, Nat.ofDigits_cons] at this ⊢
    simp at this ⊢
    omega

def dw (s : Bool) (L : List Bool) : List Bool := if s then L else L.dropWhile (fun b => !b)

theorem dw_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (dw false) :=
  PvsNP.Units.m2_transducer_polytime Bool
    (fun s b => if s || b then (true, some b) else (false, none)) (fun _ => none) dw
    (fun q => by cases q <;> rfl) (fun q b x => by cases q <;> cases b <;> simp [dw]) false

theorem T_eq (L : List Bool) : T L = (dw false L.reverse).reverse := rfl

theorem main : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) := by
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (inc true) (fun x : List Bool => x.reverse) inc_poly PvsNP.Units.m2_reverse_polytime
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (dw false) h1 dw_poly
  have h3 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (fun x : List Bool => x.reverse) h2 PvsNP.Units.m2_reverse_polytime
  have hfun : ((fun x : List Bool => x.reverse) ∘ (dw false ∘ ((fun x : List Bool => x.reverse) ∘ inc true))) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) := by
    funext x
    show (dw false (inc true x).reverse).reverse = _
    rw [← T_eq, ← bits_val, inc_val]
    rfl
  rw [← hfun]
  exact h3

end PvsNP.Units.tf_fun_succ

theorem PvsNP.Units.tf_fun_succ :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 1)) :=
  PvsNP.Units.tf_fun_succ.main
