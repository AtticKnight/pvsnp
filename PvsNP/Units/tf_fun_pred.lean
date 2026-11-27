import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_transducer_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pred

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

def dw (s : Bool) (L : List Bool) : List Bool := if s then L else L.dropWhile (fun b => !b)

theorem dw_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (dw false) :=
  PvsNP.Units.m2_transducer_polytime Bool
    (fun s b => if s || b then (true, some b) else (false, none)) (fun _ => none) dw
    (fun q => by cases q <;> rfl) (fun q b x => by cases q <;> cases b <;> simp [dw]) false

theorem T_eq (L : List Bool) : T L = (dw false L.reverse).reverse := rfl


open PvsNP.Units.fr_ladner.PEqualNP.Library in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
theorem T_poly {g : List Bool → List Bool}
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x => T (g x)) := by
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    g (fun x : List Bool => x.reverse) hg PvsNP.Units.m2_reverse_polytime
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (dw false) h1 dw_poly
  have h3 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (fun x : List Bool => x.reverse) h2 PvsNP.Units.m2_reverse_polytime
  exact h3

theorem val_cons (b : Bool) (L : List Bool) : val (b :: L) = b.toNat + 2 * val L := by
  simp [val, Nat.ofDigits_cons]


def dec : Bool → List Bool → List Bool
  | _, [] => []
  | true, false :: L => true :: dec true L
  | true, true :: L => false :: dec false L
  | false, b :: L => b :: dec false L

def δd (c b : Bool) : Bool × Option Bool :=
  if c then (if b then (false, some false) else (true, some true)) else (false, some b)

theorem dec_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (dec true) :=
  PvsNP.Units.m2_transducer_polytime Bool δd (fun _ => none) dec
    (fun q => by cases q <;> rfl) (fun q b x => by cases q <;> cases b <;> rfl) true

theorem dec_false : ∀ L : List Bool, dec false L = L
  | [] => rfl
  | b :: L => by simp [dec, dec_false L]

theorem dec_val : ∀ L : List Bool, val L ≠ 0 → val (dec true L) = val L - 1
  | [] => by simp [val]
  | false :: L => by
    intro h
    have hv : val L ≠ 0 := by rw [val_cons] at h; simpa using h
    have ih := dec_val L hv
    simp only [dec, val_cons, ih]
    simp; omega
  | true :: L => by
    intro _
    simp only [dec, val_cons, dec_false]
    simp

def cnd (x : List Bool) : Bool := decide ([true].length ≤ (T x).length)

open PvsNP.Units.fr_ladner.PEqualNP.Library in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
theorem main : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) - 1)) := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) := by
    have h := cpt_id; exact h
  have hT : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x => T x) := by
    have h := T_poly hid; exact h
  have hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer cnd := by
    have h := cpt_comp (cpt_pair (cpt_const [true]) hT) PvsNP.Units.m2_len_le_polytime
    exact h
  have hd := T_poly dec_poly
  have hz : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun _ => []) :=
    cpt_const []
  have h := PvsNP.Units.m2_ite_polytime cnd (fun x => T (dec true x)) (fun _ => []) hc hd hz
  have hfun : (fun x : List Bool => if cnd x = true then T (dec true x) else []) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) - 1)) := by
    funext x
    show _ = Nat.bits (val x - 1)
    by_cases h0 : val x = 0
    · have hTx : T x = [] := by rw [← bits_val, h0, Nat.zero_bits]
      have : cnd x = false := by simp [cnd, hTx]
      rw [this, h0]; simp [Nat.zero_bits]
    · have hTx : T x ≠ [] := by rw [← bits_val]; exact bits_ne _ h0
      have : cnd x = true := by
        simp only [cnd, List.length_singleton, decide_eq_true_eq]
        exact List.length_pos_iff.mpr hTx
      rw [this, if_pos rfl, ← bits_val, dec_val x h0]
  rw [← hfun]; exact h

end PvsNP.Units.tf_fun_pred

theorem PvsNP.Units.tf_fun_pred :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) - 1)) :=
  PvsNP.Units.tf_fun_pred.main
