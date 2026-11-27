import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_eq_polytime

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_reverse_polytime and
PvsNP.Units.m2_eq_polytime of github.com/makedotfun/pvsnp (Apache License 2.0), which this file
imports: their machines are those of github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0), and of that unit's author.
-/

namespace PvsNP.Units.m2_tm_binary_eq

/-- The value of a binary string, least significant digit first. -/
abbrev val (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

/-- Drop the trailing zeros. -/
def strip (l : List Bool) : List Bool := (l.reverse.dropWhile (fun b => !b)).reverse

theorem val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

theorem val_eq_zero (l : List Bool) : val l = 0 ↔ true ∉ l := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    rw [val_cons]
    cases b <;> simp [ih]

theorem dropWhile_append_single (p : Bool → Bool) (b : Bool) : ∀ L : List Bool,
    (L ++ [b]).dropWhile p = if L.all p then (if p b then [] else [b]) else L.dropWhile p ++ [b] := by
  intro L
  induction L with
  | nil => cases h : p b <;> simp [List.dropWhile_cons, h]
  | cons c L ih =>
    cases hc : p c
    · simp [List.dropWhile_cons, hc]
    · simp only [List.cons_append, List.dropWhile_cons, hc, if_true, List.all_cons, Bool.true_and]
      exact ih

theorem all_not_iff (l : List Bool) : (l.reverse.all fun b => !b) = true ↔ true ∉ l := by
  constructor
  · intro h ht
    have := List.all_eq_true.1 h true (List.mem_reverse.2 ht)
    simp at this
  · intro h
    refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.mem_reverse.1 hx
    cases x
    · rfl
    · exact absurd hx' h

theorem strip_cons (b : Bool) (l : List Bool) :
    strip (b :: l) = if true ∉ l ∧ b = false then [] else b :: strip l := by
  unfold strip
  rw [List.reverse_cons, dropWhile_append_single]
  by_cases h : true ∉ l
  · rw [if_pos ((all_not_iff l).2 h)]
    have hd : l.reverse.dropWhile (fun b => !b) = [] := by
      rw [List.dropWhile_eq_nil_iff]
      intro x hx
      have hx' := List.mem_reverse.1 hx
      cases x
      · rfl
      · exact absurd hx' h
    cases b <;> simp [h, hd]
  · rw [if_neg (fun hh => h ((all_not_iff l).1 hh))]
    simp [h]

/-- The binary digits of a string's value are the string without its trailing zeros. -/
theorem bits_val (l : List Bool) : Nat.bits (val l) = strip l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [strip_cons, val_cons]
    by_cases hz : true ∉ l
    · have h0 : val l = 0 := (val_eq_zero l).2 hz
      have hs : strip l = [] := by rw [← ih, h0]; rfl
      cases b <;> simp [hz, h0, hs]
    · have h0 : val l ≠ 0 := fun h => hz ((val_eq_zero l).1 h)
      rw [if_neg (fun h => hz h.1)]
      have e : b.toNat + 2 * val l = Nat.bit b (val l) := by rw [Nat.bit_val]; ring
      rw [e, Nat.bits_append_bit _ _ (fun h => absurd h h0), ih]

/-- Drop the leading zeros: drop while the state says so. -/
def dwD : Bool → Bool → Bool × Option Bool
  | true, b => if b then (false, some true) else (true, none)
  | false, b => (false, some b)

theorem dwRun_keep (l : List Bool) : PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun dwD (fun _ => none) false l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, dwD, ih]

theorem dwRun (l : List Bool) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun dwD (fun _ => none) true l = l.dropWhile (fun b => !b) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, dwD, ih, dwRun_keep, List.dropWhile_cons]

theorem cpt_dw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun l : List Bool => l.dropWhile (fun b => !b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ dwD (fun _ => none)
    true (fun l => (dwRun l).symm)

/-- Stripping trailing zeros is polynomial-time: reverse, drop leading zeros, reverse. -/
theorem cpt_strip : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString strip := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun l : List Bool => (l.reverse.dropWhile (fun b => !b)).reverse) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp PvsNP.Units.m2_reverse_polytime cpt_dw)
      PvsNP.Units.m2_reverse_polytime
  exact h

theorem val_strip (l : List Bool) : val (strip l) = val l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [strip_cons]
    by_cases h : true ∉ l ∧ b = false
    · rw [if_pos h]
      have h0 : val (b :: l) = 0 := by
        rw [val_cons, (val_eq_zero l).2 h.1, h.2]; rfl
      rw [h0]; rfl
    · rw [if_neg h, val_cons, val_cons, ih]

/-- Two strings have the same value exactly when they agree once trailing zeros are dropped. -/
theorem val_eq_iff (a b : List Bool) : val a = val b ↔ strip a = strip b := by
  constructor
  · intro h
    rw [← bits_val, ← bits_val, h]
  · intro h
    rw [← val_strip a, ← val_strip b, h]

end PvsNP.Units.m2_tm_binary_eq

/-- Equality of binary values is polynomial-time (TM2): drop the trailing zeros of both strings
and compare them. -/
theorem PvsNP.Units.m2_tm_binary_eq :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (PvsNP.Units.m2_tm_binary_eq.strip p.1 = PvsNP.Units.m2_tm_binary_eq.strip p.2)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_first PvsNP.Units.m2_tm_binary_eq.cpt_strip)
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_second PvsNP.Units.m2_tm_binary_eq.cpt_strip))
      PvsNP.Units.m2_eq_polytime
  have e : (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) =
      (fun p : List Bool × List Bool =>
        decide (PvsNP.Units.m2_tm_binary_eq.strip p.1 = PvsNP.Units.m2_tm_binary_eq.strip p.2)) := by
    funext p
    exact decide_eq_decide.2 (PvsNP.Units.m2_tm_binary_eq.val_eq_iff p.1 p.2)
  rw [e]
  exact h
