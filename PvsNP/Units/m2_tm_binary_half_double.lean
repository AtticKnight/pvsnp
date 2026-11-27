import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime

namespace PvsNP.Units.m2_tm_binary_half_double

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def dropFalseD : Bool → Bool → Bool × Option Bool
  | false, false => (false, none)
  | false, true => (true, some true)
  | true, b => (true, some b)

def dropLeadingFalse (l : List Bool) : List Bool :=
  fstRun dropFalseD (fun _ => none) false l

theorem dropLeadingFalse_eq (l : List Bool) :
    dropLeadingFalse l = l.dropWhile (fun b => !b) := by
  have htrue : ∀ t : List Bool, fstRun dropFalseD (fun _ => none) true t = t := by
    intro t; induction t with | nil => rfl | cons b ts ih => simp [fstRun, dropFalseD, ih]
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simpa [dropLeadingFalse, fstRun, dropFalseD] using ih
    · simp [dropLeadingFalse, fstRun, dropFalseD, htrue]

theorem cpt_dropLeadingFalse :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropLeadingFalse :=
  fst_polyTime _ _ _ dropFalseD (fun _ => none) false (fun _ => rfl)

def stripLSB (l : List Bool) : List Bool :=
  (dropLeadingFalse l.reverse).reverse

theorem cptE {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_stripLSB :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stripLSB := by
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  exact cptE (cpt_comp (cpt_comp hRev cpt_dropLeadingFalse) hRev) (fun _ => rfl)

def val (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits]

theorem val_append_false (l : List Bool) : val (l ++ [false]) = val l := by
  induction l with
  | nil => rfl
  | cons b t ih => simp [val_cons, ih]

theorem val_stripLSB (l : List Bool) : val (stripLSB l) = val l := by
  have hrev : ∀ r : List Bool, val (dropLeadingFalse r).reverse = val r.reverse := by
    intro r
    rw [dropLeadingFalse_eq]
    induction r with
    | nil => rfl
    | cons b t ih =>
      cases b
      · simp only [List.dropWhile_cons, Bool.not_false, ↓reduceIte, List.reverse_cons]
        rw [ih, val_append_false]
      · simp [List.dropWhile_cons]
  simpa [stripLSB] using hrev l.reverse

theorem dropWhile_append_nil {α : Type} (p : α → Bool) (r : List α) (x : α)
    (hr : r.dropWhile p = []) (hx : p x = true) : (r ++ [x]).dropWhile p = [] := by
  induction r with
  | nil => simp [hx]
  | cons u us ih =>
    by_cases h : p u = true
    · simp only [List.dropWhile_cons, h, ↓reduceIte] at hr
      simp only [List.cons_append, List.dropWhile_cons, h, ↓reduceIte]
      exact ih hr
    · simp [List.dropWhile_cons, h] at hr

theorem dropWhile_append_cons {α : Type} (p : α → Bool) (r : List α) (x : α)
    (hr : r.dropWhile p = [] → p x = false) :
    (r ++ [x]).dropWhile p = r.dropWhile p ++ [x] := by
  induction r with
  | nil => simp [hr rfl]
  | cons u us ih =>
    by_cases h : p u = true
    · simp only [List.cons_append, List.dropWhile_cons, h, ↓reduceIte]
      refine ih (fun h' => hr ?_)
      simp [List.dropWhile_cons, h, h']
    · simp [List.cons_append, List.dropWhile_cons, h]

theorem stripLSB_eq_bits (l : List Bool) : stripLSB l = Nat.bits (val l) := by
  have ht_false : ∀ m : List Bool, val m = 0 → m.reverse.dropWhile (fun x => !x) = [] := by
    intro m hm; induction m with
    | nil => rfl
    | cons u us ihu =>
      cases u
      · have hus : val us = 0 := by simp [val_cons] at hm; exact hm
        simp only [List.reverse_cons]
        exact dropWhile_append_nil _ _ _ (ihu hus) rfl
      · simp [val_cons] at hm
  have hgen : ∀ (n : ℕ) (l : List Bool), val l = n → stripLSB l = Nat.bits n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro l hl
      cases l with
      | nil =>
        simp [val_nil] at hl
        subst hl; rfl
      | cons b t =>
        by_cases h0 : val (b :: t) = 0
        · have hb : b = false := by
            cases b
            · rfl
            · simp [val_cons] at h0
          have ht : val t = 0 := by simp [val_cons, hb] at h0; exact h0
          have htf2 := dropWhile_append_nil (fun x => !x) t.reverse false (ht_false t ht) rfl
          simp only [stripLSB, dropLeadingFalse_eq, List.reverse_cons, hb, htf2, List.reverse_nil]
          rw [← hl, h0]; rfl
        · have hlt : val t < n := by
            rw [val_cons] at h0
            rw [← hl, val_cons]
            cases b <;> simp at h0 ⊢ <;> omega
          have hst := ih (val t) hlt t rfl
          have hbit : n = Nat.bit b (val t) := by
            rw [← hl, val_cons, Nat.bit_val]
            cases b <;> simp <;> omega
          rw [hbit, Nat.bits_append_bit (val t) b (fun hvt => by
            cases b
            · exfalso; simp [hvt, val_cons] at hl h0
            · rfl)]
          rw [← hst]
          simp only [stripLSB, dropLeadingFalse_eq, List.reverse_cons]
          have happ : (t.reverse ++ [b]).dropWhile (fun x => !x) =
              t.reverse.dropWhile (fun x => !x) ++ [b] := by
            refine dropWhile_append_cons (fun x => !x) t.reverse b (fun he => ?_)
            cases b
            · exfalso
              have ht0 : val t = 0 := by
                have hst' : stripLSB t = [] := by simp [stripLSB, dropLeadingFalse_eq, he]
                rw [← val_stripLSB t, hst']; rfl
              simp [val_cons, ht0] at h0
            · rfl
          simp [happ]
  exact hgen (val l) l rfl

theorem tail_bits_eq (n : ℕ) : (Nat.bits n).tail = Nat.bits (n / 2) := by
  by_cases hn : n = 0
  · simp [hn]
  · conv_lhs => rw [← Nat.div_add_mod n 2]
    by_cases hm : n % 2 = 0
    · have hn2 : n / 2 ≠ 0 := by omega
      rw [hm, add_zero, Nat.bit0_bits _ hn2, List.tail_cons]
    · have hm1 : n % 2 = 1 := by omega
      rw [hm1, Nat.bit1_bits, List.tail_cons]

theorem double_bits_eq (n : ℕ) :
    sel (Nat.bits n) [] (false :: Nat.bits n) = Nat.bits (2 * n) := by
  by_cases hn : n = 0
  · simp [hn, sel]
  · have hne : Nat.bits n ≠ [] := by
      intro h
      have := congrArg List.length h
      conv_lhs at this => rw [← Nat.div_add_mod n 2]
      by_cases hm : n % 2 = 0
      · have hn2 : n / 2 ≠ 0 := by omega
        rw [hm, add_zero, Nat.bit0_bits _ hn2] at this; simp at this
      · have hm1 : n % 2 = 1 := by omega
        rw [hm1, Nat.bit1_bits] at this; simp at this
    simp [sel, hne, Nat.bit0_bits _ hn]

end PvsNP.Units.m2_tm_binary_half_double

theorem PvsNP.Units.m2_tm_binary_half_double :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) / 2)) ∧
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))) := by
  constructor
  · have hHalf := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail
    refine PvsNP.Units.m2_tm_binary_half_double.cptE hHalf (fun x => ?_)
    simp only [Function.comp_apply, PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits,
      PvsNP.Units.m2_tm_binary_half_double.tail_bits_eq]
    rfl
  · have hDbl := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_sel
      PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_cons1 false
        PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB)
    refine PvsNP.Units.m2_tm_binary_half_double.cptE hDbl (fun x => ?_)
    simp only [PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits,
      PvsNP.Units.m2_tm_binary_half_double.double_bits_eq]
    rfl
