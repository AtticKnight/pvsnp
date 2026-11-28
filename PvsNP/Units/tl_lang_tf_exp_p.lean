import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_bool_combine_polytime

namespace PvsNP.Units.tl_lang_tf_exp_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tr_rel_val_coprime (cpt_eq_fun val val_bits)

private def copies (pick write : Bool) (x : List Bool) := List.replicate (x.count pick) write

private theorem cpt_copies (pick write : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (copies pick write) := by
  let emit : Bool → Option Bool := fun b => if b = pick then some write else none
  have emits (x : List Bool) : copies pick write x = x.filterMap emit := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
      cases pick <;> cases b <;> simp [copies, emit, List.replicate_succ] at ih ⊢ <;> exact ih
  exact filterMap_polyTime _ _ _ emit emits

private def ordered (x : List Bool) := copies true true x ++ copies false false x
private def expected (x : List Bool) := copies true false x ++ [true]

/-- Binary digits are written least significant first. The representation of the power
has length n + 1, so the decision procedure never writes an exponentially long string. -/
private theorem bits_pow_two (n : ℕ) : Nat.bits (2 ^ n) = List.replicate n false ++ [true] := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.bit0_bits _ (by positivity), ih,
      List.replicate_succ]
    rfl

private def falseBits (x : List Bool) := Nat.bits (x.count false)

private theorem verify :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => decide (x = ordered x) && decide (falseBits x = expected x)) := by
  have orderCheck := cpt_eq_fun id ordered cpt_id (cpt_app2 (cpt_copies true true) (cpt_copies false false))
  have hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString falseBits := by
    have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (copies false false) (fun s : List Bool => s.length.bits)
      (cpt_copies false false) PvsNP.Units.m2_unary_to_binary_polytime
    have eqf : (fun s : List Bool => s.length.bits) ∘ copies false false = falseBits := by
      funext x
      simp [Function.comp_def, falseBits, copies]
    rwa [eqf] at h
  have bitsCheck := cpt_eq_fun falseBits expected hc (cpt_app2 (cpt_copies true false) (cpt_const [true]))
  exact PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ orderCheck bitsCheck

private theorem correct (x : List Bool) :
    (∃ n : ℕ, x = List.replicate n true ++ List.replicate (2 ^ n) false) ↔
      (decide (x = ordered x) && decide (falseBits x = expected x)) = true := by
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨n, rfl⟩
    have noTrue (m : ℕ) : (List.replicate m false).count true = 0 := by
      induction m with
      | zero => rfl
      | succ m ih => simp [List.replicate_succ, ih]
    have noFalse (m : ℕ) : (List.replicate m true).count false = 0 := by
      induction m with
      | zero => rfl
      | succ m ih => simp [List.replicate_succ, ih]
    simp [ordered, expected, falseBits, copies, List.count_append, noTrue, noFalse, bits_pow_two]
  · rintro ⟨order, digits⟩
    have same : Nat.bits (x.count false) = Nat.bits (2 ^ (x.count true)) := by
      simpa [falseBits, expected, copies, bits_pow_two] using digits
    have sizes := congrArg val same
    rw [val_bits, val_bits] at sizes
    exact ⟨x.count true, by simpa only [ordered, copies, sizes] using order⟩

end PvsNP.Units.tl_lang_tf_exp_p

theorem PvsNP.Units.tl_lang_tf_exp_p :
    ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate (2 ^ n) false} :
      Language Bool) ∈ PvsNP.P :=
  ⟨_, PvsNP.Units.tl_lang_tf_exp_p.verify, PvsNP.Units.tl_lang_tf_exp_p.correct⟩
