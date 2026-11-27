import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines (fstRun fst_polyTime cpt_id)
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal (cpt_const cpt_iterGrow)

namespace PvsNP.Units.m2_unary_to_binary_polytime

private def incD (carry b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

private def incFin (carry : Bool) : Option Bool :=
  if carry then some true else none

private def incBits : List Bool → List Bool := fstRun incD incFin true

private theorem run_no_carry (s : List Bool) : fstRun incD incFin false s = s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [fstRun, incD, ih]

private theorem incBits_succ (n : ℕ) : incBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [incBits, fstRun, incFin]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b with
    | false =>
      have hs : Nat.bit false n + 1 = Nat.bit true n := by simp [Nat.bit_val]
      rw [hs, Nat.bits_append_bit n true (fun _ => rfl)]
      simp [incBits, fstRun, incD, run_no_carry]
    | true =>
      have hs : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
        simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false]
        omega
      rw [hs, Nat.bits_append_bit (n + 1) false (by omega)]
      simpa [incBits, fstRun, incD] using ih

-- This length bound follows `succD_length` in the settled unit `fr_ladner`,
-- adapted from brilliant-hq/pequalnp-proofs at 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache-2.0).
private theorem run_length (s : List Bool) (carry : Bool) :
    (fstRun incD incFin carry s).length ≤ s.length + 1 := by
  induction s generalizing carry with
  | nil => cases carry <;> decide
  | cons b s ih =>
    have hFalse := ih false
    have hTrue := ih true
    cases carry <;> cases b <;> simp [fstRun, incD] <;> omega

private theorem iterate_incBits (n : ℕ) : (incBits^[n]) [] = n.bits := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, incBits_succ]

end PvsNP.Units.m2_unary_to_binary_polytime

/-- Count the input symbols by iterating a least-significant-bit-first binary increment. -/
theorem PvsNP.Units.m2_unary_to_binary_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits x.length) :=
  open PvsNP.Units.m2_unary_to_binary_polytime in
  by
    have hInc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString incBits :=
      fst_polyTime _ _ _ incD incFin true (fun _ => rfl)
    have hIter := cpt_iterGrow hInc 1 (fun s => run_length s true) cpt_id (cpt_const [])
    have hEq : (fun x : List Bool => (incBits^[x.length]) []) =
        (fun x : List Bool => Nat.bits x.length) := funext (fun x => iterate_incBits x.length)
    rw [← hEq]
    exact hIter
