import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_pair_mul

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_binary_shift_left

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tf_fun_pair_mul

def toFalsesD (_ : Unit) (_ : Bool) : Unit × Option Bool :=
  ((), some false)

def toFalses (l : List Bool) : List Bool :=
  fstRun toFalsesD (fun _ => none) () l

theorem toFalses_eq (l : List Bool) : toFalses l = List.replicate l.length false := by
  dsimp [toFalses]
  induction l with
  | nil => rfl
  | cons _ t ih => simp [fstRun, toFalsesD, ih, List.replicate_succ]

theorem val_replicate_false_append (k : ℕ) (x : List Bool) :
    val (List.replicate k false ++ x) = val x * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, val_cons, Bool.toNat_false, zero_add,
      ih, pow_succ]
    ring

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * 2 ^ p.2.length)) := by
  have hx : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.1) := cpt_fst
  have hy : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.2) := cpt_snd
  have hF : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) toFalses :=
    fst_polyTime _ _ _ toFalsesD (fun _ => none) () (fun _ => rfl)
  have hApp := cpt_comp (cpt_pairG (cpt_comp hy hF) hx) cpt_append
  have hOut := cpt_comp hApp cpt_stripLSB
  refine cptE hOut ?_
  rintro ⟨x, y⟩
  change stripLSB (toFalses y ++ x) = Nat.bits (val x * 2 ^ y.length)
  rw [toFalses_eq, stripLSB_eq_bits, val_replicate_false_append]

end PvsNP.Units.m2_tm_binary_shift_left

theorem PvsNP.Units.m2_tm_binary_shift_left :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * 2 ^ p.2.length)) :=
  PvsNP.Units.m2_tm_binary_shift_left.main
