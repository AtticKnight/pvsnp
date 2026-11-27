import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tr_rel_val_coprime

/-- Compare before subtracting canonical inputs so that natural subtraction saturates at zero. -/
theorem PvsNP.Units.tf_fun_pair_sub :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  let first := fun s : List Bool => (unpairB s).1
  let second := fun s : List Bool => (unpairB s).2
  have ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString first :=
    cpt_unpairB1_1 cpt_id
  have hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString second :=
    cpt_unpairB2_1 cpt_id
  let evalSub := fun s : List Bool =>
    if decide (val (second s) ≤ val (first s)) = true
    then binSub (canon (first s)) (canon (second s))
    else []
  have hrun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString evalSub :=
    PvsNP.Units.m2_ite_polytime _ _ _ (cpt_binLe_fun _ _ hb ha)
      (cpt_binSub_fun _ _ (cpt_binAdd_fun _ _ ha (cpt_const []))
        (cpt_binAdd_fun _ _ hb (cpt_const []))) (cpt_const [])
  have hp := PvsNP.Units.m2_pair_build_polytime.cpt_comp
    (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := evalSub) cpt_pairB hrun
  have heq : (fun p : List Bool × List Bool => evalSub (pairB p.1 p.2)) =
      (fun p : List Bool × List Bool => Nat.bits (val p.1 - val p.2)) := by
    funext p
    simp only [evalSub, first, second, unpairB_pairB, canon_eq, decide_eq_true_eq]
    by_cases h : val p.2 ≤ val p.1
    · simpa only [if_pos h] using binSub_eq h
    · have zero : val p.1 - val p.2 = 0 := by omega
      simp [h, zero]
  rw [heq] at hp
  exact hp
