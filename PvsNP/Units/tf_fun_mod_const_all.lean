import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tl_lang_val_pow_p
import PvsNP.Units.tf_fun_pair_mod

namespace PvsNP.Units.tf_fun_mod_const_all

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tl_lang_val_pow_p

theorem main_proof (c : ℕ) : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (val x % c)) := by
  have hp := fromCptPair (cpt_pair cpt_id (cpt_const (Nat.bits c)))
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (x, Nat.bits c))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 % val p.2))
      hp PvsNP.Units.tf_fun_pair_mod
  have e : ((fun p : List Bool × List Bool => Nat.bits (val p.1 % val p.2)) ∘
      (fun x : List Bool => (x, Nat.bits c))) = (fun x : List Bool => Nat.bits (val x % c)) := by
    funext x
    simp only [Function.comp, val_bits]
  rw [e] at h
  exact h

end PvsNP.Units.tf_fun_mod_const_all

theorem PvsNP.Units.tf_fun_mod_const_all : ∀ c : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % c)) :=
  PvsNP.Units.tf_fun_mod_const_all.main_proof
