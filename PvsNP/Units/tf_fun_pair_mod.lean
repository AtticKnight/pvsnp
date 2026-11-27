import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tr_rel_val_dvd
import PvsNP.Units.tf_fun_pair_mul

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_mod

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

lemma encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

def modRaw (s : List Bool) : List Bool :=
  if PvsNP.Units.tr_rel_val_dvd.allFalse (unpairB s).1 = true then
    (unpairB s).2.reverse
  else
    PvsNP.Units.tr_rel_val_dvd.remOf s

def pairMod (p : List Bool × List Bool) : List Bool :=
  PvsNP.Units.tf_fun_pair_mul.stripLSB (modRaw (pairB p.2 p.1.reverse))

lemma pairMod_eq (p : List Bool × List Bool) :
    pairMod p =
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) %
        Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) := by
  rcases p with ⟨x, d⟩
  change PvsNP.Units.tf_fun_pair_mul.stripLSB (modRaw (pairB d x.reverse)) =
    Nat.bits (PvsNP.Units.tr_rel_val_dvd.val x % PvsNP.Units.tr_rel_val_dvd.val d)
  by_cases hd0 : PvsNP.Units.tr_rel_val_dvd.val d = 0
  · have hafd : PvsNP.Units.tr_rel_val_dvd.allFalse d = true :=
      (PvsNP.Units.tr_rel_val_dvd.allFalse_iff_val_eq_zero d).mpr hd0
    have hmod : modRaw (pairB d x.reverse) = x := by
      simp [modRaw, unpairB_pairB, hafd]
    rw [hmod, hd0, Nat.mod_zero]
    exact PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits x
  · have hdpos : 0 < PvsNP.Units.tr_rel_val_dvd.val d := Nat.pos_of_ne_zero hd0
    have hafd : PvsNP.Units.tr_rel_val_dvd.allFalse d = false :=
      Bool.eq_false_iff.mpr fun h =>
        hd0 ((PvsNP.Units.tr_rel_val_dvd.allFalse_iff_val_eq_zero d).mp h)
    have hmod : modRaw (pairB d x.reverse) = PvsNP.Units.tr_rel_val_dvd.remOf (pairB d x.reverse) := by
      simp [modRaw, unpairB_pairB, hafd]
    obtain ⟨r', hrun, hvalr', _⟩ :=
      PvsNP.Units.tr_rel_val_dvd.divStep_iter d hdpos x.reverse [] []
        (by simpa [PvsNP.Units.tr_rel_val_dvd.val_nil])
    simp only [List.append_nil, List.reverse_reverse, PvsNP.Units.tr_rel_val_dvd.val_nil,
      Nat.zero_mul, Nat.zero_add] at hrun hvalr'
    have hrem_eq : PvsNP.Units.tr_rel_val_dvd.remOf (pairB d x.reverse) = r' := by
      simp only [PvsNP.Units.tr_rel_val_dvd.remOf, unpairB_pairB, hrun]
    rw [hmod, hrem_eq]
    have hbits : PvsNP.Units.tf_fun_pair_mul.stripLSB r' =
        Nat.bits (PvsNP.Units.tr_rel_val_dvd.val r') :=
      PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits r'
    rw [hbits, hvalr']

theorem main_proof :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) %
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  obtain ⟨cd⟩ := PvsNP.Units.tr_rel_val_dvd.divStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        PvsNP.Units.tr_rel_val_dvd.divStep^[p.2.length] p.1) :=
    Iter.iter_polyTime PvsNP.Units.tr_rel_val_dvd.divStep cd 5
      PvsNP.Units.tr_rel_val_dvd.divStep_len
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => pairB s []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hrem : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.tr_rel_val_dvd.remOf :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit cpt_unpairB2) hiter)
  have hzeroD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool => PvsNP.Units.tr_rel_val_dvd.allFalse (unpairB s).1) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => (unpairB s).1) PvsNP.Units.tr_rel_val_dvd.allFalse
      cpt_unpairB1 PvsNP.Units.tr_rel_val_dvd.allFalse_poly
  have hsndRev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).2.reverse) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2) List.reverse
      cpt_unpairB2 PvsNP.Units.m2_reverse_polytime
  have hmodRaw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString modRaw :=
    PvsNP.Units.m2_ite_polytime _ _ _ hzeroD hsndRev hrem
  have hmodStrip : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => PvsNP.Units.tf_fun_pair_mul.stripLSB (modRaw s)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      modRaw PvsNP.Units.tf_fun_pair_mul.stripLSB
      hmodRaw PvsNP.Units.tf_fun_pair_mul.cpt_stripLSB
  have hpbSwap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.2 p.1.reverse) := by
    rw [← encodePair_eq]
    have hx : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
        PvsNP.encodeString (fun p : List Bool × List Bool => p.1) := cpt_fst
    have hy : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
        PvsNP.encodeString (fun p : List Bool × List Bool => p.2) := cpt_snd
    have hxRev : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
        PvsNP.encodeString (fun p : List Bool × List Bool => p.1.reverse) :=
      cpt_comp hx PvsNP.Units.m2_reverse_polytime
    exact cpt_comp (cpt_pairG hy hxRev) cpt_pairB
  have hpairMod : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString pairMod :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.2 p.1.reverse)
      (fun s : List Bool => PvsNP.Units.tf_fun_pair_mul.stripLSB (modRaw s))
      hpbSwap hmodStrip
  have hfun : pairMod = (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) %
        Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
    funext pairMod_eq
  rwa [hfun] at hpairMod

end PvsNP.Units.tf_fun_pair_mod

theorem PvsNP.Units.tf_fun_pair_mod :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) %
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_pair_mod.main_proof
