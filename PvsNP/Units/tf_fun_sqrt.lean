import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_val_pow_p
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.tf_fun_pred

namespace PvsNP.Units.tf_fun_sqrt

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tl_lang_val_pow_p

theorem rFinal_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rFinal := by
  obtain ⟨cs⟩ := sqrtStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => sqrtStep^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure sqrtStep cs sqrtMeasure 4
      sqrtMeasure_step sqrtStep_len sqrtMeasure_linear
  have hpow2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pow2List x.length) :=
    cpt_app2 cpt_zeros (cpt_const [true])
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pairB (pairB x (pow2List x.length)) []) :=
    cpt_pairB2 (cpt_pairB2 cpt_id hpow2) (cpt_const [])
  exact cpt_unpairB2_1
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      _ _ (cpt_pair hinit hpow2) hiter)

theorem rFinal_val (x : List Bool) : val (rFinal x) = Nat.sqrt (val x) := by
  have hhi0 : val x < (val [] + 2 ^ (x.length + 1)) * (val [] + 2 ^ (x.length + 1)) := by
    have hlt := val_lt_two_pow x
    have h1 : 2 ^ x.length ≤ 2 ^ (x.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (x.length + 1) ≤ 2 ^ (x.length + 1) * 2 ^ (x.length + 1) := Nat.le_mul_self _
    simp only [val_nil, Nat.zero_add]
    omega
  have hres := sqrtStep_iter x x.length [] (by simp [val_nil]) hhi0
  have hrf_lo : val (rFinal x) * val (rFinal x) ≤ val x := by
    simpa [rFinal, pow2List_length] using hres.1
  have hrf_hi : val x < (val (rFinal x) + 1) * (val (rFinal x) + 1) := by
    simpa [rFinal, pow2List_length] using hres.2
  exact Nat.eq_sqrt.mpr ⟨hrf_lo, hrf_hi⟩

theorem norm : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (val x)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (val x + 1)) (fun x : List Bool => Nat.bits (val x - 1))
    PvsNP.Units.tf_fun_succ PvsNP.Units.tf_fun_pred
  have e : ((fun x : List Bool => Nat.bits (val x - 1)) ∘ (fun x : List Bool => Nat.bits (val x + 1)))
      = (fun x : List Bool => Nat.bits (val x)) := by
    funext x
    simp [Function.comp, val_bits]
  rw [e] at h
  exact h

theorem main_proof : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (Nat.sqrt (val x))) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    rFinal (fun x : List Bool => Nat.bits (val x)) rFinal_poly norm
  have e : ((fun x : List Bool => Nat.bits (val x)) ∘ rFinal) =
      (fun x : List Bool => Nat.bits (Nat.sqrt (val x))) := by
    funext x
    simp [Function.comp, rFinal_val]
  rw [e] at h
  exact h

end PvsNP.Units.tf_fun_sqrt

theorem PvsNP.Units.tf_fun_sqrt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (Nat.sqrt (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)))) :=
  PvsNP.Units.tf_fun_sqrt.main_proof
