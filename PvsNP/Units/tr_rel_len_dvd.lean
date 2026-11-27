import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_unary_divmod
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

theorem PvsNP.Units.tr_rel_len_dvd :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
        ∀ p : List Bool × List Bool, (p.1.length ∣ p.2.length) ↔ f p = true := by
  have hmod := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.2, p.1))
    (fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true)
    PvsNP.Units.m2_tm_pair_swap_polytime
    PvsNP.Units.m2_tm_unary_divmod.2
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair := PvsNP.Units.m2_pair_build_polytime id (fun _ => ([] : List Bool))
    hid (PvsNP.Units.m2_const_polytime [])
  have hisNil := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x : List Bool => (x, ([] : List Bool)))
    (fun p : List Bool × List Bool => decide (p.1 = p.2))
    hpair PvsNP.Units.m2_eq_polytime
  have hf := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
    _ _ hmod hisNil
  refine ⟨_, hf, fun p => ?_⟩
  show (p.1.length ∣ p.2.length) ↔ decide (List.replicate (p.2.length % p.1.length) true = []) = true
  rw [decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
  cases p.2.length % p.1.length <;> simp
