import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tr_rel_val_power_of

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_base_pow_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem cpt_pair3 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
    (fun x : List Bool => (([true, true] : List Bool), x)) := by
  have h : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun x : List Bool => (([true, true] : List Bool), x)) :=
    cpt_pairG (cpt_const [true, true]) cpt_id
  exact h

theorem main :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 3 ^ k} :
      Language Bool) ∈ PvsNP.P := by
  obtain ⟨f, hf, hfx⟩ := PvsNP.Units.tr_rel_val_power_of
  refine ⟨f ∘ (fun x : List Bool => (([true, true] : List Bool), x)), ?_, ?_⟩
  · exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      _ f cpt_pair3 hf
  · intro x
    have e := hfx (([true, true] : List Bool), x)
    have h3 : Nat.ofDigits (2 : ℕ) (([true, true] : List Bool).map Bool.toNat) = 3 := by
      norm_num [Nat.ofDigits]
    rw [h3] at e
    exact e

end PvsNP.Units.tl_lang_val_base_pow_p

theorem PvsNP.Units.tl_lang_val_base_pow_p :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 3 ^ k} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_base_pow_p.main
