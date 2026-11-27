import Mathlib
import PvsNP.Defs
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_binary_lt
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union
import PvsNP.Units.tl_lang_composite_np

namespace PvsNP.Units.m2_x_prime_conp

open PvsNP.Units.tl_lang_composite_np (val)
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem nonprime_iff (n : ℕ) :
    ¬ n.Prime ↔ (¬ 1 < n) ∨ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  constructor
  · intro hn
    by_cases h : 1 < n
    · right
      obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ n)).1 hn
      have da : 1 < a := by
        by_contra hsmall
        have h01 : a = 0 ∨ a = 1 := by omega
        rcases h01 with rfl | rfl <;> simp_all
      have db : 1 < b := by
        by_contra hsmall
        have h01 : b = 0 ∨ b = 1 := by omega
        rcases h01 with rfl | rfl <;> simp_all
      exact ⟨a, b, da, db, hab⟩
    · exact Or.inl h
  · rintro (small | ⟨a, b, ha, hb, hab⟩) hp
    · exact small hp.one_lt
    · have divides : a ∣ n := ⟨b, hab.symm⟩
      have proper : a < a * b := calc
        a = a * 1 := (Nat.mul_one a).symm
        _ < a * b := Nat.mul_lt_mul_of_pos_left hb (by omega)
      rcases hp.eq_one_or_self_of_dvd a divides with h | h <;> omega

private theorem above_one :
    ({x : List Bool | 1 < val x} : Language Bool) ∈ PvsNP.P := by
  have pair := m2_pair_build_polytime (fun _ => [true]) (fun x => x) (m2_const_polytime [true]) cpt_id
  have decider : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (1 < val x)) :=
    m2_polytime_comp _ _ _ (fun x : List Bool => ([true], x))
      (fun p : List Bool × List Bool => decide (val p.1 < val p.2)) pair m2_tm_binary_lt
  exact ⟨_, decider, fun x => by simp⟩

/-- Reject the encodings of zero and one separately; the remaining nonprimes
have the ordinary composite certificates. -/
theorem prime_class : ({x : List Bool | (val x).Prime} : Language Bool) ∈ PvsNP.coNP := by
  let large : Language Bool := {x | 1 < val x}
  let comp : Language Bool := {x | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = val x}
  have equality : ({x : List Bool | (val x).Prime} : Language Bool)ᶜ = largeᶜ ⊔ comp := by
    ext x
    exact nonprime_iff (val x)
  change ({x : List Bool | (val x).Prime} : Language Bool)ᶜ ∈ PvsNP.NP
  rw [equality]
  exact m2_np_union _ _ (m2_p_subset_np (m2_p_compl large above_one)) tl_lang_composite_np

end PvsNP.Units.m2_x_prime_conp

theorem PvsNP.Units.m2_x_prime_conp :
    ({x : List Bool | Nat.Prime (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))} : Language Bool) ∈
      PvsNP.coNP :=
  PvsNP.Units.m2_x_prime_conp.prime_class
