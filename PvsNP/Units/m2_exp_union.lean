import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_union

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_union

open Turing

def orInTime (f1 f2 : List Bool → Bool)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => f1 x || f2 x) where
  tm := PvsNP.Units.m2_p_union.unionTM c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => 2 * n + 4 + c1.time n + c2.time n
  outputsFun x := by
    have r1 := c1.outputsFun x
    have r2 := c2.outputsFun x
    have hrun := PvsNP.Units.m2_p_union.union_run c1.tm c2.tm
      c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet x
      (c1.outputAlphabet.invFun (f1 x)) (c2.outputAlphabet.invFun (f2 x))
      r1.steps r2.steps r1.evals_in_steps r2.evals_in_steps
    have ho1 : c1.outputAlphabet (c1.outputAlphabet.invFun (f1 x)) = f1 x :=
      c1.outputAlphabet.right_inv (f1 x)
    have ho2 : c2.outputAlphabet (c2.outputAlphabet.invFun (f2 x)) = f2 x :=
      c2.outputAlphabet.right_inv (f2 x)
    rw [ho1, ho2] at hrun
    refine ⟨⟨1 + (r2.steps + (1 + (r1.steps + ((x.length + 1) + (x.length + 1))))), ?_⟩, ?_⟩
    · have hid : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := List.map_id x
      rw [hid]
      exact hrun
    · have b1 := r1.steps_le_m
      have b2 := r2.steps_le_m
      have hlen : (PvsNP.encodeString x).length = x.length := rfl
      change 1 + (r2.steps + (1 + (r1.steps + ((x.length + 1) + (x.length + 1))))) ≤
        2 * (PvsNP.encodeString x).length + 4 +
          c1.time (PvsNP.encodeString x).length +
          c2.time (PvsNP.encodeString x).length
      omega

theorem exp_add_bound (k1 k2 n : ℕ) :
    2 * n + 4 + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2) ≤
      2 ^ (n ^ (k1 + k2 + 10)) + (k1 + k2 + 10) := by
  rcases n with _ | _ | m
  · have h1 : 2 ^ (0 ^ k1) ≤ 2 := by rcases k1 with _ | k <;> simp
    have h2 : 2 ^ (0 ^ k2) ≤ 2 := by rcases k2 with _ | k <;> simp
    have h3 : 0 ^ (k1 + k2 + 10) = 0 := Nat.zero_pow (by omega)
    rw [h3]
    omega
  · simp only [Nat.zero_add, one_pow]
    omega
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    let K := k1 + k2 + 10
    let E := max (N ^ k1) (max (N ^ k2) (N + 1))
    have he1 : 2 ^ (N ^ k1) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have he2 : 2 ^ (N ^ k2) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_right _ _))
    have he3 : 2 * N + 4 ≤ 2 * 2 ^ E := by
      have hlt : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
      have hle : N + 1 ≤ E := (le_max_right _ _).trans (le_max_right _ _)
      have hp : 2 ^ (N + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hle
      omega
    have hsum : 2 * N + 4 + 2 ^ (N ^ k1) + 2 ^ (N ^ k2) ≤ 2 ^ (E + 2) := by
      have hpow : 2 ^ (E + 2) = 4 * 2 ^ E := by ring
      omega
    have hEK : E + 2 ≤ N ^ K := by
      have hb1 : N ^ k1 + 2 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k1 := Nat.one_le_pow k1 N (by omega)
        have hsq : 4 ≤ N ^ 2 := by nlinarith
        have hmul : 4 * N ^ k1 ≤ N ^ 2 * N ^ k1 := Nat.mul_le_mul_right _ hsq
        have hpk : N ^ 2 * N ^ k1 = N ^ (k1 + 2) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k1 + 2) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : N ^ k2 + 2 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k2 := Nat.one_le_pow k2 N (by omega)
        have hsq : 4 ≤ N ^ 2 := by nlinarith
        have hmul : 4 * N ^ k2 ≤ N ^ 2 * N ^ k2 := Nat.mul_le_mul_right _ hsq
        have hpk : N ^ 2 * N ^ k2 = N ^ (k2 + 2) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k2 + 2) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb3 : (N + 1) + 2 ≤ N ^ K := by
        have hcube : N + 3 ≤ N ^ 3 := by
          have hc : N ^ 3 = N * (N * N) := by ring
          rw [hc]
          have h4 : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmon : N ^ 3 ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp only [E, max_def]
      split_ifs <;> omega
    have hpowK : 2 ^ (E + 2) ≤ 2 ^ (N ^ K) := Nat.pow_le_pow_right (by omega) hEK
    change 2 * N + 4 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) ≤ 2 ^ (N ^ K) + K
    have hKdef : K = k1 + k2 + 10 := rfl
    omega

end PvsNP.Units.m2_exp_union

theorem PvsNP.Units.m2_exp_union :
    ∀ L₁ L₂ : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L₁ ⊔ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L₁ L₂ ⟨k1, f1, M1, hf1, ht1⟩ ⟨k2, f2, M2, hf2, ht2⟩
  refine ⟨k1 + k2 + 10, fun x => f1 x || f2 x,
    PvsNP.Units.m2_exp_union.orInTime f1 f2 M1 M2, fun x => ?_, fun n => ?_⟩
  · change x ∈ L₁ ∨ x ∈ L₂ ↔ (f1 x || f2 x) = true
    rw [hf1 x, hf2 x, Bool.or_eq_true]
  · have b1 := ht1 n
    have b2 := ht2 n
    have bound := PvsNP.Units.m2_exp_union.exp_add_bound k1 k2 n
    show 2 * n + 4 + M1.time n + M2.time n ≤ 2 ^ (n ^ (k1 + k2 + 10)) + (k1 + k2 + 10)
    omega
