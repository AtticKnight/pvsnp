import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_time_hierarchy_gen
import PvsNP.Units.m2_cons_true_time
import PvsNP.Units.m2_exp_clock
import PvsNP.Units.m2_eb_final

namespace PvsNP.Units.m2_exp_no_fixed_exponent

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

lemma exp_le_t (k n : ℕ) : 2 ^ (n ^ k) + k ≤ 2 ^ ((n + 2) ^ (k + 1)) := by
  have h1 : 2 ^ (n ^ k) ≤ 2 ^ ((n + 2) ^ k) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) k)
  have h2 : k ≤ 2 ^ ((n + 2) ^ k) := by
    have ha : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
    have hb : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    have hc : (n + 2) ^ k ≤ 2 ^ ((n + 2) ^ k) := Nat.le_of_lt Nat.lt_two_pow_self
    exact le_trans ha (le_trans hb hc)
  have hsum : 2 ^ (n ^ k) + k ≤ 2 ^ ((n + 2) ^ k + 1) := by
    rw [pow_succ]
    omega
  have hexp : (n + 2) ^ k + 1 ≤ (n + 2) ^ (k + 1) := by
    have hpos : 1 ≤ (n + 2) ^ k := Nat.one_le_pow k (n + 2) (by omega)
    have hmul : (n + 2) ^ k * 2 ≤ (n + 2) ^ k * (n + 2) := Nat.mul_le_mul_left _ (by omega)
    rw [pow_succ]
    omega
  exact le_trans hsum (Nat.pow_le_pow_right (by decide) hexp)

lemma n_le_t (k n : ℕ) : n ≤ 2 ^ ((n + 2) ^ (k + 1)) := by
  have h1 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (Nat.succ_ne_zero k) (n + 2)
  have h2 : (n + 2) ^ (k + 1) ≤ 2 ^ ((n + 2) ^ (k + 1)) := Nat.le_of_lt Nat.lt_two_pow_self
  omega

lemma upper_eb (c K k n : ℕ) :
    c * (2 ^ ((n + 2) ^ (k + 1))) ^ K + c ≤
      2 ^ ((c + 1 + K * 2 ^ (k + 1)) * (n + 1) ^ (k + 1)) := by
  rw [← pow_mul]
  set E := (n + 2) ^ (k + 1) * K
  have hposE : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hc1 : c * 2 ^ E + c ≤ (c + c) * 2 ^ E := by
    have : c ≤ c * 2 ^ E := Nat.le_mul_of_pos_right c hposE
    rw [Nat.add_mul]
    omega
  have hc2 : c + c ≤ 2 ^ (c + 1) := by
    have : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  have hprod : c * 2 ^ E + c ≤ 2 ^ (c + 1 + E) := by
    calc c * 2 ^ E + c ≤ (c + c) * 2 ^ E := hc1
      _ ≤ 2 ^ (c + 1) * 2 ^ E := Nat.mul_le_mul_right _ hc2
      _ = 2 ^ (c + 1 + E) := by rw [← pow_add]
  have hn2 : (n + 2) ^ (k + 1) ≤ 2 ^ (k + 1) * (n + 1) ^ (k + 1) := by
    have hle : n + 2 ≤ 2 * (n + 1) := by omega
    calc (n + 2) ^ (k + 1) ≤ (2 * (n + 1)) ^ (k + 1) := Nat.pow_le_pow_left hle (k + 1)
      _ = 2 ^ (k + 1) * (n + 1) ^ (k + 1) := Nat.mul_pow 2 (n + 1) (k + 1)
  have hE_le : E ≤ (K * 2 ^ (k + 1)) * (n + 1) ^ (k + 1) := by
    have h1 : E = K * (n + 2) ^ (k + 1) := Nat.mul_comm _ _
    rw [h1, Nat.mul_assoc]
    exact Nat.mul_le_mul_left K hn2
  have hc_le : c + 1 ≤ (c + 1) * (n + 1) ^ (k + 1) :=
    Nat.le_mul_of_pos_right (c + 1) (Nat.one_le_pow (k + 1) (n + 1) (Nat.succ_pos n))
  have hexp : c + 1 + E ≤ (c + 1 + K * 2 ^ (k + 1)) * (n + 1) ^ (k + 1) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add hc_le hE_le
  exact le_trans hprod (Nat.pow_le_pow_right (by decide) hexp)

end PvsNP.Units.m2_exp_no_fixed_exponent

theorem PvsNP.Units.m2_exp_no_fixed_exponent :
    ∀ k : ℕ, ∃ L : Language Bool,
      (∃ j : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ j) + j) ∧
      ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro k
  let t : ℕ → ℕ := fun n => 2 ^ ((n + 2) ^ (k + 1))
  have hcons1 : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
      PvsNP.encodeString PvsNP.encodeString (fun y : List Bool => true :: y) (fun n => 2 * n + 3) :=
    PvsNP.Units.m2_cons_true_time
  have hcons2 := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.comp_time
    PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun y : List Bool => true :: y) (fun y : List Bool => true :: y)
    (fun n => 2 * n + 3) (fun n => 2 * n + 3) (fun n => n + 1)
    hcons1 hcons1 (fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 3)
    (fun y => by simp only [PvsNP.encodeString, Computability.encodingList, id_eq, List.length_cons]; exact le_rfl)
  obtain ⟨c0, M0, hM0⟩ := PvsNP.Units.m2_exp_clock (k + 1) (Nat.succ_pos k)
  have hexp0 : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
      PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ (k + 1))) true)
      (fun n => c0 * 2 ^ (n ^ (k + 1)) + c0) := ⟨M0, hM0⟩
  have hmono_exp : Monotone (fun n => c0 * 2 ^ (n ^ (k + 1)) + c0) := by
    intro a b hab
    have h1 : a ^ (k + 1) ≤ b ^ (k + 1) := Nat.pow_le_pow_left hab (k + 1)
    have h2 : 2 ^ (a ^ (k + 1)) ≤ 2 ^ (b ^ (k + 1)) := Nat.pow_le_pow_right (by decide) h1
    exact Nat.add_le_add_right (Nat.mul_le_mul_left c0 h2) c0
  have hcomp := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.comp_time
    PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun y : List Bool => true :: true :: y)
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ (k + 1))) true)
    (fun n => 2 * n + 3 + (2 * (n + 1) + 2) + (2 * (n + 1) + 3))
    (fun n => c0 * 2 ^ (n ^ (k + 1)) + c0)
    (fun n => n + 2)
    hcons2 hexp0 hmono_exp
    (fun y => by simp only [PvsNP.encodeString, Computability.encodingList, id_eq, List.length_cons]; exact le_rfl)
  have hclock : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (t x.length) true)),
      ∀ n : ℕ, M.time n ≤ c * t n + c := by
    have hfun : (fun a : List Bool => List.replicate (2 ^ ((true :: true :: a).length ^ (k + 1))) true) =
        (fun x : List Bool => List.replicate (t x.length) true) := by
      funext x
      simp only [t, List.length_cons]
    rw [hfun] at hcomp
    obtain ⟨Mclk, hMclk⟩ := hcomp
    refine ⟨c0 + 18, Mclk, fun n => ?_⟩
    have h1 : Mclk.time n ≤
        2 * n + 3 + (2 * (n + 1) + 2) + (2 * (n + 1) + 3) + (2 * (n + 2) + 2) +
          (c0 * t n + c0) := hMclk n
    have hn : n ≤ t n := PvsNP.Units.m2_exp_no_fixed_exponent.n_le_t k n
    have hmul : (c0 + 18) * t n = c0 * t n + 18 * t n := Nat.add_mul c0 18 (t n)
    have h2 : 8 * n + 18 + c0 * t n + c0 ≤ (c0 + 18) * t n + (c0 + 18) := by
      rw [hmul]
      omega
    have h3 : 2 * n + 3 + (2 * (n + 1) + 2) + (2 * (n + 1) + 3) + (2 * (n + 2) + 2) +
        (c0 * t n + c0) = 8 * n + 18 + c0 * t n + c0 := by omega
    rw [h3] at h1
    exact le_trans h1 h2
  obtain ⟨K, hK⟩ := PvsNP.Units.m2_time_hierarchy_gen
  obtain ⟨L, ⟨c, f, M, hf, hM⟩, hno⟩ := hK t (PvsNP.Units.m2_exp_no_fixed_exponent.n_le_t k) hclock
  refine ⟨L, ?_, ?_⟩
  · have heb : ∃ A D : ℕ, ∀ n : ℕ, M.time n ≤ 2 ^ (A * (n + 1) ^ D) :=
      ⟨c + 1 + K * 2 ^ (k + 1), k + 1, fun n =>
        le_trans (hM n) (PvsNP.Units.m2_exp_no_fixed_exponent.upper_eb c K k n)⟩
    obtain ⟨j, hj⟩ := PvsNP.Units.m2_eb_final M.time heb
    exact ⟨j, f, M, hf, hj⟩
  · rintro ⟨f', M', hf', hM'⟩
    exact hno ⟨f', M', hf', fun n =>
      le_trans (hM' n) (PvsNP.Units.m2_exp_no_fixed_exponent.exp_le_t k n)⟩
