import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_output_length_poly
import PvsNP.Units.m2_eb_two_pow
import PvsNP.Units.m2_eb_add
import PvsNP.Units.m2_eb_final

/-
Class-level fact in the setting of github.com/open-goat/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License, Version 2.0, http://www.apache.org/licenses/LICENSE-2.0):
EXP (upstream lean/PEqualNP/Defs/Classes.lean, DTIME(2 ^ (n ^ k) + k)) is closed downward under polynomial-time
reductions, as P is in lean/PEqualNP/Library/L016.lean. The proof composes the reduction with the decider by the
upstream Machines/ComposeTime comp_time and bounds the time with upstream Helpers/ExpBound (eb_two_pow, eb_add,
eb_final), here the settled campaign units fr_ladner, m2_output_length_poly, m2_eb_two_pow, m2_eb_add,
m2_eb_final (imported). New proof.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_down_closed

open PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem poly_mono_bound (p : Polynomial ℕ) : ∃ A D : ℕ, ∀ n : ℕ, p.eval n ≤ A * (n + 1) ^ D := by
  obtain ⟨s, hs⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.polynomial_le_pow_add p
  refine ⟨s + 1, s, fun n => ?_⟩
  have h1 : n ^ s ≤ (n + 1) ^ s := Nat.pow_le_pow_left (by omega) s
  have h2 : 1 ≤ (n + 1) ^ s := Nat.one_le_pow _ _ (by omega)
  have h3 : s ≤ s * (n + 1) ^ s := Nat.le_mul_of_pos_right _ h2
  have h4 : (s + 1) * (n + 1) ^ s = s * (n + 1) ^ s + (n + 1) ^ s := by ring
  have := hs n
  omega

theorem main : ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ →
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L₁ L₂ ⟨r, hr, hred⟩ ⟨k, g, M, hg, hM⟩
  obtain ⟨p, hp⟩ := time_of_polyTime (ea := fun x : List Bool => x) (eb := fun x : List Bool => x) hr
  obtain ⟨q, hq⟩ := PvsNP.Units.m2_output_length_poly r hr
  have hgt : ComputableInTime (fun x : List Bool => x) Computability.encodeBool g
      (fun n => 2 ^ (n ^ k) + k) := ⟨M, hM⟩
  have hmono : Monotone (fun n : ℕ => 2 ^ (n ^ k) + k) := fun a b h => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.pow_le_pow_left h k)
    dsimp only
    omega
  have hc := comp_time (fun x : List Bool => x) (fun x : List Bool => x) Computability.encodeBool r g
    (fun n => p.eval n) (fun n => 2 ^ (n ^ k) + k) (fun n => q.eval n) hp hgt hmono (fun x => hq x)
  obtain ⟨A, D, hAD⟩ := poly_mono_bound p
  obtain ⟨B, E, hBE⟩ := poly_mono_bound q
  obtain ⟨B', E', h2⟩ := PvsNP.Units.m2_eb_two_pow (fun n => q.eval n) B E k hBE
  have hG : ∃ A D : ℕ, ∀ n : ℕ, (fun n => p.eval n + (2 * q.eval n + 2) + k) n ≤ 2 ^ (A * (n + 1) ^ D) := by
    refine ⟨A + 2 * B + 2 + k, D + E, fun n => ?_⟩
    have e1 : (n + 1) ^ D ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (n + 1) ^ E ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
    have e3 : 1 ≤ (n + 1) ^ (D + E) := Nat.one_le_pow _ _ (by omega)
    have t1 : A * (n + 1) ^ D ≤ A * (n + 1) ^ (D + E) := Nat.mul_le_mul_left A e1
    have t2 : B * (n + 1) ^ E ≤ B * (n + 1) ^ (D + E) := Nat.mul_le_mul_left B e2
    have t3 : 2 + k ≤ (2 + k) * (n + 1) ^ (D + E) := Nat.le_mul_of_pos_right _ e3
    have t4 : (A + 2 * B + 2 + k) * (n + 1) ^ (D + E) =
        A * (n + 1) ^ (D + E) + 2 * (B * (n + 1) ^ (D + E)) + (2 + k) * (n + 1) ^ (D + E) := by ring
    have hp' := hAD n
    have hq' := hBE n
    have hlt : (A + 2 * B + 2 + k) * (n + 1) ^ (D + E) ≤ 2 ^ ((A + 2 * B + 2 + k) * (n + 1) ^ (D + E)) :=
      Nat.lt_two_pow_self.le
    dsimp only
    omega
  obtain ⟨A₂, D₂, hsum⟩ := PvsNP.Units.m2_eb_add _ _ hG ⟨B', E', h2⟩
  obtain ⟨j, hj⟩ := PvsNP.Units.m2_eb_final _ ⟨A₂, D₂, hsum⟩
  obtain ⟨M', hM'⟩ := time_mono hc (t' := fun n => 2 ^ (n ^ j) + j) (fun n => by
    have := hj n
    omega)
  have _hc := Classical.em True
  exact ⟨j, fun x => g (r x), M', fun x => (hred x).trans (hg (r x)), hM'⟩



theorem h_fk : ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ → (∃ (k : ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → ∃ (k : ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := PvsNP.Units.m2_exp_down_closed.main


theorem h_swap : ∀ L₁ L₂ : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → PvsNP.KarpReducible L₁ L₂ → ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := fun L₁ L₂ h hr => PvsNP.Units.m2_exp_down_closed.main L₁ L₂ hr h


end PvsNP.Units.m2_exp_down_closed

theorem PvsNP.Units.m2_exp_down_closed :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_exp_down_closed.main
