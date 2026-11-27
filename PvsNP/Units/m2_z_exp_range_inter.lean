import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_exp

set_option autoImplicit false

theorem PvsNP.Units.m2_z_exp_range_inter :
  ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ F i ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  intro F m
  induction m with
  | zero =>
    intro _
    obtain ⟨k, f, M, hf, hM⟩ :=
      PvsNP.Units.m2_p_subset_exp (Set.univ : Language Bool) PvsNP.Units.m2_p_trivial.2
    refine ⟨k, f, M, fun x => ?_, hM⟩
    rw [← hf x]
    exact ⟨fun _ => trivial, fun _ i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ m ih =>
    intro hF
    have h1 := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have h2 := hF m (Nat.lt_succ_self m)
    obtain ⟨k, f, M, hf, hM⟩ := PvsNP.Units.m2_exp_inter _ _ h1 h2
    refine ⟨k, f, M, fun x => ?_, hM⟩
    rw [← hf x]
    change (∀ i < m + 1, x ∈ F i) ↔ (∀ i < m, x ∈ F i) ∧ x ∈ F m
    constructor
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h m (Nat.lt_succ_self m)⟩
    · rintro ⟨hl, hr⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hl i hlt
      · exact hr
