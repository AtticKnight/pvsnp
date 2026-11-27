import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_np_down_closed

/-
Original proof of `PvsNP.Units.m2_expc_np_iff_conp`, from the settled units it imports.
-/

theorem PvsNP.Units.m2_expc_np_iff_conp :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' L) →
  (L ∈ PvsNP.NP ↔ L ∈ PvsNP.coNP) := by
  intro L hL hard
  have hc : PvsNP.KarpReducible Lᶜ L := hard _ (PvsNP.Units.m2_exp_compl L hL)
  have hc' : PvsNP.KarpReducible L Lᶜ := by
    have h := (PvsNP.Units.m2_karp_compl_iff _ _).mp hc
    rwa [compl_compl] at h
  constructor
  · intro hNP
    show Lᶜ ∈ PvsNP.NP
    exact PvsNP.Units.m2_np_down_closed _ _ hc hNP
  · intro hco
    have hco' : Lᶜ ∈ PvsNP.NP := hco
    exact PvsNP.Units.m2_np_down_closed _ _ hc' hco'
