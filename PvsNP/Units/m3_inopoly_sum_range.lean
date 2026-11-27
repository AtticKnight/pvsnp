import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_inopoly_sum_range : ∀ f : ℕ → ℕ, inOPoly f → inOPoly (fun n => ((List.range n).map f).sum) := by
  intro f hf
  obtain ⟨c, k, d, hbound⟩ := CookLevin.Lang.FrontWitness.inOPoly_monomial_bound hf
  have hpoly : inOPoly (fun n => n * (c * (n + 1) ^ k + d)) :=
    inOPoly_mul inOPoly_id
      (inOPoly_add (inOPoly_mul (inOPoly_const c) (CookLevin.Lang.FrontWitness.inOPoly_pow_succ k))
        (inOPoly_const d))
  refine CookLevin.Lang.inOPoly_of_le ?_ hpoly
  intro n
  have hsum : ∀ m, m ≤ n → ((List.range m).map f).sum ≤ m * (c * (n + 1) ^ k + d) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hih := ih (Nat.le_of_succ_le hm)
      have hfm : f m ≤ c * (n + 1) ^ k + d := by
        have h1 := hbound m
        have h2 : (m + 1) ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (by omega) k
        nlinarith
      nlinarith
  exact hsum n le_rfl
