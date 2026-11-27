import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_clock
import PvsNP.Units.m2_cons_true_time
import PvsNP.Units.m2_tm_timed_comp

theorem PvsNP.Units.m2_tm_exp_clock_succ :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + 1) true)), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  obtain ⟨c₀, M₀, hM₀⟩ := PvsNP.Units.m2_exp_clock k hk
  have hmono : Monotone (fun n : ℕ => 2 * n + 3) := by
    intro a b h; dsimp; omega
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_tm_timed_comp
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true) (fun y : List Bool => true :: y)
    (fun n => c₀ * 2 ^ (n ^ k) + c₀) (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k)) hmono
    (fun x => by simp) ⟨M₀, hM₀⟩ PvsNP.Units.m2_cons_true_time
  refine ⟨c₀ + 5, M, fun n => ?_⟩
  have h := hM n
  have hp : 1 ≤ 2 ^ (n ^ k) := Nat.one_le_two_pow
  nlinarith
