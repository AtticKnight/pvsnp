import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_square_clock
import PvsNP.Units.m2_cons_true_time
import PvsNP.Units.m2_tm_timed_comp

theorem PvsNP.Units.m2_tm_square_clock_succ :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (x.length ^ 2 + 1) true)), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c := by
  obtain ⟨c₀, M₀, hM₀⟩ := PvsNP.Units.m2_square_clock
  have hmono : Monotone (fun n : ℕ => 2 * n + 3) := by
    intro a b h; dsimp; omega
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_tm_timed_comp
    (fun x : List Bool => List.replicate (x.length ^ 2) true) (fun y : List Bool => true :: y)
    (fun n => c₀ * n ^ 2 + c₀) (fun n => 2 * n + 3) (fun n => n ^ 2) hmono
    (fun x => by simp) ⟨M₀, hM₀⟩ PvsNP.Units.m2_cons_true_time
  refine ⟨c₀ + 5, M, fun n => ?_⟩
  have h := hM n
  nlinarith
