import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_first_time
import PvsNP.Units.m2_cons_true_time

theorem PvsNP.Units.m2_tm_first_cons_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodePair
        (fun p : List Bool × List Bool => (true :: p.1, p.2)),
      ∀ n : ℕ, M.time n ≤ 6 * n + 10 := by
  have ht : Monotone (fun n : ℕ => 2 * n + 3) := by intro a b h; dsimp; omega
  have hl : Monotone (fun n : ℕ => n + 1) := by intro a b h; dsimp; omega
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_first_time (fun y : List Bool => true :: y)
    (fun n => 2 * n + 3) (fun n => n + 1) ht hl (fun x => by simp) PvsNP.Units.m2_cons_true_time
  refine ⟨M, fun n => ?_⟩
  have h := hM n
  omega
