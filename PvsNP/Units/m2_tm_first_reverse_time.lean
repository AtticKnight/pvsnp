import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_first_time
import PvsNP.Units.m2_tm_reverse_time

theorem PvsNP.Units.m2_tm_first_reverse_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodePair
        (fun p : List Bool × List Bool => (p.1.reverse, p.2)),
      ∀ n : ℕ, M.time n ≤ 5 * n + 6 := by
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_first_time
    (fun x : List Bool => x.reverse)
    (fun n : ℕ => n + 1)
    (fun n : ℕ => n)
    (fun _ _ h => Nat.add_le_add_right h 1)
    (fun _ _ h => h)
    (fun x => by simp)
    PvsNP.Units.m2_tm_reverse_time
  refine ⟨M, fun n => ?_⟩
  have hn : M.time n ≤ n + 1 + 2 * n + 2 * n + 5 := hM n
  omega
