import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_linear_clock
import PvsNP.Units.m2_first_time

namespace PvsNP.Units.m2_tm_first_clock_time

theorem len_le (x : List Bool) : (List.replicate x.length true).length ≤ id x.length := by
  simp

theorem lin_mono (c : ℕ) : Monotone (fun n : ℕ => c * n + c) := by
  intro a b h
  show c * a + c ≤ c * b + c
  have := Nat.mul_le_mul_left c h
  omega

end PvsNP.Units.m2_tm_first_clock_time

/-- Run the linear clock (`m2_linear_clock`) on the first string of the pair, via the
first-component lift of `m2_first_time`. -/
theorem PvsNP.Units.m2_tm_first_clock_time :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodePair
        (fun p : List Bool × List Bool => (List.replicate p.1.length true, p.2))), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨c, M, hM⟩ := PvsNP.Units.m2_linear_clock
  obtain ⟨M', hM'⟩ := PvsNP.Units.m2_first_time (fun x : List Bool => List.replicate x.length true)
    (fun n => c * n + c) id (PvsNP.Units.m2_tm_first_clock_time.lin_mono c) monotone_id
    PvsNP.Units.m2_tm_first_clock_time.len_le ⟨M, hM⟩
  refine ⟨c + 5, M', fun n => ?_⟩
  have h := hM' n
  simp only [id] at h
  have : (c + 5) * n + (c + 5) = c * n + c + 5 * n + 5 := by ring
  omega
