import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_timed_comp
import PvsNP.Units.m2_cons_true_time

set_option autoImplicit false

theorem PvsNP.Units.m2_tm_cons_cons_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => true :: true :: x),
      ∀ n : ℕ, M.time n ≤ 6 * n + 12 := by
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_tm_timed_comp (fun y : List Bool => true :: y)
    (fun y : List Bool => true :: y) (fun n => 2 * n + 3) (fun n => 2 * n + 3) (fun n => n + 1)
    (by intro a b h; show 2 * a + 3 ≤ 2 * b + 3; omega)
    (by intro x; show x.length + 1 ≤ x.length + 1; exact le_refl _)
    PvsNP.Units.m2_cons_true_time PvsNP.Units.m2_cons_true_time
  refine ⟨M, fun n => ?_⟩
  have h : M.time n ≤ 2 * n + 3 + 2 * (n + 1) + 2 + (2 * (n + 1) + 3) := hM n
  omega
