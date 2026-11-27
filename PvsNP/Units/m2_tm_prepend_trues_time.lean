import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_cons_true_time
import PvsNP.Units.m2_tm_timed_comp

theorem PvsNP.Units.m2_tm_prepend_trues_time :
    ∀ k : ℕ, ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate k true ++ x)), ∀ n : ℕ, M.time n ≤ c * n + c := by
  intro k
  induction k with
  | zero =>
      refine ⟨1, Turing.idComputableInTime _, fun n => ?_⟩
      show Polynomial.eval n 1 ≤ 1 * n + 1
      simp
  | succ k ih =>
      obtain ⟨c, M₀, hM₀⟩ := ih
      have hmono : Monotone (fun n : ℕ => 2 * n + 3) := by
        intro a b h; dsimp; omega
      obtain ⟨M, hM⟩ := PvsNP.Units.m2_tm_timed_comp
        (fun x : List Bool => List.replicate k true ++ x) (fun y : List Bool => true :: y)
        (fun n => c * n + c) (fun n => 2 * n + 3) (fun n => n + k) hmono
        (fun x => by simp; omega) ⟨M₀, hM₀⟩ PvsNP.Units.m2_cons_true_time
      refine ⟨c + 4 * k + 5, M, fun n => ?_⟩
      have h := hM n
      nlinarith
