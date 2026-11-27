import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.tl_lang_len_square_p

/-- Map length n to length 8n+1. The odd squares among these lengths encode the triangular numbers. -/
theorem PvsNP.Units.tl_lang_len_tri_p :
    ({x : List Bool | ∃ k : ℕ, 2 * x.length = k * (k + 1)} : Language Bool) ∈ PvsNP.P := by
  let p : Polynomial ℕ := 8 * Polynomial.X + 1
  refine PvsNP.Units.m2_p_down_closed _ _ ?_ PvsNP.Units.tl_lang_len_square_p
  refine ⟨fun x => List.replicate (p.eval x.length) true,
    PvsNP.Units.fr_ladner.PEqualNP.Library.L055 p, ?_⟩
  intro x
  change (∃ k : ℕ, 2 * x.length = k * (k + 1)) ↔
    ∃ j : ℕ, (List.replicate (p.eval x.length) true).length = j ^ 2
  simp only [List.length_replicate]
  have hp : p.eval x.length = 8 * x.length + 1 := by simp [p]
  rw [hp]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by nlinarith⟩
  · rintro ⟨j, hj⟩
    let k := j / 2
    have hd : j = 2 * k ∨ j = 2 * k + 1 := by dsimp [k]; omega
    rcases hd with he | ho
    · have bad : 8 * x.length + 1 = 4 * k ^ 2 := calc
        _ = j ^ 2 := hj
        _ = (2 * k) ^ 2 := congrArg (fun a : ℕ => a ^ 2) he
        _ = _ := by ring
      omega
    · have hs : 8 * x.length + 1 = (2 * k + 1) ^ 2 :=
        hj.trans (congrArg (fun a : ℕ => a ^ 2) ho)
      exact ⟨k, by nlinarith⟩
