import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_len_prime_p
import PvsNP.Units.tl_lang_len_square_p
import PvsNP.Units.m2_p_union

theorem PvsNP.Units.m2_x_len_prime_or_square_p :
    ({x : List Bool | Nat.Prime x.length ∨ ∃ k : ℕ, x.length = k ^ 2} : Language Bool) ∈ PvsNP.P := by
  have h : ({x : List Bool | Nat.Prime x.length ∨ ∃ k : ℕ, x.length = k ^ 2} : Language Bool)
      = {x : List Bool | Nat.Prime x.length} ⊔ {x : List Bool | ∃ k : ℕ, x.length = k ^ 2} := by
    ext x
    simp
  rw [h]
  exact m2_p_union _ _ PvsNP.Units.tl_lang_len_prime_p PvsNP.Units.tl_lang_len_square_p
