import Mathlib
import PvsNP.Defs
import CookLevin

/-- The palindrome language is not Karp reducible to the empty language, nor to the
universal language: `[]` is a palindrome (so no reduction can land in the empty
language), while `[true, false]` is not a palindrome (so no reduction can land in the
universal language). -/
theorem PvsNP.Units.m2_x_pal_not_karp_trivial :
    ¬ PvsNP.KarpReducible ({x : List Bool | x.reverse = x} : Language Bool)
        ({x : List Bool | False} : Language Bool) ∧
      ¬ PvsNP.KarpReducible ({x : List Bool | x.reverse = x} : Language Bool)
        ({x : List Bool | True} : Language Bool) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, -, hiff⟩
    exact (hiff []).mp
      (by decide : ([] : List Bool) ∈ ({x : List Bool | x.reverse = x} : Language Bool))
  · rintro ⟨f, -, hiff⟩
    exact (by decide : ¬ ([true, false] : List Bool).reverse = [true, false])
      ((hiff [true, false]).mpr
        (by decide : ([true, false] : List Bool) ∈ ({x : List Bool | True} : Language Bool)))
