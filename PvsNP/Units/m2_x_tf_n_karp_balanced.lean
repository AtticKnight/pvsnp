import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_reduces_nontrivial
import PvsNP.Units.tl_lang_tf_n_p

-- Built from the settled campaign units m2_p_reduces_nontrivial and tl_lang_tf_n_p (make.fun pvsnp campaign).

theorem PvsNP.Units.m2_x_tf_n_karp_balanced :
    PvsNP.KarpReducible ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate n false} : Language Bool)
      ({x : List Bool | x.count true = x.count false} : Language Bool) := by
  have _hc := Classical.em True
  refine PvsNP.Units.m2_p_reduces_nontrivial _ _ PvsNP.Units.tl_lang_tf_n_p ⟨[], ?_⟩ ⟨[true], ?_⟩
  · show ([] : List Bool).count true = ([] : List Bool).count false
    rfl
  · show ¬ ([true] : List Bool).count true = ([true] : List Bool).count false
    simp
