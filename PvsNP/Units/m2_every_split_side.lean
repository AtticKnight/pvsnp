import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_concat
import PvsNP.Units.m2_np_concat

set_option autoImplicit false

namespace PvsNP.Units.m2_every_split_side

theorem split_compl (L : Language Bool) :
    ({x : List Bool | ∀ u v : List Bool, x = u ++ v → u ∈ L ∨ v ∈ L} : Language Bool) =
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ Lᶜ ∧ v ∈ Lᶜ} : Language Bool)ᶜ := by
  ext x
  constructor
  · intro h ⟨u, v, hx, hu, hv⟩
    rcases h u v hx with h1 | h1
    · exact hu h1
    · exact hv h1
  · intro h u v hx
    by_contra hn
    exact h ⟨u, v, hx, fun h1 => hn (Or.inl h1), fun h1 => hn (Or.inr h1)⟩

theorem main (L : Language Bool) :
    (L ∈ PvsNP.P → ({x : List Bool | ∀ u v : List Bool, x = u ++ v → u ∈ L ∨ v ∈ L} : Language Bool) ∈ PvsNP.P) ∧
      (L ∈ PvsNP.coNP →
        ({x : List Bool | ∀ u v : List Bool, x = u ++ v → u ∈ L ∨ v ∈ L} : Language Bool) ∈ PvsNP.coNP) := by
  rw [split_compl L]
  constructor
  · intro hL
    have hc : Lᶜ ∈ PvsNP.P := PvsNP.Units.m2_p_compl L hL
    exact PvsNP.Units.m2_p_compl _ (PvsNP.Units.m2_p_concat Lᶜ Lᶜ hc hc)
  · intro hL
    show (({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ Lᶜ ∧ v ∈ Lᶜ} : Language Bool)ᶜ)ᶜ ∈ PvsNP.NP
    rw [compl_compl]
    exact PvsNP.Units.m2_np_concat Lᶜ Lᶜ hL hL

end PvsNP.Units.m2_every_split_side

theorem PvsNP.Units.m2_every_split_side :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | ∀ u v : List Bool, x = u ++ v → u ∈ L ∨ v ∈ L} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.coNP →
          ({x : List Bool | ∀ u v : List Bool, x = u ++ v → u ∈ L ∨ v ∈ L} : Language Bool) ∈ PvsNP.coNP) :=
  PvsNP.Units.m2_every_split_side.main
