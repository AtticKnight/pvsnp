import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_exp_down_closed

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Append or prepend the fixed word to reduce each quotient to the original language. -/
theorem PvsNP.Units.m2_fixed_quotient_conp_exp :
    ∀ (w : List Bool) (L : Language Bool),
  (L ∈ PvsNP.coNP → ({x : List Bool | x ++ w ∈ L} : Language Bool) ∈ PvsNP.coNP ∧
      ({x : List Bool | w ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) ∧
    ((∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({y : List Bool | y ++ w ∈ L} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({y : List Bool | w ++ y ∈ L} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) := by
  intro w L
  have right : PvsNP.KarpReducible ({x : List Bool | x ++ w ∈ L} : Language Bool) L :=
    ⟨fun x => x ++ w, cpt_app2 cpt_id (cpt_const w), fun _ => Iff.rfl⟩
  have left : PvsNP.KarpReducible ({x : List Bool | w ++ x ∈ L} : Language Bool) L :=
    ⟨fun x => w ++ x, cpt_app2 (cpt_const w) cpt_id, fun _ => Iff.rfl⟩
  constructor
  · intro h
    exact ⟨PvsNP.Units.m2_conp_down_closed _ _ right h, PvsNP.Units.m2_conp_down_closed _ _ left h⟩
  · intro h
    exact ⟨PvsNP.Units.m2_exp_down_closed _ _ right h, PvsNP.Units.m2_exp_down_closed _ _ left h⟩
