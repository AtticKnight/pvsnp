import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_join_in_p
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_exp_union

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_join

private lemma tail_in_exp {L : Language Bool}
    (hL : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ ({x : List Bool | x.tail ∈ L} : Language Bool) ↔ f x = true) ∧
      ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  have hred : PvsNP.KarpReducible ({x : List Bool | x.tail ∈ L} : Language Bool) L :=
    ⟨List.tail, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail, fun _ => Iff.rfl⟩
  exact PvsNP.Units.m2_exp_down_closed _ _ hred hL

private lemma cons_in_exp (b : Bool) {L : Language Bool}
    (hL : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) ↔ f x = true) ∧
      ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  have hEq : ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, x = b :: y} : Language Bool) ⊓
      ({x : List Bool | x.tail ∈ L} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, hy⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hy, rfl⟩
  rw [hEq]
  exact PvsNP.Units.m2_exp_inter _ _
    (PvsNP.Units.m2_p_subset_exp _ (PvsNP.Units.m2_join_in_p.head_in_p b))
    (tail_in_exp hL)

end PvsNP.Units.m2_exp_join

theorem PvsNP.Units.m2_exp_join :
    ∀ L₁ L₂ : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L₁ L₂ h1 h2
  have hEq : ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) =
      ({x : List Bool | ∃ y ∈ L₁, x = false :: y} : Language Bool) ⊔
      ({x : List Bool | ∃ y ∈ L₂, x = true :: y} : Language Bool) := by
    ext x
    rfl
  rw [hEq]
  exact PvsNP.Units.m2_exp_union _ _
    (PvsNP.Units.m2_exp_join.cons_in_exp false h1)
    (PvsNP.Units.m2_exp_join.cons_in_exp true h2)
