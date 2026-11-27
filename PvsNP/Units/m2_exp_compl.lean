import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_exp_compl

private def boolNotEquiv : Bool ≃ Bool where
  toFun := (!·)
  invFun := (!·)
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

theorem exp_compl_main :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ Lᶜ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, htime⟩
  let M' : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => !f x) :=
    { tm := M.tm
      inputAlphabet := M.inputAlphabet
      outputAlphabet := M.outputAlphabet.trans boolNotEquiv
      time := M.time
      outputsFun := fun x =>
        { steps := (M.outputsFun x).steps
          steps_le_m := (M.outputsFun x).steps_le_m
          evals_in_steps := by
            have h := (M.outputsFun x).evals_in_steps
            have heq : List.map (M.outputAlphabet.trans boolNotEquiv).invFun (PvsNP.encodeAnswer (!f x)) =
                List.map M.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)) := by
              cases f x <;> rfl
            rw [heq]
            exact h } }
  refine ⟨k, fun x => !f x, M', fun x => ?_, htime⟩
  show x ∉ L ↔ (!f x) = true
  rw [hf x]
  cases f x <;> simp

end PvsNP.Units.m2_exp_compl

theorem PvsNP.Units.m2_exp_compl :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ Lᶜ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_exp_compl.exp_compl_main
