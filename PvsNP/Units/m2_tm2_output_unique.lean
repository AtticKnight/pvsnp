import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_tm2_output_unique

lemma step_haltList (tm : Turing.FinTM2) (o : List (tm.Γ tm.k₁)) :
    tm.step (Turing.haltList tm o) = none := rfl

lemma iter_bind_none {σ : Type*} (f : σ → Option σ) :
    ∀ k : ℕ, (flip bind f)^[k] none = none
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply]
    exact iter_bind_none f k

lemma iter_bind_haltList_succ (tm : Turing.FinTM2) (o : List (tm.Γ tm.k₁)) (k : ℕ) :
    (flip bind tm.step)^[k + 1] (some (Turing.haltList tm o)) = none := by
  rw [Function.iterate_succ_apply]
  change (flip bind tm.step)^[k] (tm.step (Turing.haltList tm o)) = none
  rw [step_haltList]
  exact iter_bind_none tm.step k

end PvsNP.Units.m2_tm2_output_unique

theorem PvsNP.Units.m2_tm2_output_unique :
    ∀ (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) (o₁ o₂ : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2Outputs tm l (some o₁)) →
        Nonempty (Turing.TM2Outputs tm l (some o₂)) → o₁ = o₂ := by
  intro tm l o₁ o₂ ⟨h₁⟩ ⟨h₂⟩
  have e₁ : (flip bind tm.step)^[h₁.steps] (some (Turing.initList tm l)) =
      some (Turing.haltList tm o₁) := h₁.evals_in_steps
  have e₂ : (flip bind tm.step)^[h₂.steps] (some (Turing.initList tm l)) =
      some (Turing.haltList tm o₂) := h₂.evals_in_steps
  have hsteps : h₁.steps = h₂.steps := by
    rcases lt_trichotomy h₁.steps h₂.steps with hlt | heq | hgt
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
      have hk' : h₂.steps = (k + 1) + h₁.steps := by omega
      rw [hk', Function.iterate_add_apply, e₁,
        PvsNP.Units.m2_tm2_output_unique.iter_bind_haltList_succ] at e₂
      exact absurd e₂ (by simp)
    · exact heq
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
      have hk' : h₁.steps = (k + 1) + h₂.steps := by omega
      rw [hk', Function.iterate_add_apply, e₂,
        PvsNP.Units.m2_tm2_output_unique.iter_bind_haltList_succ] at e₁
      exact absurd e₁ (by simp)
  rw [hsteps] at e₁
  have hc : Turing.haltList tm o₁ = Turing.haltList tm o₂ := Option.some.inj (e₁.symm.trans e₂)
  have hstk := congrArg (fun c => c.stk tm.k₁) hc
  simpa [Turing.haltList] using hstk
