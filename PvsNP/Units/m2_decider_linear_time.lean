import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_decider_linear_time

private def pops {K : Type} {Γ : K → Type} {Λ σ : Type} : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pops q
  | .peek _ _ q => pops q
  | .pop _ _ q => pops q + 1
  | .load _ q => pops q
  | .branch _ q₁ q₂ => max (pops q₁) (pops q₂)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_len {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    (S k).length ≤ ((Turing.TM2.stepAux q v S).stk k).length + pops q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [Turing.TM2.stepAux, pops]
    have h := ih v (Function.update S k' (f v :: S k'))
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_cons] at h
      omega
    · simp only [Function.update_of_ne hk] at h
      exact h
  | peek k' f q ih =>
    simp only [Turing.TM2.stepAux, pops]
    exact ih (f v (S k').head?) S
  | pop k' f q ih =>
    simp only [Turing.TM2.stepAux, pops]
    have h := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_tail] at h
      omega
    · simp only [Function.update_of_ne hk] at h
      omega
  | load a q ih =>
    simp only [Turing.TM2.stepAux, pops]
    exact ih (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [Turing.TM2.stepAux, pops]
    cases hf : f v with
    | false =>
      have h := ih₂ v S
      simp only [Bool.cond_false]
      omega
    | true =>
      have h := ih₁ v S
      simp only [Bool.cond_true]
      omega
  | goto f =>
    simp [Turing.TM2.stepAux, pops]
  | halt =>
    simp [Turing.TM2.stepAux, pops]

private def maxPops (tm : Turing.FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup (fun l : tm.Λ => pops (tm.m l))

private lemma step_len (tm : Turing.FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    (c.stk tm.k₀).length ≤ (c'.stk tm.k₀).length + maxPops tm := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
    | some lbl =>
      simp only [Turing.FinTM2.step, Turing.TM2.step] at h
      cases h
      let _ := tm.ΛFin
      have hle : pops (tm.m lbl) ≤ maxPops tm := by
        unfold maxPops
        exact Finset.le_sup (f := fun l : tm.Λ => pops (tm.m l)) (Finset.mem_univ lbl)
      have haux := stepAux_len (tm.m lbl) v S tm.k₀
      dsimp only
      omega

private lemma iter_none (tm : Turing.FinTM2) :
    ∀ k : ℕ, (flip bind tm.step)^[k] (none : Option tm.Cfg) = none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih

private lemma iter_len (tm : Turing.FinTM2) :
    ∀ (steps : ℕ) (c c' : tm.Cfg),
      (flip bind tm.step)^[steps] (some c) = some c' →
      (c.stk tm.k₀).length ≤ (c'.stk tm.k₀).length + maxPops tm * steps := by
  intro steps
  induction steps with
  | zero =>
    intro c c' h
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    simp
  | succ s ih =>
    intro c c' h
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[s] (tm.step c) = some c' at h
    cases hstep : tm.step c with
    | none =>
      rw [hstep, iter_none] at h
      cases h
    | some c₁ =>
      rw [hstep] at h
      have h1 := step_len tm c c₁ hstep
      have h2 := ih c₁ c' h
      have hmul : maxPops tm * (s + 1) = maxPops tm * s + maxPops tm := Nat.mul_succ _ _
      omega

private lemma haltList_len (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₁)) (hs : s.length ≤ 1) :
    ((Turing.haltList tm s).stk tm.k₀).length ≤ 1 := by
  dsimp only [Turing.haltList]
  generalize tm.k₀ = k
  by_cases h : k = tm.k₁
  · subst h
    simpa using hs
  · simp [h]

end PvsNP.Units.m2_decider_linear_time

theorem PvsNP.Units.m2_decider_linear_time :
    ∀ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer f),
      ∃ d : ℕ, ∀ n : ℕ, n ≤ d * M.time.eval n + 1 := by
  intro f M
  refine ⟨PvsNP.Units.m2_decider_linear_time.maxPops M.tm, fun n => ?_⟩
  let x : List Bool := List.replicate n false
  have hxlen : (PvsNP.encodeString x).length = n := by
    simp [x, PvsNP.encodeString, Computability.encodingList]
  have hout := M.outputsFun x
  have heval :
      (flip bind M.tm.step)^[hout.steps]
        (some (Turing.initList M.tm (List.map M.inputAlphabet.invFun (PvsNP.encodeString x)))) =
      some (Turing.haltList M.tm (List.map M.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)))) := by
    simpa [Turing.TM2OutputsInTime] using hout.evals_in_steps
  have hiter := PvsNP.Units.m2_decider_linear_time.iter_len M.tm hout.steps _ _ heval
  have hinit :
      ((Turing.initList M.tm (List.map M.inputAlphabet.invFun (PvsNP.encodeString x))).stk M.tm.k₀).length = n := by
    simp [Turing.initList, hxlen]
  have hhalt :
      ((Turing.haltList M.tm (List.map M.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)))).stk M.tm.k₀).length ≤ 1 := by
    apply PvsNP.Units.m2_decider_linear_time.haltList_len
    cases f x <;> simp [PvsNP.encodeAnswer, Computability.encodeBool]
  have hsteps : hout.steps ≤ M.time.eval n := by
    simpa [hxlen] using hout.steps_le_m
  have hmul :
      PvsNP.Units.m2_decider_linear_time.maxPops M.tm * hout.steps ≤
      PvsNP.Units.m2_decider_linear_time.maxPops M.tm * M.time.eval n :=
    Nat.mul_le_mul_left _ hsteps
  omega
