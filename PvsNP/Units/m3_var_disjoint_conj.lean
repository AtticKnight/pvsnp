import Mathlib
import PvsNP.Defs
import CookLevin

open SAT_inNP

namespace PvsNP.Units.m3_var_disjoint_conj

theorem evalClause_congr {a₁ a₂ : assgn} {C : clause}
    (h : ∀ l ∈ C, evalLiteral a₁ l = evalLiteral a₂ l) :
    evalClause a₁ C = evalClause a₂ C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    show (l :: C).any (evalLiteral a₁) = (l :: C).any (evalLiteral a₂)
    rw [List.any_cons, List.any_cons, h l (by simp)]
    congr 1
    exact ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))

theorem evalCnf_congr {a₁ a₂ : assgn} {N : cnf}
    (h : ∀ C ∈ N, ∀ l ∈ C, evalLiteral a₁ l = evalLiteral a₂ l) :
    evalCnf a₁ N = evalCnf a₂ N := by
  induction N with
  | nil => rfl
  | cons C N ih =>
    show (C :: N).all (evalClause a₁) = (C :: N).all (evalClause a₂)
    rw [List.all_cons, List.all_cons, evalClause_congr (h C (by simp))]
    congr 1
    exact ih (fun C' hC' => h C' (List.mem_cons_of_mem C hC'))


end PvsNP.Units.m3_var_disjoint_conj

/-- Two CNFs with no variable in common are jointly satisfiable iff each is:
left to right restricts an assignment (vendored `evalCnf_app_iff`); right to
left glues the two assignments, each cut down to its own formula's variables,
so no literal of one formula sees the variables kept from the other. -/
theorem PvsNP.Units.m3_var_disjoint_conj :
    ∀ N₁ N₂ : cnf, (∀ C ∈ N₁, ∀ D ∈ N₂, ∀ l ∈ C, ∀ m ∈ D, l.2 ≠ m.2) →
      (SAT (N₁ ++ N₂) ↔ SAT N₁ ∧ SAT N₂) := by
  intro N₁ N₂ hdisj
  constructor
  · rintro ⟨a, ha⟩
    rw [satisfiesCnf, evalCnf_app_iff] at ha
    exact ⟨⟨a, ha.1⟩, ⟨a, ha.2⟩⟩
  · rintro ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
    refine ⟨a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂), ?_⟩
    have hdisj' : ∀ v : var, v ∈ varsOfCnf N₁ → v ∈ varsOfCnf N₂ → False := by
      intro v hv₁ hv₂
      have hv₁' : v ∈ (N₁.map varsOfClause).flatten := hv₁
      have hv₂' : v ∈ (N₂.map varsOfClause).flatten := hv₂
      rw [List.mem_flatten] at hv₁' hv₂'
      obtain ⟨VC, hVC, hvC⟩ := hv₁'
      obtain ⟨VD, hVD, hvD⟩ := hv₂'
      rw [List.mem_map] at hVC hVD
      obtain ⟨C, hC, rfl⟩ := hVC
      obtain ⟨D, hD, rfl⟩ := hVD
      have hvC' : v ∈ (C.map varsOfLiteral).flatten := hvC
      have hvD' : v ∈ (D.map varsOfLiteral).flatten := hvD
      rw [List.mem_flatten] at hvC' hvD'
      obtain ⟨VL, hVL, hvL⟩ := hvC'
      obtain ⟨VM, hVM, hvM⟩ := hvD'
      rw [List.mem_map] at hVL hVM
      obtain ⟨l, hl, rfl⟩ := hVL
      obtain ⟨m, hm, rfl⟩ := hVM
      have hvL' : v ∈ [l.2] := hvL
      have hvM' : v ∈ [m.2] := hvM
      rw [List.mem_singleton] at hvL' hvM'
      exact hdisj C hC D hD l hl m hm (by rw [← hvL', ← hvM'])
    have hmem₁ : ∀ v : var, v ∈ varsOfCnf N₁ →
        ((v ∈ a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) ↔ v ∈ a₁) := by
      intro v hv
      rw [List.mem_append, List.mem_filter, List.mem_filter]
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact h1
        · exact absurd h2 (fun h2' => hdisj' v hv (of_decide_eq_true h2'))
      · intro h1
        exact Or.inl ⟨h1, decide_eq_true hv⟩
    have hmem₂ : ∀ v : var, v ∈ varsOfCnf N₂ →
        ((v ∈ a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) ↔ v ∈ a₂) := by
      intro v hv
      rw [List.mem_append, List.mem_filter, List.mem_filter]
      constructor
      · rintro (⟨-, h1⟩ | ⟨h2, -⟩)
        · exact absurd h1 (fun h1' => hdisj' v (of_decide_eq_true h1') hv)
        · exact h2
      · intro h2
        exact Or.inr ⟨h2, decide_eq_true hv⟩
    have hvar₁ : ∀ v : var, v ∈ varsOfCnf N₁ →
        evalVar (a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) v = evalVar a₁ v := by
      intro v hv
      simp only [evalVar, decide_eq_decide]
      exact hmem₁ v hv
    have hvar₂ : ∀ v : var, v ∈ varsOfCnf N₂ →
        evalVar (a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) v = evalVar a₂ v := by
      intro v hv
      simp only [evalVar, decide_eq_decide]
      exact hmem₂ v hv
    rw [satisfiesCnf, evalCnf_app_iff]
    constructor
    · have hcc : evalCnf (a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) N₁ = evalCnf a₁ N₁ := by
        apply PvsNP.Units.m3_var_disjoint_conj.evalCnf_congr
        intro C hC l hl
        simp only [evalLiteral]
        rw [hvar₁ l.2 (varsOfCnf_mem N₁ C l hC hl)]
      rw [hcc]
      exact ha₁
    · have hcc : evalCnf (a₁.filter (· ∈ varsOfCnf N₁) ++ a₂.filter (· ∈ varsOfCnf N₂)) N₂ = evalCnf a₂ N₂ := by
        apply PvsNP.Units.m3_var_disjoint_conj.evalCnf_congr
        intro C hC l hl
        simp only [evalLiteral]
        rw [hvar₂ l.2 (varsOfCnf_mem N₂ C l hC hl)]
      rw [hcc]
      exact ha₂
