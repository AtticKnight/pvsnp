import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_models_count_incl_excl

private theorem evalCnf_or_distrib (a : assgn) (N₁ N₂ : cnf) :
    evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D))) =
      (evalCnf a N₁ || evalCnf a N₂) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true]
  rw [evalCnf_clause_iff, evalCnf_clause_iff, evalCnf_clause_iff]
  constructor
  · intro h
    by_cases h1 : ∀ C ∈ N₁, evalClause a C = true
    · exact Or.inl h1
    · right
      push_neg at h1
      obtain ⟨C, hC, hCfalse⟩ := h1
      intro D hD
      have hCD := h (C ++ D) (List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨D, hD, rfl⟩⟩)
      obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a (C ++ D)).mp hCD
      rcases List.mem_append.mp hl with hlC | hlD
      · exfalso
        exact hCfalse ((evalClause_literal_iff a C).mpr ⟨l, hlC, hlit⟩)
      · exact (evalClause_literal_iff a D).mpr ⟨l, hlD, hlit⟩
  · rintro (h1 | h2) E hE
    · obtain ⟨C, hC, hE'⟩ := List.mem_flatMap.mp hE
      obtain ⟨D, _, rfl⟩ := List.mem_map.mp hE'
      obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a C).mp (h1 C hC)
      exact (evalClause_literal_iff a (C ++ D)).mpr ⟨l, List.mem_append_left D hl, hlit⟩
    · obtain ⟨C, _, hE'⟩ := List.mem_flatMap.mp hE
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE'
      obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a D).mp (h2 D hD)
      exact (evalClause_literal_iff a (C ++ D)).mpr ⟨l, List.mem_append_right C hl, hlit⟩

private theorem evalCnf_append_eq (a : assgn) (N₁ N₂ : cnf) :
    evalCnf a (N₁ ++ N₂) = (evalCnf a N₁ && evalCnf a N₂) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true]
  rw [evalCnf_clause_iff, evalCnf_clause_iff, evalCnf_clause_iff]
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append_left N₂ hC),
      fun D hD => h D (List.mem_append_right N₁ hD)⟩
  · rintro ⟨h1, h2⟩ C hC
    rcases List.mem_append.mp hC with hC1 | hC2
    · exact h1 C hC1
    · exact h2 C hC2

private theorem filter_or_add_and {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x || q x)).length + (l.filter (fun x => p x && q x)).length =
      (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

end PvsNP.Units.m3_y_models_count_incl_excl

theorem PvsNP.Units.m3_y_models_count_incl_excl :
    ∀ (n : ℕ) (N₁ N₂ : cnf),
      ((List.range n).sublists.filter (fun a => evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D))))).length +
          ((List.range n).sublists.filter (fun a => evalCnf a (N₁ ++ N₂))).length =
        ((List.range n).sublists.filter (fun a => evalCnf a N₁)).length +
          ((List.range n).sublists.filter (fun a => evalCnf a N₂)).length := by
  intro n N₁ N₂
  have h1 : (fun a => evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D)))) =
      (fun a => evalCnf a N₁ || evalCnf a N₂) :=
    funext fun a => PvsNP.Units.m3_y_models_count_incl_excl.evalCnf_or_distrib a N₁ N₂
  have h2 : (fun a => evalCnf a (N₁ ++ N₂)) = (fun a => evalCnf a N₁ && evalCnf a N₂) :=
    funext fun a => PvsNP.Units.m3_y_models_count_incl_excl.evalCnf_append_eq a N₁ N₂
  rw [h1, h2]
  exact PvsNP.Units.m3_y_models_count_incl_excl.filter_or_add_and
    (fun a => evalCnf a N₁) (fun a => evalCnf a N₂) (List.range n).sublists
