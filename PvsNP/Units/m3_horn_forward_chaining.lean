import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_horn_forward_chaining

def Closed (N : cnf) (S : Set var) : Prop :=
  ∀ D ∈ N, ∀ v : var, (true, v) ∈ D → (∀ m ∈ D, m.1 = false → m.2 ∈ S) → v ∈ S

theorem pos_unique {C : clause} (h : (C.filter (fun l => l.1)).length ≤ 1)
    {l₁ l₂ : literal} (h1 : l₁ ∈ C) (hp1 : l₁.1 = true) (h2 : l₂ ∈ C) (hp2 : l₂.1 = true) :
    l₁ = l₂ := by
  have hm1 : l₁ ∈ C.filter (fun l => l.1) := List.mem_filter.2 ⟨h1, hp1⟩
  have hm2 : l₂ ∈ C.filter (fun l => l.1) := List.mem_filter.2 ⟨h2, hp2⟩
  cases hf : C.filter (fun l => l.1) with
  | nil => rw [hf] at hm1; simp at hm1
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hf, List.mem_singleton] at hm1 hm2
      exact hm1.trans hm2.symm
    | cons y ys =>
      rw [hf] at h
      simp at h

theorem main :
    ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
      (SAT N ↔ ∀ C ∈ N, (∀ l ∈ C, l.1 = false) →
        ∃ S : Set var, (∀ D ∈ N, ∀ v : var, (true, v) ∈ D → (∀ m ∈ D, m.1 = false → m.2 ∈ S) → v ∈ S) ∧
          ∃ l ∈ C, l.2 ∉ S) := by
  classical
  intro N hhorn
  constructor
  · rintro ⟨a, ha⟩ C hCN hall
    refine ⟨{v : var | v ∈ a}, ?_, ?_⟩
    · intro D hDN v hvD hneg
      have hDa : evalClause a D = true := by
        simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha
        exact ha D hDN
      rw [evalClause, List.any_eq_true] at hDa
      obtain ⟨l, hlD, hle⟩ := hDa
      cases hl1 : l.1 with
      | false =>
        have hmem : l.2 ∈ a := hneg l hlD hl1
        rcases l with ⟨s, u⟩
        dsimp only at hl1 hmem
        subst hl1
        simp [evalLiteral, evalVar, hmem] at hle
      | true =>
        have heq := pos_unique (hhorn D hDN) hlD hl1 hvD rfl
        subst heq
        simpa [evalLiteral, evalVar] using hle
    · have hCa : evalClause a C = true := by
        simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha
        exact ha C hCN
      rw [evalClause, List.any_eq_true] at hCa
      obtain ⟨l, hlC, hle⟩ := hCa
      refine ⟨l, hlC, ?_⟩
      have hl1 := hall l hlC
      rcases l with ⟨s, u⟩
      dsimp only at hl1 ⊢
      subst hl1
      simpa [evalLiteral, evalVar] using hle
  · intro hrhs
    let M : Set var := {v : var | ∀ S : Set var, Closed N S → v ∈ S}
    have hM_closed : Closed N M := by
      intro D hDN v hvD hneg S hS
      exact hS D hDN v hvD (fun m hmD hm1 => hneg m hmD hm1 S hS)
    let a : assgn := (N.flatten.map Prod.snd).filter (fun v => decide (v ∈ M))
    have ha_iff : ∀ C ∈ N, ∀ l ∈ C, l.2 ∈ a ↔ l.2 ∈ M := by
      intro C hCN l hlC
      simp only [a, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
      intro _
      exact List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨C, hCN, hlC⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true]
    intro C hCN
    rw [evalClause, List.any_eq_true]
    by_cases hneg_out : ∃ l ∈ C, l.1 = false ∧ l.2 ∉ M
    · obtain ⟨l, hlC, hl1, hlM⟩ := hneg_out
      refine ⟨l, hlC, ?_⟩
      have hna : l.2 ∉ a := fun h => hlM ((ha_iff C hCN l hlC).1 h)
      rcases l with ⟨s, u⟩
      dsimp only at hl1 hna
      subst hl1
      simp [evalLiteral, evalVar, hna]
    · push_neg at hneg_out
      by_cases hpos : ∃ l ∈ C, l.1 = true
      · obtain ⟨⟨s, v⟩, hvC, hs⟩ := hpos
        dsimp only at hs
        subst hs
        have hvM : v ∈ M := hM_closed C hCN v hvC (fun m hmC hm1 => hneg_out m hmC hm1)
        have hva : v ∈ a := (ha_iff C hCN (true, v) hvC).2 hvM
        exact ⟨(true, v), hvC, by simp [evalLiteral, evalVar, hva]⟩
      · have hall : ∀ l ∈ C, l.1 = false := by
          intro l hlC
          cases hl1 : l.1 with
          | false => rfl
          | true => exact absurd ⟨l, hlC, hl1⟩ hpos
        obtain ⟨S, hS, l, hlC, hlS⟩ := hrhs C hCN hall
        have hlM : l.2 ∈ M := hneg_out l hlC (hall l hlC)
        exact absurd (hlM S hS) hlS

end PvsNP.Units.m3_horn_forward_chaining

theorem PvsNP.Units.m3_horn_forward_chaining :
    ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
      (SAT N ↔ ∀ C ∈ N, (∀ l ∈ C, l.1 = false) →
        ∃ S : Set var, (∀ D ∈ N, ∀ v : var, (true, v) ∈ D → (∀ m ∈ D, m.1 = false → m.2 ∈ S) → v ∈ S) ∧
          ∃ l ∈ C, l.2 ∉ S) :=
  PvsNP.Units.m3_horn_forward_chaining.main
