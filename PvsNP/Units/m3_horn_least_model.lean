import Mathlib
import PvsNP.Defs
import CookLevin

/-- Every satisfiable Horn CNF has a least satisfying assignment under inclusion. -/
theorem PvsNP.Units.m3_horn_least_model :
    ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) → SAT N →
      ∃ a : assgn, satisfiesCnf a N ∧ ∀ b : assgn, satisfiesCnf b N → ∀ v ∈ a, v ∈ b := by
  classical
  intro N hhorn hsat
  let a : assgn :=
    (N.flatten.map Prod.snd).filter (fun v => decide (∀ b : assgn, satisfiesCnf b N → v ∈ b))
  have ha_sub : ∀ b : assgn, satisfiesCnf b N → ∀ v ∈ a, v ∈ b := by
    intro b hb v hva
    simp only [a, List.mem_filter, decide_eq_true_eq] at hva
    exact hva.2 b hb
  refine ⟨a, ?_, ha_sub⟩
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]
  intro C hCN
  by_contra hCfalse
  have hno : ∀ l ∈ C, evalLiteral a l ≠ true := by
    intro l hlC hle
    apply hCfalse
    rw [evalClause, List.any_eq_true]
    exact ⟨l, hlC, hle⟩
  have hneg_in_a : ∀ v : var, (false, v) ∈ C → v ∈ a := by
    intro v hvC
    by_contra hva
    exact hno (false, v) hvC (by simp [evalLiteral, evalVar, hva])
  have hCh := hhorn C hCN
  cases hfl : C.filter (fun l => l.1) with
  | nil =>
    obtain ⟨b, hb⟩ := hsat
    have hCb : evalClause b C = true := by
      simp only [satisfiesCnf, evalCnf, List.all_eq_true] at hb
      exact hb C hCN
    rw [evalClause, List.any_eq_true] at hCb
    obtain ⟨⟨s, v⟩, hlC, hlb⟩ := hCb
    cases s with
    | true =>
      have hm : (true, v) ∈ C.filter (fun l => l.1) := List.mem_filter.2 ⟨hlC, rfl⟩
      rw [hfl] at hm
      simp at hm
    | false =>
      have hvb : v ∈ b := ha_sub b hb v (hneg_in_a v hlC)
      simp [evalLiteral, evalVar, hvb] at hlb
  | cons l₀ ls =>
    cases ls with
    | cons l₁ ls' =>
      rw [hfl] at hCh
      simp at hCh
    | nil =>
      have hl₀mem : l₀ ∈ C.filter (fun l => l.1) := by rw [hfl]; simp
      have hl₀C : l₀ ∈ C := (List.mem_filter.1 hl₀mem).1
      have hl₀pos : l₀.1 = true := (List.mem_filter.1 hl₀mem).2
      rcases l₀ with ⟨s₀, u⟩
      dsimp only at hl₀pos
      subst hl₀pos
      have hu_notin_a : u ∉ a := by
        intro hua
        exact hno (true, u) hl₀C (by simp [evalLiteral, evalVar, hua])
      have hu_in_vars : u ∈ N.flatten.map Prod.snd := by
        rw [List.mem_map]
        refine ⟨(true, u), ?_, rfl⟩
        rw [List.mem_flatten]
        exact ⟨C, hCN, hl₀C⟩
      have hex_b : ∃ b : assgn, satisfiesCnf b N ∧ u ∉ b := by
        by_contra hnone
        apply hu_notin_a
        refine List.mem_filter.2 ⟨hu_in_vars, decide_eq_true (fun b hb => ?_)⟩
        by_contra hub
        exact hnone ⟨b, hb, hub⟩
      obtain ⟨b, hb, hub⟩ := hex_b
      have hCb : evalClause b C = true := by
        simp only [satisfiesCnf, evalCnf, List.all_eq_true] at hb
        exact hb C hCN
      rw [evalClause, List.any_eq_true] at hCb
      obtain ⟨⟨s, v⟩, hlC, hlb⟩ := hCb
      cases s with
      | false =>
        have hvb : v ∈ b := ha_sub b hb v (hneg_in_a v hlC)
        simp [evalLiteral, evalVar, hvb] at hlb
      | true =>
        have hm : (true, v) ∈ C.filter (fun l => l.1) := List.mem_filter.2 ⟨hlC, rfl⟩
        rw [hfl, List.mem_singleton] at hm
        have hvu : v = u := (Prod.mk.inj hm).2
        subst hvu
        simp [evalLiteral, evalVar, hub] at hlb
