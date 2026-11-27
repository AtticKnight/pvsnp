import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_coloring_encoding

lemma encode_inj {k u₁ u₂ c₁ c₂ : ℕ} (h1 : c₁ < k) (h2 : c₂ < k)
    (heq : u₁ * k + c₁ = u₂ * k + c₂) : u₁ = u₂ ∧ c₁ = c₂ := by
  have hu : u₁ = u₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (u₁ + 1) * k ≤ u₂ * k := Nat.mul_le_mul_right k hlt
      nlinarith
    · have : (u₂ + 1) * k ≤ u₁ * k := Nat.mul_le_mul_right k hgt
      nlinarith
  subst hu
  exact ⟨rfl, by omega⟩

end PvsNP.Units.m3_coloring_encoding

theorem PvsNP.Units.m3_coloring_encoding :
    ∀ (k : ℕ) (V : List var) (E : List (var × var)), (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) →
      (SAT (V.map (fun v => (List.range k).map (fun c => (true, v * k + c))) ++
          E.flatMap (fun e => (List.range k).map (fun c => [(false, e.1 * k + c), (false, e.2 * k + c)]))) ↔
        ∃ col : var → ℕ, (∀ v ∈ V, col v < k) ∧ ∀ e ∈ E, col e.1 ≠ col e.2) := by
  intro k V E hEV
  let F : cnf :=
    V.map (fun v => (List.range k).map (fun c => (true, v * k + c))) ++
      E.flatMap (fun e => (List.range k).map (fun c => [(false, e.1 * k + c), (false, e.2 * k + c)]))
  change SAT F ↔ _
  constructor
  · rintro ⟨a, ha⟩
    have hclauses := (evalCnf_clause_iff a F).mp ha
    have hvcol : ∀ v ∈ V, ∃ c < k, v * k + c ∈ a := by
      intro v hv
      have hmemC : (List.range k).map (fun c => (true, v * k + c)) ∈ F :=
        List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      obtain ⟨l, hlmem, hleval⟩ := (evalClause_literal_iff a _).mp (hclauses _ hmemC)
      obtain ⟨c, hcrange, rfl⟩ := List.mem_map.mp hlmem
      refine ⟨c, List.mem_range.mp hcrange, ?_⟩
      simp only [evalLiteral, evalVar, decide_eq_true_eq] at hleval
      exact hleval
    let col : var → ℕ := fun v => if hv : v ∈ V then Classical.choose (hvcol v hv) else 0
    have hcol_spec : ∀ v ∈ V, col v < k ∧ v * k + col v ∈ a := by
      intro v hv
      have hspec := Classical.choose_spec (hvcol v hv)
      simpa [col, hv] using hspec
    refine ⟨col, fun v hv => (hcol_spec v hv).1, fun e he heq => ?_⟩
    obtain ⟨he1, he2⟩ := hEV e he
    have hc1 := hcol_spec e.1 he1
    have hc2 := hcol_spec e.2 he2
    have hmemE : [(false, e.1 * k + col e.1), (false, e.2 * k + col e.1)] ∈ F := by
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.mpr ⟨e, he, ?_⟩
      exact List.mem_map.mpr ⟨col e.1, List.mem_range.mpr hc1.1, rfl⟩
    have hsatE := hclauses _ hmemE
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      evalLiteral, evalVar, decide_eq_true_eq, decide_eq_false_iff_not] at hsatE
    rcases hsatE with h1 | h2
    · exact h1 hc1.2
    · rw [heq] at h2
      exact h2 hc2.2
  · rintro ⟨col, hlt, hne⟩
    let a : assgn := V.map (fun v => v * k + col v)
    refine ⟨a, (evalCnf_clause_iff a F).mpr ?_⟩
    intro C hC
    rcases List.mem_append.mp hC with hCV | hCE
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hCV
      refine (evalClause_literal_iff a _).mpr ⟨(true, v * k + col v), ?_, ?_⟩
      · exact List.mem_map.mpr ⟨col v, List.mem_range.mpr (hlt v hv), rfl⟩
      · have hmem : v * k + col v ∈ a := List.mem_map.mpr ⟨v, hv, rfl⟩
        simp [evalLiteral, evalVar, hmem]
    · obtain ⟨e, he, hC1⟩ := List.mem_flatMap.mp hCE
      obtain ⟨c, hcrange, rfl⟩ := List.mem_map.mp hC1
      have hck : c < k := List.mem_range.mp hcrange
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        evalLiteral, evalVar, decide_eq_true_eq, decide_eq_false_iff_not]
      by_cases h1 : e.1 * k + c ∈ a
      · right
        intro h2
        obtain ⟨u₁, hu₁V, hu₁eq⟩ := List.mem_map.mp h1
        obtain ⟨u₂, hu₂V, hu₂eq⟩ := List.mem_map.mp h2
        obtain ⟨rfl, hc₁⟩ := PvsNP.Units.m3_coloring_encoding.encode_inj (hlt u₁ hu₁V) hck hu₁eq
        obtain ⟨rfl, hc₂⟩ := PvsNP.Units.m3_coloring_encoding.encode_inj (hlt u₂ hu₂V) hck hu₂eq
        exact hne e he (hc₁.trans hc₂.symm)
      · exact Or.inl h1
