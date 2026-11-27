import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_equiv_literal_subst :
    ∀ (N : cnf) (x y : var), x ≠ y →
      (SAT ([(false, x), (true, y)] :: [(true, x), (false, y)] :: N) ↔
        SAT (N.map (fun C => C.map (fun l => if l.2 = x then (l.1, y) else l)))) := by
  intro N x y hxy
  constructor
  · rintro ⟨a, ha⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha
    have h1 := ha [(false, x), (true, y)] (by simp)
    have h2 := ha [(true, x), (false, y)] (by simp)
    have hiff : x ∈ a ↔ y ∈ a := by
      by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;>
        simp [evalClause, evalLiteral, evalVar, hx, hy] at h1 h2 ⊢
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true]
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    have hCa := ha C (by simp [hC])
    simp only [evalClause, List.any_eq_true] at hCa ⊢
    obtain ⟨⟨s, v⟩, hmem, hev⟩ := hCa
    refine ⟨if v = x then (s, y) else (s, v), List.mem_map.mpr ⟨(s, v), hmem, rfl⟩, ?_⟩
    by_cases hv : v = x
    · simp only [hv, ite_true, evalLiteral, evalVar] at hev ⊢
      by_cases hx : x ∈ a
      · have hy : y ∈ a := hiff.mp hx
        simpa [hx, hy] using hev
      · have hy : y ∉ a := fun hc => hx (hiff.mpr hc)
        simpa [hx, hy] using hev
    · simp only [hv, ite_false]
      exact hev
  · rintro ⟨a, ha⟩
    let a' : assgn := if y ∈ a then x :: a else a.filter (fun v => decide (v ≠ x))
    have hxa' : x ∈ a' ↔ y ∈ a := by
      by_cases hy : y ∈ a <;> simp [a', hy]
    have hva' : ∀ v, v ≠ x → (v ∈ a' ↔ v ∈ a) := by
      intro v hv
      by_cases hy : y ∈ a <;> simp [a', hy, hv]
    have hya' : y ∈ a' ↔ y ∈ a := hva' y hxy.symm
    refine ⟨a', ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true]
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · by_cases hy : y ∈ a
      · simp [evalClause, evalLiteral, evalVar, hya'.mpr hy]
      · have hnx : x ∉ a' := fun hc => hy (hxa'.mp hc)
        simp [evalClause, evalLiteral, evalVar, hnx]
    · rcases List.mem_cons.mp hC with rfl | hC
      · by_cases hy : y ∈ a
        · simp [evalClause, evalLiteral, evalVar, hxa'.mpr hy]
        · have hny : y ∉ a' := fun hc => hy (hya'.mp hc)
          simp [evalClause, evalLiteral, evalVar, hny]
      · simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha
        have hCa := ha (C.map (fun l => if l.2 = x then (l.1, y) else l))
          (List.mem_map.mpr ⟨C, hC, rfl⟩)
        simp only [evalClause, List.any_eq_true] at hCa ⊢
        obtain ⟨l', hl', hev⟩ := hCa
        obtain ⟨⟨s, v⟩, hmem, rfl⟩ := List.mem_map.mp hl'
        refine ⟨(s, v), hmem, ?_⟩
        by_cases hv : v = x
        · simp only [hv, ite_true, evalLiteral, evalVar] at hev ⊢
          by_cases hy : y ∈ a
          · have hx : x ∈ a' := hxa'.mpr hy
            simpa [hy, hx] using hev
          · have hx : x ∉ a' := fun hc => hy (hxa'.mp hc)
            simpa [hy, hx] using hev
        · simp only [hv, ite_false, evalLiteral, evalVar] at hev ⊢
          by_cases hva : v ∈ a
          · have hva2 : v ∈ a' := (hva' v hv).mpr hva
            simpa [hva, hva2] using hev
          · have hva2 : v ∉ a' := fun hc => hva ((hva' v hv).mp hc)
            simpa [hva, hva2] using hev
