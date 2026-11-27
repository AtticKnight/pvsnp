import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_autarky

theorem lit_congr (a a' : assgn) (x : literal) (h : evalVar a' x.2 = evalVar a x.2) :
    evalLiteral a' x = evalLiteral a x := by
  rcases x with ⟨s, w⟩
  show decide (evalVar a' w = s) = decide (evalVar a w = s)
  rw [show evalVar a' w = evalVar a w from h]

theorem mix (a b : assgn) (vs : List var) :
    ∃ b' : assgn, (∀ u ∈ vs, evalVar b' u = evalVar a u) ∧
      (∀ u, u ∉ vs → evalVar b' u = evalVar b u) := by
  refine ⟨a.filter (fun u => decide (u ∈ vs)) ++ b.filter (fun u => decide (u ∉ vs)), ?_, ?_⟩
  · intro u hu
    simp [evalVar, List.mem_filter, hu]
  · intro u hu
    simp [evalVar, List.mem_filter, hu]

end PvsNP.Units.m3_autarky

theorem PvsNP.Units.m3_autarky :
    ∀ (N : cnf) (vs : List var) (a : assgn),
  (∀ C ∈ N, (∃ l ∈ C, l.2 ∈ vs) → ∃ l ∈ C, l.2 ∈ vs ∧ evalLiteral a l = true) →
    (SAT N ↔ SAT (N.filter (fun C => decide (∀ l ∈ C, l.2 ∉ vs)))) := by
  have lit_congr := PvsNP.Units.m3_autarky.lit_congr
  have mix := PvsNP.Units.m3_autarky.mix
  intro N vs a haut
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, (evalCnf_clause_iff b _).mpr fun C hC => ?_⟩
    exact (evalCnf_clause_iff b N).mp hb C (List.mem_filter.mp hC).1
  · rintro ⟨b, hb⟩
    obtain ⟨b', h1, h2⟩ := mix a b vs
    refine ⟨b', (evalCnf_clause_iff b' N).mpr fun C hC => ?_⟩
    rw [evalClause_literal_iff]
    by_cases ht : ∃ l ∈ C, l.2 ∈ vs
    · obtain ⟨l, hl, hlv, hla⟩ := haut C hC ht
      exact ⟨l, hl, by rw [lit_congr a b' l (h1 l.2 hlv)]; exact hla⟩
    · have hCf : C ∈ N.filter (fun C => decide (∀ l ∈ C, l.2 ∉ vs)) := by
        refine List.mem_filter.mpr ⟨hC, decide_eq_true ?_⟩
        intro l hl hlv
        exact ht ⟨l, hl, hlv⟩
      obtain ⟨k, hk, hkb⟩ :=
        (evalClause_literal_iff b C).mp ((evalCnf_clause_iff b _).mp hb C hCf)
      have hkv : k.2 ∉ vs := fun hkv => ht ⟨k, hk, hkv⟩
      exact ⟨k, hk, by rw [lit_congr b b' k (h2 k.2 hkv)]; exact hkb⟩
