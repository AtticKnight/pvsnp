import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_tseitin_xor

namespace PvsNP.Units.m3_plaisted_greenbaum_aux

open PvsNP.Units.m3_tseitin_xor

def rest (z : var) (C : clause) := C.filter (fun l => decide (l ≠ (true, z)))
def expand (z : var) (u v : literal) (C : clause) : cnf :=
  if (true, z) ∈ C then [rest z C ++ [u], rest z C ++ [v]] else [C]

theorem flat (a : assgn) (N : cnf) (f : clause → cnf) :
    satisfiesCnf a (N.flatMap f) ↔ ∀ C ∈ N, evalCnf a (f C) = true := by
  simp only [satisfiesCnf, evalCnf_clause_iff, List.mem_flatMap]
  constructor
  · intro h C hc D hd
    exact h D ⟨C, hc, hd⟩
  · rintro h D ⟨C, hc, hd⟩
    exact h C hc D hd

theorem expanded (a : assgn) (z : var) (u v : literal) (C : clause) (hp : (true,z) ∈ C) :
    evalCnf a (expand z u v C) = true ↔
      (evalClause a (rest z C) = true ∨ evalLiteral a u = true) ∧
      (evalClause a (rest z C) = true ∨ evalLiteral a v = true) := by
  simp [expand, hp, evalCnf, evalClause, List.any_append, Bool.and_eq_true, Bool.or_eq_true]

theorem notZ (z : var) (C : clause) (hn : (false,z) ∉ C) (l : literal)
    (hl : l ∈ C) (ne : l ≠ (true,z)) : l.2 ≠ z := by
  obtain ⟨p,w⟩ := l
  rintro rfl
  cases p with
  | false => exact hn hl
  | true => exact ne rfl

theorem forward (N : cnf) (z : var) (u v : literal) (a : assgn)
    (ha : satisfiesCnf a ([(false,z),u] :: [(false,z),v] :: N)) :
    satisfiesCnf a (N.flatMap (expand z u v)) := by
  have all := (evalCnf_clause_iff a _).1 ha
  have h1 : evalLiteral a (false,z) = true ∨ evalLiteral a u = true := by
    simpa [evalClause, Bool.or_eq_true] using all [(false,z),u] (by simp)
  have h2 : evalLiteral a (false,z) = true ∨ evalLiteral a v = true := by
    simpa [evalClause, Bool.or_eq_true] using all [(false,z),v] (by simp)
  apply (flat a N _).2
  intro C hc
  have satC := all C (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
  by_cases hp : (true,z) ∈ C
  · apply (expanded a z u v C hp).2
    obtain ⟨l, hl, lit⟩ := (evalClause_literal_iff a C).1 satC
    by_cases same : l = (true,z)
    · subst l
      have hn : evalLiteral a (false,z) ≠ true := by
        cases h : evalVar a z <;> simp_all [evalLiteral]
      exact ⟨Or.inr (h1.resolve_left hn), Or.inr (h2.resolve_left hn)⟩
    · have r : evalClause a (rest z C) = true :=
        (evalClause_literal_iff a _).2 ⟨l, by simp [rest, hl, same], lit⟩
      exact ⟨Or.inl r, Or.inl r⟩
  · simpa [expand, hp, evalCnf] using satC

theorem backward (N : cnf) (z : var) (u v : literal) (hu : u.2 ≠ z) (hv : v.2 ≠ z)
    (hn : ∀ C ∈ N, (false,z) ∉ C) (a : assgn) (ha : satisfiesCnf a (N.flatMap (expand z u v))) :
    SAT ([(false,z),u] :: [(false,z),v] :: N) := by
  let b := evalLiteral a u && evalLiteral a v
  let a' := setZ a z b
  have guard (l : literal) (hl : l.2 ≠ z) (ok : b = true → evalLiteral a l = true) :
      evalClause a' [(false,z),l] = true := by
    simp only [a', evalClause, List.any_cons, List.any_nil, Bool.or_false,
      evalLiteral_setZ_z, evalLiteral_setZ_ne a z b l hl]
    cases hb : b with
    | false => simp
    | true => simp [ok hb]
  have gu := guard u hu (fun h => (Bool.and_eq_true_iff.mp h).1)
  have gv := guard v hv (fun h => (Bool.and_eq_true_iff.mp h).2)
  have original : evalCnf a' N = true := by
    apply (evalCnf_clause_iff a' N).2
    intro C hc
    have hit := (flat a N _).1 ha C hc
    by_cases hp : (true,z) ∈ C
    · have choices := (expanded a z u v C hp).1 hit
      by_cases hr : evalClause a (rest z C) = true
      · obtain ⟨l, hl, good⟩ := (evalClause_literal_iff a _).1 hr
        have facts : l ∈ C ∧ l ≠ (true,z) := by simpa [rest] using hl
        exact (evalClause_literal_iff a' C).2 ⟨l, facts.1,
          (evalLiteral_setZ_ne a z b l (notZ z C (hn C hc) l facts.1 facts.2)).trans good⟩
      · have hb : b = true := Bool.and_eq_true_iff.mpr ⟨choices.1.resolve_left hr, choices.2.resolve_left hr⟩
        apply (evalClause_literal_iff a' C).2
        exact ⟨(true,z), hp, by simp [a', evalLiteral_setZ_z, hb]⟩
    · have plain : evalClause a C = true := by simpa [expand, hp, evalCnf] using hit
      rw [show evalClause a' C = evalClause a C from evalClause_setZ a z b C
        (fun l hl => notZ z C (hn C hc) l hl (fun eq => hp (eq ▸ hl)))]
      exact plain
  refine ⟨a', ?_⟩
  change (evalClause a' [(false,z),u] && (evalClause a' [(false,z),v] && evalCnf a' N)) = true
  simp [gu, gv, original]

end PvsNP.Units.m3_plaisted_greenbaum_aux

open PvsNP.Units.m3_plaisted_greenbaum_aux in
theorem PvsNP.Units.m3_plaisted_greenbaum :
    ∀ (N : cnf) (z : var) (l₁ l₂ : literal), l₁.2 ≠ z → l₂.2 ≠ z →
      (∀ C ∈ N, (false, z) ∉ C) →
      (SAT ([(false, z), l₁] :: [(false, z), l₂] :: N) ↔
        SAT (N.flatMap (fun C => if (true, z) ∈ C then
          [C.filter (fun l => decide (l ≠ (true, z))) ++ [l₁],
           C.filter (fun l => decide (l ≠ (true, z))) ++ [l₂]] else [C]))) := by
  intro N z u v hu hv hn
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, forward N z u v a ha⟩
  · rintro ⟨a, ha⟩
    exact backward N z u v hu hv hn a ha
