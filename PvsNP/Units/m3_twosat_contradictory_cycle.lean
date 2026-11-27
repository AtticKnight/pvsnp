import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_twosat_contradictory_cycle

lemma evalLiteral_neg (a : assgn) (p : literal) :
    evalLiteral a (!p.1, p.2) = !evalLiteral a p := by
  obtain ⟨s, v⟩ := p
  cases s <;> by_cases h : v ∈ a <;> simp [evalLiteral, evalVar, h]

lemma clause_step (a : assgn) (N : cnf) (hN : satisfiesCnf a N) (p q : literal)
    (h : [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (hp : evalLiteral a p = true) :
    evalLiteral a q = true := by
  have hall : ∀ C ∈ N, evalClause a C = true := by
    intro C hC
    unfold satisfiesCnf evalCnf at hN
    exact List.all_eq_true.mp hN C hC
  have hneg := evalLiteral_neg a p
  rw [hp] at hneg
  rcases h with h | h
  · have := hall _ h
    simp [evalClause, hneg] at this
    exact this
  · have := hall _ h
    simp [evalClause, hneg] at this
    exact this

lemma chain (a : assgn) (N : cnf) (hN : satisfiesCnf a N) (p q : literal)
    (h : Relation.ReflTransGen
      (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) p q)
    (hp : evalLiteral a p = true) : evalLiteral a q = true := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact clause_step a N hN _ _ hs ih

end PvsNP.Units.m3_twosat_contradictory_cycle

theorem PvsNP.Units.m3_twosat_contradictory_cycle :
    ∀ (N : cnf) (v : var),
      Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (true, v) (false, v) →
        Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (false, v) (true, v) →
          ¬ SAT N := by
  intro N v h1 h2 ⟨a, ha⟩
  by_cases hv : v ∈ a
  · have := PvsNP.Units.m3_twosat_contradictory_cycle.chain a N ha _ _ h1 (by simp [evalLiteral, evalVar, hv])
    simp [evalLiteral, evalVar, hv] at this
  · have := PvsNP.Units.m3_twosat_contradictory_cycle.chain a N ha _ _ h2 (by simp [evalLiteral, evalVar, hv])
    simp [evalLiteral, evalVar, hv] at this
