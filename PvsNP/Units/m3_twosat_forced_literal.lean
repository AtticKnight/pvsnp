import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_twosat_forced_literal

theorem eval_neg (a : assgn) (p : literal) :
    evalLiteral a (!p.1, p.2) = !evalLiteral a p := by
  obtain ⟨s, v⟩ := p
  simp only [evalLiteral]
  cases s <;> cases h : evalVar a v <;> simp

theorem step_true (a : assgn) (N : cnf) (hN : satisfiesCnf a N) (p q : literal)
    (h : [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (hp : evalLiteral a p = true) :
    evalLiteral a q = true := by
  have key : ∀ C ∈ N, evalClause a C = true := by
    intro C hC
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at hN
    exact hN C hC
  have hn := eval_neg a p
  rcases h with h | h
  · have := key _ h
    simp only [evalClause, List.any_cons, List.any_nil, hn, hp] at this
    simpa using this
  · have := key _ h
    simp only [evalClause, List.any_cons, List.any_nil, hn, hp] at this
    simpa using this

end PvsNP.Units.m3_twosat_forced_literal

theorem PvsNP.Units.m3_twosat_forced_literal :
    ∀ (N : cnf) (l : literal),
      Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) l (!l.1, l.2) →
        (SAT N ↔ SAT ([(!l.1, l.2)] :: N)) := by
  intro N l hr
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hprop : evalLiteral a l = true → evalLiteral a (!l.1, l.2) = true := by
      intro h0
      exact Relation.ReflTransGen.rec (motive := fun q _ => evalLiteral a q = true) h0
        (fun _ hbc ih => PvsNP.Units.m3_twosat_forced_literal.step_true a N ha _ _ hbc ih) hr
    have hl : evalLiteral a (!l.1, l.2) = true := by
      cases h : evalLiteral a l
      · simpa [PvsNP.Units.m3_twosat_forced_literal.eval_neg, h]
      · exact hprop h
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha ⊢
    refine ⟨?_, ha⟩
    simp [evalClause, hl]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha
    exact ha.2
