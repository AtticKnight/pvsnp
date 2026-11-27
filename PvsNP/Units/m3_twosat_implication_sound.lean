import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_twosat_implication_sound

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

end PvsNP.Units.m3_twosat_implication_sound

theorem PvsNP.Units.m3_twosat_implication_sound :
    ∀ (N : cnf) (a : assgn) (l m : literal), satisfiesCnf a N →
      Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) l m →
        evalLiteral a l = true → evalLiteral a m = true := by
  intro N a l m hN hr hl
  exact Relation.ReflTransGen.rec (motive := fun q _ => evalLiteral a q = true) hl
    (fun _ hbc ih => PvsNP.Units.m3_twosat_implication_sound.step_true a N hN _ _ hbc ih) hr
