import Mathlib
import PvsNP.Defs
import CookLevin

/-!
Padding each nonempty clause `C` of length `≤ k` to length `k` by repeating its first literal
`C.headD (true, 0)` preserves `evalClause a C` for every assignment `a` (since the added copies
evaluate identically to the head literal already in `C`), and hence preserves `evalCnf a N`.
-/

namespace PvsNP.Units.m3_y_pad_clause_repeat

theorem evalClause_replicate_false (a : assgn) (l : literal) (m : ℕ)
    (hl : evalLiteral a l = false) :
    evalClause a (List.replicate m l) = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, evalClause, List.any_cons, hl, Bool.false_or]
    exact ih

theorem evalClause_pad (a : assgn) (C : clause) (hC : C ≠ []) (k : ℕ) :
    evalClause a (C ++ List.replicate (k - C.length) (C.headD (true, 0))) = evalClause a C := by
  cases C with
  | nil => exact absurd rfl hC
  | cons l t =>
    simp only [List.headD_cons, List.cons_append, evalClause, List.any_cons, List.any_append]
    cases hl : evalLiteral a l with
    | true => simp
    | false =>
      have hrep : (List.replicate (k - (l :: t).length) l).any (evalLiteral a) = false :=
        evalClause_replicate_false a l _ hl
      rw [hrep, Bool.false_or, Bool.or_false, Bool.false_or]

end PvsNP.Units.m3_y_pad_clause_repeat

/-- Padding each nonempty clause of a k-CNF to length exactly k with copies of its first literal keeps every value (vendored model). -/
theorem PvsNP.Units.m3_y_pad_clause_repeat :
    ∀ (N : cnf) (k : ℕ), (∀ C ∈ N, C ≠ [] ∧ C.length ≤ k) →
      (∀ C ∈ N.map (fun C => C ++ List.replicate (k - C.length) (C.headD (true, 0))), C.length = k) ∧
        ∀ a : assgn,
          evalCnf a (N.map (fun C => C ++ List.replicate (k - C.length) (C.headD (true, 0)))) =
            evalCnf a N := by
  intro N k hN
  constructor
  · intro C hC
    rw [List.mem_map] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    have hlen := (hN C₀ hC₀).2
    simp only [List.length_append, List.length_replicate]
    omega
  · intro a
    induction N with
    | nil => rfl
    | cons C N ih =>
      have hC : C ≠ [] := (hN C (by simp)).1
      have hrest : ∀ D ∈ N, D ≠ [] ∧ D.length ≤ k := fun D hD => hN D (by simp [hD])
      simp only [List.map_cons, evalCnf, List.all_cons]
      rw [PvsNP.Units.m3_y_pad_clause_repeat.evalClause_pad a C hC k]
      congr 1
      exact ih hrest
