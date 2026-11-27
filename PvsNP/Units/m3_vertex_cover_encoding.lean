import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-
The edge-clause encoding of vertex cover: the CNF with one two-literal clause
`[(true, u), (true, v)]` per edge `(u, v)` is satisfied by an assignment `a`
(the list of variables set true) exactly when every edge has an endpoint in `a`.

The proof is pure logic over the vendored CookLevin model: `satisfiesCnf` is
`evalCnf a N = true`, `evalCnf` is `List.all` of `evalClause`, and a clause is
`List.any` of `evalLiteral`; a positive literal `(true, v)` evaluates to true
exactly when `v ∈ a` (`evalLiteral` is `decide (evalVar a v = s)` and
`evalVar a v` is `decide (v ∈ a)`). No machine is involved.
-/

namespace PvsNP.Units.m3_vertex_cover_encoding

/-- A positive literal is true exactly when its variable is in the assignment. -/
theorem literal_true_iff (a : assgn) (v : var) :
    evalLiteral a (true, v) = true ↔ v ∈ a := by
  simp [evalLiteral, evalVar]

/-- The two-literal edge clause is true exactly when one of its endpoints is in
    the assignment. -/
theorem edge_clause_iff (a : assgn) (e : var × var) :
    evalClause a [(true, e.1), (true, e.2)] = true ↔ e.1 ∈ a ∨ e.2 ∈ a := by
  simp [evalClause, List.any_cons, List.any_nil, Bool.or_eq_true,
    PvsNP.Units.m3_vertex_cover_encoding.literal_true_iff]

end PvsNP.Units.m3_vertex_cover_encoding

/-- The edge-clause CNF is satisfied exactly when the assignment is a vertex cover. -/
theorem PvsNP.Units.m3_vertex_cover_encoding :
    ∀ (E : List (var × var)) (a : assgn),
      satisfiesCnf a (E.map (fun e => [(true, e.1), (true, e.2)])) ↔
        ∀ e ∈ E, e.1 ∈ a ∨ e.2 ∈ a := by
  intro E a
  constructor
  · intro h e he
    have hc := (evalCnf_clause_iff a _).mp h _ (List.mem_map_of_mem he)
    exact (PvsNP.Units.m3_vertex_cover_encoding.edge_clause_iff a e).mp hc
  · intro h
    apply (evalCnf_clause_iff a _).mpr
    intro C hC
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hC
    exact (PvsNP.Units.m3_vertex_cover_encoding.edge_clause_iff a e).mpr (h e he)
