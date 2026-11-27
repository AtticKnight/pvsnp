import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_unit_clauses_sat_iff

end PvsNP.Units.m3_y_unit_clauses_sat_iff

theorem PvsNP.Units.m3_y_unit_clauses_sat_iff :
    ∀ ls : List literal, SAT (ls.map (fun l => [l])) ↔ ∀ l ∈ ls, (!l.1, l.2) ∉ ls := by
  intro ls
  constructor
  · rintro ⟨a, ha⟩
    intro l hl hcontra
    obtain ⟨s, v⟩ := l
    have h1 : evalClause a [(s, v)] = true :=
      (evalCnf_clause_iff a _).mp ha _ (List.mem_map.mpr ⟨(s, v), hl, rfl⟩)
    have h2 : evalClause a [(!s, v)] = true :=
      (evalCnf_clause_iff a _).mp ha _ (List.mem_map.mpr ⟨(!s, v), hcontra, rfl⟩)
    have e1 : evalLiteral a (s, v) = true := by
      obtain ⟨x, hx, hxx⟩ := (evalClause_literal_iff a [(s, v)]).mp h1
      rw [List.mem_singleton] at hx
      subst hx
      exact hxx
    have e2 : evalLiteral a (!s, v) = true := by
      obtain ⟨x, hx, hxx⟩ := (evalClause_literal_iff a [(!s, v)]).mp h2
      rw [List.mem_singleton] at hx
      subst hx
      exact hxx
    have d1 : evalVar a v = s := by simpa [evalLiteral] using e1
    have d2 : evalVar a v = !s := by simpa [evalLiteral] using e2
    have hss : s = !s := d1.symm.trans d2
    cases s <;> simp at hss
  · intro h
    refine ⟨(ls.filter (·.1)).map Prod.snd, ?_⟩
    show evalCnf _ _ = true
    rw [evalCnf_clause_iff]
    intro C hC
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hC
    rw [evalClause_literal_iff]
    refine ⟨l, List.mem_singleton.mpr rfl, ?_⟩
    obtain ⟨s, v⟩ := l
    cases s with
    | true =>
      have hv : v ∈ (ls.filter (·.1)).map Prod.snd :=
        List.mem_map.mpr ⟨(true, v), List.mem_filter.mpr ⟨hl, rfl⟩, rfl⟩
      simpa [evalLiteral, evalVar] using hv
    | false =>
      have hv : v ∉ (ls.filter (·.1)).map Prod.snd := by
        intro hmem
        obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hmem
        obtain ⟨hxls, hx1⟩ := List.mem_filter.mp hx
        have hxeq : x = (true, v) := Prod.ext hx1 hxv
        exact h (false, v) hl (hxeq ▸ hxls)
      simpa [evalLiteral, evalVar] using hv
