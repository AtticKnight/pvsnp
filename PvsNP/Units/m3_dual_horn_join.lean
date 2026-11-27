import Mathlib
import PvsNP.Defs
import CookLevin

/-!
# Unit `m3_dual_horn_join`

The satisfying assignments of a dual-Horn formula are closed under
union: in each clause, take a literal true under `a` and one true under
`b`. A positive one stays true under the larger assignment `a ++ b`.
If both are negative, they are the clause's one negative literal (the
dual-Horn condition allows at most one), whose variable lies in neither
`a` nor `b`, hence not in `a ++ b` either.
-/

namespace PvsNP.Units.m3_dual_horn_join

theorem mem_of_pos {x : assgn} {v : var}
    (h : evalLiteral x (true, v) = true) : v ∈ x := by
  simpa [evalLiteral, evalVar] using h

theorem not_mem_of_neg {x : assgn} {v : var}
    (h : evalLiteral x (false, v) = true) : v ∉ x := by
  simpa [evalLiteral, evalVar] using h

theorem pos_of_mem {x : assgn} {v : var} (h : v ∈ x) :
    evalLiteral x (true, v) = true := by
  simp [evalLiteral, evalVar, h]

theorem neg_of_not_mem {x : assgn} {v : var} (h : v ∉ x) :
    evalLiteral x (false, v) = true := by
  simp [evalLiteral, evalVar, h]

theorem eq_of_mem_of_length_le_one {α : Type} {l : List α}
    (h : l.length ≤ 1) {x y : α} (hx : x ∈ l) (hy : y ∈ l) : x = y := by
  cases l with
  | nil => cases hx
  | cons z l =>
    cases l with
    | nil =>
      have hx' : x = z := List.mem_singleton.mp hx
      have hy' : y = z := List.mem_singleton.mp hy
      rw [hx', hy']
    | cons w l =>
      exfalso
      simp only [List.length_cons] at h
      omega

end PvsNP.Units.m3_dual_horn_join

theorem PvsNP.Units.m3_dual_horn_join :
    ∀ (N : cnf) (a b : assgn), (∀ C ∈ N, (C.filter (fun l => !l.1)).length ≤ 1) →
      satisfiesCnf a N → satisfiesCnf b N → satisfiesCnf (a ++ b) N := by
  intro N a b hhorn ha hb
  have ha' : evalCnf a N = true := ha
  have hb' : evalCnf b N = true := hb
  show evalCnf (a ++ b) N = true
  rw [evalCnf_clause_iff] at ha' hb' ⊢
  intro C hC
  obtain ⟨la, hlaC, hla⟩ :=
    (evalClause_literal_iff a C).mp (ha' C hC)
  obtain ⟨lb, hlbC, hlb⟩ :=
    (evalClause_literal_iff b C).mp (hb' C hC)
  rw [evalClause_literal_iff]
  rcases la with ⟨sa, va⟩
  rcases lb with ⟨sb, vb⟩
  cases sa with
  | true =>
    refine ⟨(true, va), hlaC, ?_⟩
    apply PvsNP.Units.m3_dual_horn_join.pos_of_mem
    exact List.mem_append_left b
      (PvsNP.Units.m3_dual_horn_join.mem_of_pos hla)
  | false =>
    cases sb with
    | true =>
      refine ⟨(true, vb), hlbC, ?_⟩
      apply PvsNP.Units.m3_dual_horn_join.pos_of_mem
      exact List.mem_append_right a
        (PvsNP.Units.m3_dual_horn_join.mem_of_pos hlb)
    | false =>
      have hlaF : (false, va) ∈ C.filter (fun l => !l.1) := by
        rw [List.mem_filter]
        exact ⟨hlaC, rfl⟩
      have hlbF : (false, vb) ∈ C.filter (fun l => !l.1) := by
        rw [List.mem_filter]
        exact ⟨hlbC, rfl⟩
      have heq : (false, va) = (false, vb) :=
        PvsNP.Units.m3_dual_horn_join.eq_of_mem_of_length_le_one
          (hhorn C hC) hlaF hlbF
      have hva : va = vb := congrArg Prod.snd heq
      refine ⟨(false, va), hlaC, ?_⟩
      apply PvsNP.Units.m3_dual_horn_join.neg_of_not_mem
      rw [List.mem_append, not_or]
      refine ⟨PvsNP.Units.m3_dual_horn_join.not_mem_of_neg hla, ?_⟩
      rw [hva]
      exact PvsNP.Units.m3_dual_horn_join.not_mem_of_neg hlb
