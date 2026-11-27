import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_sat_to_monotone_sat

theorem evalLiteral_true_iff (a : assgn) (v : var) :
    evalLiteral a (true, v) = true ↔ v ∈ a := by
  by_cases hv : v ∈ a <;> simp [evalLiteral, evalVar, hv]

theorem evalLiteral_false_iff (a : assgn) (v : var) :
    evalLiteral a (false, v) = true ↔ v ∉ a := by
  by_cases hv : v ∈ a <;> simp [evalLiteral, evalVar, hv]

theorem mem_vs_of_mem {N : cnf} {C : clause} {l : literal}
    (hCN : C ∈ N) (hlC : l ∈ C) : l.2 ∈ N.flatten.map Prod.snd :=
  List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨C, hCN, hlC⟩, rfl⟩

theorem two_mul_inj {u v : ℕ} (h : 2 * u = 2 * v) : u = v := by omega
theorem two_mul_add_one_inj {u v : ℕ} (h : 2 * u + 1 = 2 * v + 1) : u = v := by omega
theorem two_mul_ne_add_one {u v : ℕ} (h : 2 * u + 1 = 2 * v) : False := by omega
theorem two_mul_ne_add_one' {u v : ℕ} (h : 2 * u = 2 * v + 1) : False := by omega

theorem sat_to_monotone_sat_aux (N : cnf) :
    SAT N ↔
      SAT (N.map (fun C => C.map (fun l => (true, if l.1 then 2 * l.2 else 2 * l.2 + 1))) ++
        (N.flatten.map Prod.snd).flatMap
          (fun v => [[(true, 2 * v), (true, 2 * v + 1)], [(false, 2 * v), (false, 2 * v + 1)]])) := by
  let vs : List var := N.flatten.map Prod.snd
  constructor
  · rintro ⟨a, ha⟩
    let b : assgn :=
      (vs.filter (fun v => decide (v ∈ a))).map (fun v => 2 * v) ++
        (vs.filter (fun v => decide (v ∉ a))).map (fun v => 2 * v + 1)
    have hmem_even : ∀ v ∈ vs, 2 * v ∈ b ↔ v ∈ a := by
      intro v hv
      simp only [b, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (⟨u, ⟨_, hua⟩, heq⟩ | ⟨u, _, heq⟩)
        · have huv : u = v := two_mul_inj heq
          subst huv
          exact hua
        · exact (two_mul_ne_add_one heq).elim
      · intro hva
        left
        exact ⟨v, ⟨hv, hva⟩, rfl⟩
    have hmem_odd : ∀ v ∈ vs, 2 * v + 1 ∈ b ↔ v ∉ a := by
      intro v hv
      simp only [b, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (⟨u, _, heq⟩ | ⟨u, ⟨_, huna⟩, heq⟩)
        · exact (two_mul_ne_add_one' heq).elim
        · have huv : u = v := two_mul_add_one_inj heq
          subst huv
          exact huna
      · intro hvna
        right
        exact ⟨v, ⟨hv, hvna⟩, rfl⟩
    refine ⟨b, (evalCnf_app_iff b _ _).mpr ⟨?_, ?_⟩⟩
    · rw [evalCnf_clause_iff]
      intro C' hC'
      obtain ⟨C, hCN, rfl⟩ := List.mem_map.mp hC'
      have hCa : evalClause a C = true := (evalCnf_clause_iff a N).mp ha C hCN
      obtain ⟨⟨s, v⟩, hlC, hla⟩ := (evalClause_literal_iff a C).mp hCa
      have hv : v ∈ vs := mem_vs_of_mem hCN hlC
      rw [evalClause_literal_iff]
      refine ⟨(true, if s then 2 * v else 2 * v + 1),
        List.mem_map.mpr ⟨(s, v), hlC, rfl⟩, ?_⟩
      rw [evalLiteral_true_iff]
      cases s with
      | true =>
        simp only [↓reduceIte]
        exact (hmem_even v hv).mpr ((evalLiteral_true_iff a v).mp hla)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (hmem_odd v hv).mpr ((evalLiteral_false_iff a v).mp hla)
    · rw [evalCnf_clause_iff]
      intro C' hC'
      obtain ⟨v, hv, hCmem⟩ := List.mem_flatMap.mp hC'
      have hcases : C' = [(true, 2 * v), (true, 2 * v + 1)] ∨
          C' = [(false, 2 * v), (false, 2 * v + 1)] := by
        simpa using hCmem
      by_cases hva : v ∈ a
      · have he : 2 * v ∈ b := (hmem_even v hv).mpr hva
        have ho : 2 * v + 1 ∉ b := fun h => ((hmem_odd v hv).mp h) hva
        rcases hcases with rfl | rfl
        · rw [evalClause_literal_iff]
          exact ⟨(true, 2 * v), by simp, (evalLiteral_true_iff b _).mpr he⟩
        · rw [evalClause_literal_iff]
          exact ⟨(false, 2 * v + 1), by simp, (evalLiteral_false_iff b _).mpr ho⟩
      · have he : 2 * v ∉ b := fun h => hva ((hmem_even v hv).mp h)
        have ho : 2 * v + 1 ∈ b := (hmem_odd v hv).mpr hva
        rcases hcases with rfl | rfl
        · rw [evalClause_literal_iff]
          exact ⟨(true, 2 * v + 1), by simp, (evalLiteral_true_iff b _).mpr ho⟩
        · rw [evalClause_literal_iff]
          exact ⟨(false, 2 * v), by simp, (evalLiteral_false_iff b _).mpr he⟩
  · rintro ⟨b, hb⟩
    obtain ⟨hpos, hlink⟩ := (evalCnf_app_iff b _ _).mp hb
    let a : assgn := vs.filter (fun v => decide (2 * v ∈ b))
    have hmem_a : ∀ v ∈ vs, v ∈ a ↔ 2 * v ∈ b := by
      intro v hv
      simp only [a, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
    refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
    intro C hCN
    have hCpos : evalClause b
        (C.map (fun l => (true, if l.1 then 2 * l.2 else 2 * l.2 + 1))) = true :=
      (evalCnf_clause_iff b _).mp hpos _ (List.mem_map.mpr ⟨C, hCN, rfl⟩)
    obtain ⟨l', hl'C, hlb⟩ := (evalClause_literal_iff b _).mp hCpos
    obtain ⟨⟨s, v⟩, hlC, rfl⟩ := List.mem_map.mp hl'C
    have hv : v ∈ vs := mem_vs_of_mem hCN hlC
    rw [evalLiteral_true_iff] at hlb
    rw [evalClause_literal_iff]
    refine ⟨(s, v), hlC, ?_⟩
    cases s with
    | true =>
      simp only [↓reduceIte] at hlb
      exact (evalLiteral_true_iff a v).mpr ((hmem_a v hv).mpr hlb)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hlb
      have hnegMem : [(false, 2 * v), (false, 2 * v + 1)] ∈
          vs.flatMap (fun v =>
            [[(true, 2 * v), (true, 2 * v + 1)], [(false, 2 * v), (false, 2 * v + 1)]]) :=
        List.mem_flatMap.mpr ⟨v, hv, by simp⟩
      have hnegSat : evalClause b [(false, 2 * v), (false, 2 * v + 1)] = true :=
        (evalCnf_clause_iff b _).mp hlink _ hnegMem
      obtain ⟨lneg, hlnegMem, hlnegSat⟩ := (evalClause_literal_iff b _).mp hnegSat
      have hcases : lneg = (false, 2 * v) ∨ lneg = (false, 2 * v + 1) := by
        simpa using hlnegMem
      have hnotEven : 2 * v ∉ b := by
        rcases hcases with rfl | rfl
        · exact (evalLiteral_false_iff b _).mp hlnegSat
        · exact absurd hlb ((evalLiteral_false_iff b _).mp hlnegSat)
      exact (evalLiteral_false_iff a v).mpr (fun h => hnotEven ((hmem_a v hv).mp h))

end PvsNP.Units.m3_sat_to_monotone_sat

/-- SAT reduces to monotone SAT by splitting each variable into positive and negative copies. -/
theorem PvsNP.Units.m3_sat_to_monotone_sat :
    ∀ N : cnf,
      SAT N ↔ SAT (N.map (fun C => C.map (fun l => (true, if l.1 then 2 * l.2 else 2 * l.2 + 1))) ++
        (N.flatten.map Prod.snd).flatMap (fun v => [[(true, 2 * v), (true, 2 * v + 1)], [(false, 2 * v), (false, 2 * v + 1)]])) :=
  PvsNP.Units.m3_sat_to_monotone_sat.sat_to_monotone_sat_aux
