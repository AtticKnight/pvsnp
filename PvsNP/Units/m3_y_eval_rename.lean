import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_eval_rename :
    ∀ (N : cnf) (f : var → var) (a : assgn),
      evalCnf a (N.map (fun C => C.map (fun l => (l.1, f l.2)))) =
        evalCnf ((N.flatten.map Prod.snd).filter (fun v => decide (f v ∈ a))) N := by
  intro N f a
  let a' : assgn := (N.flatten.map Prod.snd).filter (fun v => decide (f v ∈ a))
  have hiff : evalCnf a (N.map (fun C => C.map (fun l => (l.1, f l.2)))) = true ↔
      evalCnf a' N = true := by
    simp only [evalCnf, List.all_map, List.all_eq_true, Function.comp_apply]
    apply forall_congr'
    intro C
    apply imp_congr_right
    intro hCN
    simp only [evalClause, List.any_map, List.any_eq_true, Function.comp_apply]
    apply exists_congr
    intro l
    apply and_congr_right
    intro hlC
    rcases l with ⟨s, v⟩
    have hv_mem : v ∈ N.flatten.map Prod.snd :=
      List.mem_map.mpr ⟨(s, v), List.mem_flatten.mpr ⟨C, hCN, hlC⟩, rfl⟩
    have hv_iff : v ∈ a' ↔ f v ∈ a := by
      simp only [a', List.mem_filter, decide_eq_true_eq, hv_mem, true_and]
    by_cases hfa : f v ∈ a
    · have hva : v ∈ a' := hv_iff.mpr hfa
      simp [evalLiteral, evalVar, hfa, hva]
    · have hva : v ∉ a' := fun hc => hfa (hv_iff.mp hc)
      simp [evalLiteral, evalVar, hfa, hva]
  cases h1 : evalCnf a (N.map (fun C => C.map (fun l => (l.1, f l.2)))) <;>
    cases h2 : evalCnf a' N <;> simp_all
