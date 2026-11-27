import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_cnf_distribution_dnf

theorem main :
    ∀ (a : assgn) (N : cnf),
      evalCnf a N =
        (N.foldr (fun (C : clause) (acc : List (List literal)) =>
          C.flatMap (fun l => acc.map (fun t => l :: t))) [[]]).any
          (fun t => t.all (evalLiteral a)) := by
  intro a N
  induction N with
  | nil => rfl
  | cons C N' ih =>
    apply Bool.eq_iff_iff.2
    simp only [evalCnf, List.all_cons, Bool.and_eq_true, List.foldr_cons,
      List.any_eq_true, List.mem_flatMap, List.mem_map]
    rw [← evalCnf, ih, List.any_eq_true]
    constructor
    · rintro ⟨hC, t, ht, htall⟩
      rw [evalClause, List.any_eq_true] at hC
      obtain ⟨l, hlC, hl⟩ := hC
      exact ⟨l :: t, ⟨l, hlC, t, ht, rfl⟩, by simp [hl, htall]⟩
    · rintro ⟨u, ⟨l, hlC, t, ht, rfl⟩, hall⟩
      simp only [List.all_cons, Bool.and_eq_true] at hall
      exact ⟨by rw [evalClause, List.any_eq_true]; exact ⟨l, hlC, hall.1⟩, t, ht, hall.2⟩

end PvsNP.Units.m3_cnf_distribution_dnf

theorem PvsNP.Units.m3_cnf_distribution_dnf :
    ∀ (a : assgn) (N : cnf),
      evalCnf a N =
        (N.foldr (fun (C : clause) (acc : List (List literal)) =>
          C.flatMap (fun l => acc.map (fun t => l :: t))) [[]]).any
          (fun t => t.all (evalLiteral a)) :=
  PvsNP.Units.m3_cnf_distribution_dnf.main
