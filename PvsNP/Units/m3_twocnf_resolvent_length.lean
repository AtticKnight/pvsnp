import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_twocnf_resolvent_length

theorem flt (l : clause) (x : literal) (h : x ∈ l) :
    (l.filter (fun y => decide (y ≠ x))).length + 1 ≤ l.length := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases hax : a = x
    · subst hax
      have hd : decide (a ≠ a) = false := by simp
      rw [hd]
      simp only [Bool.false_eq_true, if_false, List.length_cons]
      have := List.length_filter_le (fun y => decide (y ≠ a)) l
      omega
    · have hd : decide (a ≠ x) = true := by simp [hax]
      rw [hd]
      simp only [if_true, List.length_cons]
      have hx : x ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hax
        · exact h
      have := ih hx
      omega

end PvsNP.Units.m3_twocnf_resolvent_length

theorem PvsNP.Units.m3_twocnf_resolvent_length :
    ∀ (C D : clause) (v : var), C.length ≤ 2 → D.length ≤ 2 → (true, v) ∈ C → (false, v) ∈ D →
      (C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v)))).length ≤ 2 := by
  intro C D v hC hD hCv hDv
  have _hc := Classical.em True
  rw [List.length_append]
  have h1 : (C.filter (fun l => decide (l ≠ (true, v)))).length + 1 ≤ C.length :=
    PvsNP.Units.m3_twocnf_resolvent_length.flt C _ hCv
  have h2 : (D.filter (fun l => decide (l ≠ (false, v)))).length + 1 ≤ D.length :=
    PvsNP.Units.m3_twocnf_resolvent_length.flt D _ hDv
  omega
