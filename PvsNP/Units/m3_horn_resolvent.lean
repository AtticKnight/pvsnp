import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_horn_resolvent

theorem filter_comm {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).filter q = (l.filter q).filter p := by
  simp only [List.filter_filter]
  apply List.filter_congr
  intro a _
  exact Bool.and_comm _ _

theorem eq_singleton_of_mem_of_length_le_one {α : Type} {l : List α} {x : α}
    (hx : x ∈ l) (h : l.length ≤ 1) : l = [x] := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hx
      rw [hx]
    | cons b t' =>
      simp only [List.length_cons] at h
      omega

theorem m3_horn_resolvent_aux (C D : clause) (v : var)
    (hC : (C.filter (fun l => l.1)).length ≤ 1)
    (hD : (D.filter (fun l => l.1)).length ≤ 1)
    (hCv : (true, v) ∈ C) (hDv : (false, v) ∈ D) :
    ((C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v)))).filter
      (fun l => l.1)).length ≤ 1 := by
  have hP : (C.filter (fun l => l.1)) = [(true, v)] :=
    eq_singleton_of_mem_of_length_le_one (List.mem_filter.mpr ⟨hCv, rfl⟩) hC
  have hC0 : ((C.filter (fun l => decide (l ≠ (true, v)))).filter (fun l => l.1)).length = 0 := by
    rw [filter_comm, hP]
    simp
  have hD1 : ((D.filter (fun l => decide (l ≠ (false, v)))).filter (fun l => l.1)).length ≤ 1 := by
    rw [filter_comm]
    exact (List.length_filter_le _ _).trans hD
  rw [List.filter_append, List.length_append, hC0]
  omega

end PvsNP.Units.m3_horn_resolvent

theorem PvsNP.Units.m3_horn_resolvent :
    ∀ (C D : clause) (v : var), (C.filter (fun l => l.1)).length ≤ 1 → (D.filter (fun l => l.1)).length ≤ 1 →
      (true, v) ∈ C → (false, v) ∈ D →
        ((C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v)))).filter
          (fun l => l.1)).length ≤ 1 := by
  intro C D v hC hD hCv hDv
  exact PvsNP.Units.m3_horn_resolvent.m3_horn_resolvent_aux C D v hC hD hCv hDv
