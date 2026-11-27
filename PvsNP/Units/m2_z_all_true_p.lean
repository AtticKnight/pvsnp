import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

namespace PvsNP.Units.m2_z_all_true_p

theorem fold (x : List Bool) : ∀ q : Bool,
    x.foldl (fun q b => q && b) q = (q && x.all id) := by
  induction x with
  | nil => intro q; simp
  | cons b x ih =>
    intro q
    simp only [List.foldl_cons, ih, List.all_cons, id]
    cases q <;> cases b <;> simp

end PvsNP.Units.m2_z_all_true_p

theorem PvsNP.Units.m2_z_all_true_p : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_dfa_in_p Bool (fun q b => q && b) true id
  have e : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) =
      {x : List Bool | id (x.foldl (fun q b => q && b) true) = true} := by
    ext x
    show (∀ b ∈ x, b = true) ↔ id (x.foldl (fun q b => q && b) true) = true
    rw [PvsNP.Units.m2_z_all_true_p.fold]
    simp
  rw [e]
  exact h
