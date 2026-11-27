import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_var_disjoint_conj
import PvsNP.Units.m3_sat_rename

theorem PvsNP.Units.m3_y_shift_disjoint_sat :
    ∀ (N M : cnf) (k : ℕ), (∀ C ∈ N, ∀ l ∈ C, l.2 < k) →
      (SAT (N ++ M.map (fun C => C.map (fun l => (l.1, l.2 + k)))) ↔ SAT N ∧ SAT M) := by
  intro N M k hbound
  let shift (C : clause) : clause := C.map (fun l => (l.1, l.2 + k))
  have disjointVars : ∀ C ∈ N, ∀ D ∈ M.map shift, ∀ l ∈ C, ∀ m ∈ D, l.2 ≠ m.2 := by
    intro C hC D hD l hl m hm
    obtain ⟨E, _, rfl⟩ := List.mem_map.mp hD
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hm
    have small := hbound C hC l hl
    change l.2 ≠ p.2 + k
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le small (Nat.le_add_left k p.2))
  have inj : Function.Injective (fun v : var => v + k) := fun _ _ h => Nat.add_right_cancel h
  change SAT (N ++ M.map shift) ↔ SAT N ∧ SAT M
  rw [PvsNP.Units.m3_var_disjoint_conj N (M.map shift) disjointVars]
  exact and_congr_right' (PvsNP.Units.m3_sat_rename M (fun v => v + k) inj)
