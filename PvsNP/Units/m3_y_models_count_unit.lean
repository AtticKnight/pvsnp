import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_models_count_unit

private theorem map_same (xs : List (List ℕ)) (f : List ℕ → List ℕ) (p : List ℕ → Bool)
    (h : ∀ a, p (f a) = p a) :
    ((xs.map f).filter p).length = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases test : p a <;> simp [h a, test, ih]

private theorem complementary (xs : List (List ℕ)) (f : List ℕ → List ℕ) (p : List ℕ → Bool)
    (h : ∀ a ∈ xs, p (f a) = !(p a)) :
    (xs.filter p).length + ((xs.map f).filter p).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have next := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    have head := h a (by simp)
    cases test : p a <;> simp [head, test] <;> omega

end PvsNP.Units.m3_y_models_count_unit

theorem PvsNP.Units.m3_y_models_count_unit :
    ∀ (n : ℕ) (l : literal), l.2 < n →
      ((List.range n).sublists.filter (fun a => evalCnf a [[l]])).length = 2 ^ (n - 1) := by
  intro n
  induction n with
  | zero => rintro ⟨s, v⟩ h; exact (Nat.not_lt_zero v h).elim
  | succ n ih =>
    rintro ⟨s, v⟩ hv
    change v < n + 1 at hv
    let p : List ℕ → Bool := fun a => evalCnf a [[(s, v)]]
    change (((List.range (n + 1)).sublists).filter p).length = 2 ^ n
    rw [List.range_succ, List.sublists_concat, List.filter_append, List.length_append]
    by_cases he : v = n
    · subst v
      have toggle (a : List ℕ) (ha : a ∈ (List.range n).sublists) :
          p (a ++ [n]) = !(p a) := by
        have absent : n ∉ a := fun hn =>
          (Nat.lt_irrefl n) (List.mem_range.mp ((List.mem_sublists.mp ha).subset hn))
        cases s <;> simp [p, evalCnf, evalClause, evalLiteral, evalVar, absent]
      rw [PvsNP.Units.m3_y_models_count_unit.complementary _ _ _ toggle,
        List.length_sublists, List.length_range]
    · have same (a : List ℕ) : p (a ++ [n]) = p a := by
        by_cases member : v ∈ a <;> simp [p, evalCnf, evalClause, evalLiteral, evalVar, member, he]
      rw [PvsNP.Units.m3_y_models_count_unit.map_same _ _ _ same]
      have smaller : v < n := lt_of_le_of_ne (Nat.le_of_lt_succ hv) he
      have previous : ((List.range n).sublists.filter p).length = 2 ^ (n - 1) :=
        ih (s, v) smaller
      rw [previous]
      cases n with
      | zero => exact (Nat.not_lt_zero v smaller).elim
      | succ m => simp [Nat.pow_succ, Nat.mul_two]
