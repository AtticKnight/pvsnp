import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

namespace PvsNP.Units.tl_lang_count_mod_all_p

private theorem count_eq_in_p (r : ℕ) :
    ({x : List Bool | x.count true = r} : Language Bool) ∈ PvsNP.P := by
  let δ : Fin (r + 2) → Bool → Fin (r + 2) :=
    fun q b => if b then ⟨min (q.val + 1) (r + 1), by omega⟩ else q
  have hfold : ∀ (x : List Bool) (q : Fin (r + 2)),
      (x.foldl δ q).val = min (q.val + x.count true) (r + 1) := by
    intro x
    induction x with
    | nil =>
      intro q
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      omega
    | cons b y ih =>
      intro q
      cases b with
      | false =>
        simp only [List.foldl_cons, δ, Bool.false_eq_true, ↓reduceIte,
          List.count_cons_of_ne (by decide : false ≠ true)]
        exact ih q
      | true =>
        simp only [List.foldl_cons, δ, ↓reduceIte, List.count_cons_self]
        rw [ih]
        dsimp only
        omega
  have hdfa := PvsNP.Units.m2_dfa_in_p (Fin (r + 2)) δ ⟨0, by omega⟩ (fun q => decide (q.val = r))
  have heq : ({x : List Bool | decide ((x.foldl δ ⟨0, by omega⟩).val = r) = true} : Language Bool) =
      ({x : List Bool | x.count true = r} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, decide_eq_true_eq, hfold x ⟨0, by omega⟩, Nat.zero_add]
    omega
  rwa [← heq]

private theorem count_mod_pos_in_p (m r : ℕ) (hm : 0 < m) :
    ({x : List Bool | x.count true % m = r} : Language Bool) ∈ PvsNP.P := by
  let δ : Fin m → Bool → Fin m :=
    fun q b => if b then ⟨(q.val + 1) % m, Nat.mod_lt _ hm⟩ else q
  have hfold : ∀ (x : List Bool) (q : Fin m),
      (x.foldl δ q).val = (q.val + x.count true) % m := by
    intro x
    induction x with
    | nil =>
      intro q
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact (Nat.mod_eq_of_lt q.isLt).symm
    | cons b y ih =>
      intro q
      cases b with
      | false =>
        simp only [List.foldl_cons, δ, Bool.false_eq_true, ↓reduceIte,
          List.count_cons_of_ne (by decide : false ≠ true)]
        exact ih q
      | true =>
        simp only [List.foldl_cons, δ, ↓reduceIte, List.count_cons_self]
        rw [ih]
        dsimp only
        rw [Nat.mod_add_mod]
        congr 1
        omega
  have hdfa := PvsNP.Units.m2_dfa_in_p (Fin m) δ ⟨0, hm⟩ (fun q => decide (q.val = r))
  have heq : ({x : List Bool | decide ((x.foldl δ ⟨0, hm⟩).val = r) = true} : Language Bool) =
      ({x : List Bool | x.count true % m = r} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, decide_eq_true_eq, hfold x ⟨0, hm⟩, Nat.zero_add]
  rwa [← heq]

theorem main :
    ∀ m r : ℕ, ({x : List Bool | x.count true % m = r} : Language Bool) ∈ PvsNP.P := by
  intro m r
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa only [Nat.mod_zero] using count_eq_in_p r
  · exact count_mod_pos_in_p m r hm

end PvsNP.Units.tl_lang_count_mod_all_p

theorem PvsNP.Units.tl_lang_count_mod_all_p :
    ∀ m r : ℕ, ({x : List Bool | x.count true % m = r} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_count_mod_all_p.main
