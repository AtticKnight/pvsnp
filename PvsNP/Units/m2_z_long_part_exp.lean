import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_exp_union

/-!
The members longer than `m` of a language `L` in exponential time are `(Lᶜ ∪ {x | x.length ≤ m})ᶜ`.
Here `{x | x.length ≤ m}` is in `P` via a `(m + 2)`-state counter DFA (`m2_dfa_in_p`), hence in
`EXP` (`m2_p_subset_exp`), and `EXP` is closed under complement (`m2_exp_compl`) and union
(`m2_exp_union`).
-/

namespace PvsNP.Units.m2_z_long_part_exp

def step (m : ℕ) (q : Fin (m + 2)) (_ : Bool) : Fin (m + 2) :=
  if _ : q.val ≤ m then ⟨q.val + 1, by omega⟩ else q

def acc (m : ℕ) (q : Fin (m + 2)) : Bool :=
  decide (q.val ≤ m)

theorem foldl_val (m : ℕ) (x : List Bool) (q : Fin (m + 2)) :
    (x.foldl (step m) q).val = min (q.val + x.length) (m + 1) := by
  induction x generalizing q with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    have hq := q.isLt
    omega
  | cons b t ih =>
    rw [List.foldl_cons, ih, List.length_cons]
    dsimp only [step]
    split_ifs with h
    · simp only [Nat.add_assoc, Nat.add_comm 1 t.length]
    · have hq := q.isLt
      omega

theorem short_in_p (m : ℕ) :
    ({x : List Bool | x.length ≤ m} : Language Bool) ∈ PvsNP.P := by
  have heq : ({x : List Bool | x.length ≤ m} : Language Bool) =
      {x : List Bool | acc m (x.foldl (step m) 0) = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, acc, decide_eq_true_eq, foldl_val, Fin.val_zero, Nat.zero_add]
    omega
  rw [heq]
  exact PvsNP.Units.m2_dfa_in_p (Fin (m + 2)) (step m) 0 (acc m)

end PvsNP.Units.m2_z_long_part_exp

/-- The members longer than `m` of a language in exponential time form a language in exponential time (TM2). -/
theorem PvsNP.Units.m2_z_long_part_exp :
    ∀ (L : Language Bool) (m : ℕ),
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ ({x : List Bool | x ∈ L ∧ m < x.length} : Language Bool) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  intro L m hL
  have hLc := PvsNP.Units.m2_exp_compl L hL
  have hS := PvsNP.Units.m2_p_subset_exp ({x : List Bool | x.length ≤ m} : Language Bool)
    (PvsNP.Units.m2_z_long_part_exp.short_in_p m)
  have hU := PvsNP.Units.m2_exp_union Lᶜ ({x : List Bool | x.length ≤ m} : Language Bool) hLc hS
  have hC := PvsNP.Units.m2_exp_compl (Lᶜ ⊔ ({x : List Bool | x.length ≤ m} : Language Bool)) hU
  have heq : (Lᶜ ⊔ ({x : List Bool | x.length ≤ m} : Language Bool))ᶜ =
      ({x : List Bool | x ∈ L ∧ m < x.length} : Language Bool) := by
    ext x
    change ¬ (x ∉ L ∨ x.length ≤ m) ↔ x ∈ L ∧ m < x.length
    simp only [not_or, not_not, not_le]
  rwa [heq] at hC
