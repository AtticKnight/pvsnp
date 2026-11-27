import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_composite_np
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union

set_option autoImplicit false

-- Built from the settled campaign units tl_lang_composite_np, m2_dfa_in_p, m2_p_subset_np, m2_np_union.

namespace PvsNP.Units.m2_x_prime_conp

def dfaStep (q : Bool × Bool) (b : Bool) : Bool × Bool := (true, q.2 || (q.1 && b))

def dfaAcc (q : Bool × Bool) : Bool := !q.2

theorem foldl_true (xs : List Bool) (t : Bool) :
    xs.foldl dfaStep (true, t) = (true, t || xs.any id) := by
  induction xs generalizing t with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons]
    show List.foldl dfaStep (true, t || (true && c)) cs = _
    rw [ih]
    simp [Bool.or_assoc]

theorem foldl_tail (x : List Bool) : (x.foldl dfaStep (false, false)).2 = x.tail.any id := by
  cases x with
  | nil => rfl
  | cons b xs =>
    rw [List.foldl_cons]
    show (List.foldl dfaStep (true, false || (false && b)) xs).2 = _
    rw [foldl_true]
    simp

theorem small_iff (x : List Bool) :
    dfaAcc (x.foldl dfaStep (false, false)) = true ↔ PvsNP.Units.tl_lang_composite_np.val x < 2 := by
  have h := PvsNP.Units.tl_lang_composite_np.one_lt_val_iff x
  unfold dfaAcc
  rw [foldl_tail]
  revert h
  cases x.tail.any id
  · intro h
    have h1 : ¬ 1 < PvsNP.Units.tl_lang_composite_np.val x := fun h' => absurd (h.1 h') (by simp)
    constructor
    · intro _; omega
    · intro _; rfl
  · intro h
    have h1 : 1 < PvsNP.Units.tl_lang_composite_np.val x := h.2 rfl
    constructor
    · intro h2; exact absurd h2 (by simp)
    · intro h2; omega

theorem not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n < 2 ∨ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  constructor
  · intro hn
    by_cases h2 : n < 2
    · exact Or.inl h2
    · right
      have h2' : 2 ≤ n := by omega
      obtain ⟨m, hdvd, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 h2' hn
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨m, k, by omega, ?_, hk.symm⟩
      by_contra hk1
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> omega
  · rintro (h | ⟨a, b, ha, hb, rfl⟩) hp
    · have := hp.two_le
      omega
    · rw [Nat.prime_mul_iff] at hp
      rcases hp with ⟨_, hb1⟩ | ⟨_, ha1⟩ <;> omega

end PvsNP.Units.m2_x_prime_conp

theorem PvsNP.Units.m2_x_prime_conp :
    ({x : List Bool | Nat.Prime (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))} : Language Bool) ∈ PvsNP.coNP := by
  have hS := PvsNP.Units.m2_dfa_in_p (Bool × Bool) PvsNP.Units.m2_x_prime_conp.dfaStep (false, false)
    PvsNP.Units.m2_x_prime_conp.dfaAcc
  have hU := PvsNP.Units.m2_np_union _ _ (PvsNP.Units.m2_p_subset_np hS)
    PvsNP.Units.tl_lang_composite_np
  show (_ : Language Bool)ᶜ ∈ PvsNP.NP
  convert hU using 1
  ext x
  show ¬ Nat.Prime (PvsNP.Units.tl_lang_composite_np.val x) ↔
    (PvsNP.Units.m2_x_prime_conp.dfaAcc (x.foldl PvsNP.Units.m2_x_prime_conp.dfaStep (false, false)) = true ∨
      ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = PvsNP.Units.tl_lang_composite_np.val x)
  rw [PvsNP.Units.m2_x_prime_conp.small_iff, PvsNP.Units.m2_x_prime_conp.not_prime_iff]
