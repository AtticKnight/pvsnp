import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-
Binary value mod 3 by a finite automaton: read the bits left to right (the
first bit is the least significant digit), keeping the value read so far mod 3
and the current power of two mod 3. The automaton is the one of the settled
unit `PvsNP.Units.m2_dfa_in_p`; only the state update and its correctness
against `Nat.ofDigits` are new here.

Note: `Fin 3` has no `NatCast` instance in the pinned Lean 4.36, so no
`ℕ`-to-`Fin 3` cast is used anywhere: the step is a plain `if`, and the
fold invariant is stated as `Nat.ModEq` on `.val`s, i.e. pure `ℕ` arithmetic.
-/

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_mod_p

/-- One step: add the bit's contribution, double the power of two. -/
def step (s : Fin 3 × Fin 3) (b : Bool) : Fin 3 × Fin 3 :=
  if b then (s.1 + s.2, 2 * s.2) else (s.1, 2 * s.2)

/-- Accept when the value read so far is 0 mod 3. -/
def accept (s : Fin 3 × Fin 3) : Bool :=
  decide (s.1 = 0)

/-- Folding the automaton over `x` from `(r, p)` adds `p` times the binary
value of `x` to `r`, and multiplies `p` by `2 ^ x.length` (both mod 3). -/
theorem foldl_step (x : List Bool) (r p : Fin 3) :
    (x.foldl step (r, p)).1.val
        ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) [MOD 3] ∧
      (x.foldl step (r, p)).2.val ≡ p.val * 2 ^ x.length [MOD 3] := by
  induction x generalizing r p with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp [Nat.ofDigits_nil]
      exact Nat.ModEq.refl _
    · simp
      exact Nat.ModEq.refl _
  | cons b xs ih =>
    cases b with
    | false =>
      show (xs.foldl step (r, 2 * p)).1.val
            ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) ((false :: xs).map Bool.toNat) [MOD 3] ∧
          (xs.foldl step (r, 2 * p)).2.val ≡ p.val * 2 ^ (false :: xs).length [MOD 3]
      obtain ⟨ih1, ih2⟩ := ih r (2 * p)
      have e2 : ((2 * p : Fin 3)).val = (2 * p.val) % 3 := by
        rw [Fin.val_mul, Fin.val_two]
      constructor
      · apply ih1.trans
        rw [e2]
        simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_false]
        have hA : (2 * p.val) % 3 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            ≡ (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) [MOD 3] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have h := Nat.ModEq.add_left r.val hA
        have hring : r.val + (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            = r.val + p.val * (0 + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by ring
        rw [hring] at h
        exact h
      · apply ih2.trans
        rw [e2]
        simp only [List.length_cons, pow_succ]
        have hA : (2 * p.val) % 3 * 2 ^ xs.length
            ≡ (2 * p.val) * 2 ^ xs.length [MOD 3] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hring : (2 * p.val) * 2 ^ xs.length = p.val * (2 ^ xs.length * 2) := by ring
        rw [hring] at hA
        exact hA
    | true =>
      show (xs.foldl step (r + p, 2 * p)).1.val
            ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) ((true :: xs).map Bool.toNat) [MOD 3] ∧
          (xs.foldl step (r + p, 2 * p)).2.val ≡ p.val * 2 ^ (true :: xs).length [MOD 3]
      obtain ⟨ih1, ih2⟩ := ih (r + p) (2 * p)
      have e1 : ((r + p : Fin 3)).val = (r.val + p.val) % 3 := Fin.val_add _ _
      have e2 : ((2 * p : Fin 3)).val = (2 * p.val) % 3 := by
        rw [Fin.val_mul, Fin.val_two]
      constructor
      · apply ih1.trans
        rw [e1, e2]
        simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_true]
        have hA : (2 * p.val) % 3 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            ≡ (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) [MOD 3] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hX : (r.val + p.val) % 3 ≡ r.val + p.val [MOD 3] := Nat.mod_modEq _ _
        have h := hX.add hA
        have hring : (r.val + p.val) + (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            = r.val + p.val * (1 + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by ring
        rw [hring] at h
        exact h
      · apply ih2.trans
        rw [e2]
        simp only [List.length_cons, pow_succ]
        have hA : (2 * p.val) % 3 * 2 ^ xs.length
            ≡ (2 * p.val) * 2 ^ xs.length [MOD 3] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hring : (2 * p.val) * 2 ^ xs.length = p.val * (2 ^ xs.length * 2) := by ring
        rw [hring] at hA
        exact hA

/-- The automaton accepts exactly the strings whose binary value is 0 mod 3. -/
theorem accept_iff (x : List Bool) :
    accept (x.foldl step (0, 1)) = true ↔
      Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 = 0 := by
  obtain ⟨h1, -⟩ := foldl_step x 0 1
  simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, Nat.one_mul] at h1
  have h1' : (x.foldl step (0, 1)).1.val % 3
      = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 := h1
  simp only [accept, decide_eq_true_eq]
  constructor
  · intro h
    have hv : (x.foldl step (0, 1)).1.val = 0 := congrArg Fin.val h
    rw [hv] at h1'
    exact h1'.symm
  · intro h
    apply Fin.ext
    rw [Fin.val_zero]
    have hlt := (x.foldl step (0, 1)).1.isLt
    rw [h] at h1'
    rwa [Nat.mod_eq_of_lt hlt] at h1'

end PvsNP.Units.tl_lang_val_mod_p

/-- The strings whose binary value is divisible by 3 are in P. -/
theorem PvsNP.Units.tl_lang_val_mod_p :
    ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 = 0} :
      Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 = 0} :
        Language Bool)
      = {x : List Bool |
        PvsNP.Units.tl_lang_val_mod_p.accept (x.foldl
          PvsNP.Units.tl_lang_val_mod_p.step (0, 1)) = true} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact (PvsNP.Units.tl_lang_val_mod_p.accept_iff x).symm
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p _ PvsNP.Units.tl_lang_val_mod_p.step (0, 1)
    PvsNP.Units.tl_lang_val_mod_p.accept
