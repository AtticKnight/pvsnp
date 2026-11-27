import Mathlib
import PvsNP.Defs
import CookLevin

/-
Provenance: upstream lean/PEqualNP/Library/Helpers/ExpBound.lean (exp_le_merge, 6 lines),
github.com/brilliant-hq/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9,
Apache License 2.0. The statement proved is the posted unit m2_exp_le_merge, verbatim.
-/

/-- Merging exponential bounds: A * (n+1)^D + B * (n+1)^E ≤ (A+B) * (n+1)^(D+E). -/
theorem PvsNP.Units.m2_exp_le_merge :
    ∀ A B D E n : ℕ, A * (n + 1) ^ D + B * (n + 1) ^ E ≤ (A + B) * (n + 1) ^ (D + E) := by
  intro A B D E n
  have h1 : (n + 1) ^ D ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ E ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  calc A * (n + 1) ^ D + B * (n + 1) ^ E
      ≤ A * (n + 1) ^ (D + E) + B * (n + 1) ^ (D + E) :=
        Nat.add_le_add (Nat.mul_le_mul le_rfl h1) (Nat.mul_le_mul le_rfl h2)
    _ = (A + B) * (n + 1) ^ (D + E) := (Nat.add_mul A B ((n + 1) ^ (D + E))).symm
