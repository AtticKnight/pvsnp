import Mathlib
import PvsNP.Defs
import CookLevin

/-- A power of a polynomially bounded function is polynomially bounded: by induction on the
exponent, from products of polynomially bounded functions (`inOPoly_mul`). -/
theorem PvsNP.Units.m3_inopoly_pow :
    ∀ (f : ℕ → ℕ) (k : ℕ), inOPoly f → inOPoly (fun n => f n ^ k) := by
  intro f k hf
  induction k with
  | zero => simpa using inOPoly_const 1
  | succ k ih =>
    have h := inOPoly_mul ih hf
    simpa [pow_succ] using h
