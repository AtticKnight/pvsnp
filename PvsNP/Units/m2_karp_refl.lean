import Mathlib
import PvsNP.Defs
import CookLevin

/-- Karp reducibility is reflexive: the identity map reduces a language to itself, computed by
Mathlib's identity machine `Turing.idComputableInPolyTime`. -/
theorem PvsNP.Units.m2_karp_refl : ∀ L : Language Bool, PvsNP.KarpReducible L L :=
  fun _ => ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun _ => Iff.rfl⟩
