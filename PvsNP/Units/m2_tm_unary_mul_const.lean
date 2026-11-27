import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_mul_polytime
import PvsNP.Units.m2_polytime_comp

/-!
# m2_tm_unary_mul_const

Pair the constant `1^k` with the input, then multiply the lengths in unary.
-/

theorem PvsNP.Units.m2_tm_unary_mul_const : ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (k * x.length) true) := by
  intro k
  have hc := PvsNP.Units.m2_const_polytime (List.replicate k true)
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) := ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hp := PvsNP.Units.m2_pair_build_polytime _ _ hc hid
  have h := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hp PvsNP.Units.m2_mul_polytime
  have heq : ((fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true) ∘
      (fun x : List Bool => (List.replicate k true, x))) =
      (fun x : List Bool => List.replicate (k * x.length) true) := by
    funext x
    simp
  rw [heq] at h
  exact h
