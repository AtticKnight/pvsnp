import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_mod_const
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

/-- The remainder of a length by a fixed number, in binary, takes polynomial time:
compute the remainder in unary, then convert unary to binary. -/
theorem PvsNP.Units.m2_tm_y_binary_length_mod_const :
    ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.length % k)) := by
  intro k
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length % k) true)
    (fun x : List Bool => Nat.bits x.length)
    (PvsNP.Units.m2_tm_unary_mod_const k)
    PvsNP.Units.m2_unary_to_binary_polytime
  have hfun : (fun x : List Bool => Nat.bits x.length) ∘
      (fun x : List Bool => List.replicate (x.length % k) true)
      = fun x : List Bool => Nat.bits (x.length % k) := by
    funext x
    simp [List.length_replicate]
  rw [hfun] at h
  exact h
