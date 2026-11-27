import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

/-- Writing two to the power of the length in binary takes polynomial time (TM2):
`Nat.bits (2 ^ n)` is `n` falses followed by one true, which a one-state
transducer writes (one false per input bit, then a true at the end). -/
theorem PvsNP.Units.tf_fun_pow2_len :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (2 ^ x.length)) := by
  have hbits : ∀ n : ℕ, Nat.bits (2 ^ n) = List.replicate n false ++ [true] := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : 2 ^ n ≠ 0 := by positivity
      rw [Nat.pow_succ, mul_comm (2 ^ n) 2, Nat.bit0_bits _ hne, ih]
      simp [List.replicate_succ]
  have hfun : (fun x : List Bool => Nat.bits (2 ^ x.length))
      = (fun x : List Bool => List.replicate x.length false ++ [true]) := by
    funext x
    exact hbits x.length
  rw [hfun]
  exact PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some false)) (fun _ => some true)
    (fun _ x => List.replicate x.length false ++ [true])
    (by intro q; rfl)
    (by intro q b x; rfl)
    ()
