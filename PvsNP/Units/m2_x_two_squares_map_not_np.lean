import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_sum_two_squares_np
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_transducer_polytime

namespace PvsNP.Units.m2_x_two_squares_map_not_np

open Turing

/-- Flipping every bit is polynomial-time: a one-state transducer that outputs the
negation of each bit it reads. -/
theorem map_not_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => u.map not) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ b => ((), some (!b)))
    (fun _ => none)
    (fun _ u => u.map not)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

/-- Bit-flipping Karp-reduces this language to the sums of two squares: flipping the
bits of `x` does not change the value the language tests, so membership is preserved
exactly. -/
theorem karp_reduce :
    PvsNP.KarpReducible
      ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 =
        Nat.ofDigits (2 : ℕ) ((x.map not).map Bool.toNat)} : Language Bool)
      ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 =
        Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) :=
  ⟨fun x => x.map not, map_not_polytime, fun x => Iff.rfl⟩

end PvsNP.Units.m2_x_two_squares_map_not_np

/-- The strings whose flipped bits have a value that is a sum of two squares are in NP:
bit-flipping is polynomial-time, so this language Karp-reduces to the sums of two
squares (settled), and NP is closed downward under Karp reductions. -/
theorem PvsNP.Units.m2_x_two_squares_map_not_np :
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 =
      Nat.ofDigits (2 : ℕ) ((x.map not).map Bool.toNat)} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_down_closed _ _
    PvsNP.Units.m2_x_two_squares_map_not_np.karp_reduce
    PvsNP.Units.tl_lang_sum_two_squares_np
