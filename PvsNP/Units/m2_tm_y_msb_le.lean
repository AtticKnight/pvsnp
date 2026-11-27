import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

/-- Comparing two binary numerals written most significant bit first takes
polynomial time (TM2).

Reverse both strings (the settled unit `m2_reverse_polytime` on each part, by
the settled unit `m2_prod_map_polytime`), then compare the reversed strings
(the settled unit `m2_binary_le_polytime`, which compares least-significant-bit
first numerals), composed by the settled unit `m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_y_msb_le :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.reverse.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.reverse.map Bool.toNat))) := by
  -- Reverse both components of the pair.
  have hrev : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse)) :=
    PvsNP.Units.m2_prod_map_polytime _ _ PvsNP.Units.m2_reverse_polytime
      PvsNP.Units.m2_reverse_polytime
  -- The comparison on least-significant-bit-first numerals is polytime.
  have hle := PvsNP.Units.m2_binary_le_polytime
  -- Compose: reverse, then compare.
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse))
    (fun p : List Bool × List Bool =>
      decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤
        Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    hrev hle
