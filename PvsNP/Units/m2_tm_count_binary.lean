import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_count_pow2_p

/-- Count the true input bits in unary and convert their count to binary. -/
theorem PvsNP.Units.m2_tm_count_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (x.count true)) := PvsNP.Units.tl_lang_count_pow2_p.countBits_polyTime
