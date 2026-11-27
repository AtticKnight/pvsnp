import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.tf_fun_ones_unary

/-- Zip the input strings to obtain their mismatch bits, then count the true bits in unary. -/
theorem PvsNP.Units.m2_tm_hamming_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate ((List.zipWith (fun a b : Bool => a != b) p.1 p.2).count true) true) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a != b) p.1 p.2)
    (fun xs : List Bool => List.replicate (xs.count true) true)
    PvsNP.Units.m2_zip_bne_polytime PvsNP.Units.tf_fun_ones_unary
