import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime

theorem PvsNP.Units.m2_tm_unary_header_split :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x.takeWhile id, (x.dropWhile id).drop 1)) := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.takeWhile id) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_hd
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (x.dropWhile id).drop 1) := by
    have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN :=
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN
    have heq : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN =
        (fun x : List Bool => (x.dropWhile id).drop 1) := by
      funext x
      exact (List.drop_one).symm
    rwa [heq] at hdrop
  exact PvsNP.Units.m2_pair_build_polytime _ _ h1 h2
