import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_divmod
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.m2_tm_unary_mod_const :
    ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length % k) true) := by
  intro k
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hconst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => List.replicate k true) :=
    PvsNP.Units.m2_const_polytime (List.replicate k true)
  have hpair := PvsNP.Units.m2_pair_build_polytime
    (fun x : List Bool => x) (fun _ : List Bool => List.replicate k true) hid hconst
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, List.replicate k true))
    (fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true)
    hpair PvsNP.Units.m2_tm_unary_divmod.2
  have heq : ((fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true) ∘
      (fun x : List Bool => (x, List.replicate k true))) =
      (fun x : List Bool => List.replicate (x.length % k) true) := by
    funext x
    simp [List.length_replicate]
  rwa [heq] at hcomp
