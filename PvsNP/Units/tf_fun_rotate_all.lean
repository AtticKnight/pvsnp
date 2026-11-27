import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_rotate
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tf_fun_rotate_all

/-- Iterating rotate-by-one `k` times is rotate-by-`k`. -/
theorem rotate_iter (k : ℕ) (x : List Bool) :
    (fun y : List Bool => y.rotate 1)^[k] x = x.rotate k := by
  induction k with
  | zero => simp [List.rotate_zero]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      show (x.rotate k).rotate 1 = x.rotate (k + 1)
      rw [List.rotate_rotate]

end PvsNP.Units.tf_fun_rotate_all

/-- Rotating by a fixed amount takes polynomial time (TM2): rotate-by-one is polynomial-time
(the settled unit `tf_fun_rotate`) and preserves length, so iterating it `k` times is
polynomial-time (the settled unit `m2_iterate_polytime`); feed the pair `(x, replicate k true)`
built from the identity and a constant. -/
theorem PvsNP.Units.tf_fun_rotate_all :
    ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.rotate k) := by
  intro k
  have hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate 1) :=
    PvsNP.Units.tf_fun_rotate
  have hlen : ∀ y : List Bool, ((fun x : List Bool => x.rotate 1) y).length ≤ y.length + 0 := by
    intro y
    simp [List.length_rotate]
  have hiter := PvsNP.Units.m2_iterate_polytime (fun x : List Bool => x.rotate 1) 0 hg hlen
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    PvsNP.Units.m2_pair_build_polytime.cpt_id
  have hconst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => List.replicate k true) :=
    PvsNP.Units.m2_const_polytime _
  have hpair := PvsNP.Units.m2_pair_build_polytime.cpt_pair hid hconst
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, List.replicate k true))
    (fun p : List Bool × List Bool => (fun x : List Bool => x.rotate 1)^[p.2.length] p.1)
    hpair hiter
  have hfun : (fun p : List Bool × List Bool => (fun x : List Bool => x.rotate 1)^[p.2.length] p.1) ∘
      (fun x : List Bool => (x, List.replicate k true)) = fun x : List Bool => x.rotate k := by
    funext x
    simp only [Function.comp_apply, List.length_replicate]
    exact PvsNP.Units.tf_fun_rotate_all.rotate_iter k x
  rw [← hfun]
  exact hcomp
