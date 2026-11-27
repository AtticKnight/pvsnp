import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_two_pass_polytime

/-
Prediction module m2_x_reverse_map_not_polytime: sibling statements of the tf_fun_self_append family (a binary string written
together with a second copy, reversed or complemented), proved from settled campaign units only: the
machines cpt_id and cpt_app2 of PvsNP.Units.fr_ladner (adapted there from github.com/open-goat/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9, lean/PEqualNP/Library/Machines.lean and
lean/PEqualNP/Library/Universal.lean, Apache License 2.0), m2_reverse_polytime, m2_two_pass_polytime and
m2_polytime_comp.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_x_reverse_map_not_polytime

theorem ofEq {f g : List Bool → List Bool}
    (h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) (e : ∀ x, f x = g x) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g := by
  have hfg : f = g := funext e
  rw [← hfg]
  exact h

theorem comp {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x => g (f x)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString f g hf hg

theorem app2 {u v : List Bool → List Bool}
    (hu : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString u)
    (hv : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString v) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x => u x ++ v x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2 hu hv

theorem idp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id

theorem revP : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse) :=
  PvsNP.Units.m2_reverse_polytime

theorem fm_none (x : List Bool) : x.filterMap (fun _ : Bool => (none : Option Bool)) = [] := by
  induction x with
  | nil => rfl
  | cons b t ih => exact ih

theorem mapP (f : Bool → Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.map f) :=
  ofEq (PvsNP.Units.m2_two_pass_polytime (fun b => some (f b)) (fun _ => none)) (fun x => by
    rw [fm_none, List.append_nil]
    induction x with
    | nil => rfl
    | cons b t ih => simp [ih])

theorem notP : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.map not) :=
  mapP not

theorem lenP (c : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length c) :=
  ofEq (mapP (fun _ => c)) (fun x => by
    induction x with
    | nil => rfl
    | cons b t ih => simp [List.replicate_succ, ih])



theorem h_rev_self : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse ++ x) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.revP PvsNP.Units.m2_x_reverse_map_not_polytime.idp

theorem h_self_rev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ x.reverse) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.idp PvsNP.Units.m2_x_reverse_map_not_polytime.revP

theorem h_triple : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ x ++ x) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 (PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.idp PvsNP.Units.m2_x_reverse_map_not_polytime.idp) PvsNP.Units.m2_x_reverse_map_not_polytime.idp

theorem h_self_not : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ x.map not) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.idp PvsNP.Units.m2_x_reverse_map_not_polytime.notP

theorem h_not_self : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.map not ++ x) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.notP PvsNP.Units.m2_x_reverse_map_not_polytime.idp

theorem h_rev_not : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse.map not) := PvsNP.Units.m2_x_reverse_map_not_polytime.comp PvsNP.Units.m2_x_reverse_map_not_polytime.revP PvsNP.Units.m2_x_reverse_map_not_polytime.notP

theorem h_not_rev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => (x.map not).reverse) := PvsNP.Units.m2_x_reverse_map_not_polytime.comp PvsNP.Units.m2_x_reverse_map_not_polytime.notP PvsNP.Units.m2_x_reverse_map_not_polytime.revP

theorem h_rev_rev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse ++ x.reverse) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.revP PvsNP.Units.m2_x_reverse_map_not_polytime.revP

theorem h_pad_f : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ List.replicate x.length false) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 PvsNP.Units.m2_x_reverse_map_not_polytime.idp (PvsNP.Units.m2_x_reverse_map_not_polytime.lenP false)

theorem h_pad_t : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true ++ x) := PvsNP.Units.m2_x_reverse_map_not_polytime.app2 (PvsNP.Units.m2_x_reverse_map_not_polytime.lenP true) PvsNP.Units.m2_x_reverse_map_not_polytime.idp

end PvsNP.Units.m2_x_reverse_map_not_polytime

theorem PvsNP.Units.m2_x_reverse_map_not_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => (x.map not).reverse) :=
  PvsNP.Units.m2_x_reverse_map_not_polytime.h_not_rev
