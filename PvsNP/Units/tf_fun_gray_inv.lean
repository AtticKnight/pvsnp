import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_gray_inv

def gF : Bool → List Bool → List Bool
  | _, [] => []
  | q, b :: t => xor q b :: gF (xor q b) t

def gδ : Bool → Bool → Bool × Option Bool := fun q b => (xor q b, some (xor q b))

def gFin : Bool → Option Bool := fun _ => none

theorem gF_nil (q : Bool) : gF q [] = (gFin q).toList := rfl

theorem gF_cons (q : Bool) (b : Bool) (x : List Bool) :
    gF q (b :: x) = (gδ q b).2.toList ++ gF (gδ q b).1 x := rfl

theorem gF_snoc (q : Bool) (l : List Bool) (a : Bool) :
    gF q (l ++ [a]) = gF q l ++ [xor (l.foldl xor q) a] := by
  induction l generalizing q with
  | nil => rfl
  | cons b t ih => simp [gF, ih]

theorem key (q : Bool) (x : List Bool) :
    (gF q x.reverse).reverse = (List.scanr xor q x).dropLast := by
  induction x with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, gF_snoc, List.reverse_append, ih, List.scanr_cons]
    have hne : List.scanr xor q t ≠ [] := by simp
    rw [List.dropLast_cons_of_ne_nil hne, List.foldl_reverse]
    simp only [List.reverse_singleton, List.singleton_append]
    congr 1
    rw [Bool.xor_comm]
    congr 1
    induction t with
    | nil => rfl
    | cons c u ihu => simp [List.foldr, Bool.xor_comm]

theorem cpt_g : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (gF false) :=
  PvsNP.Units.m2_transducer_polytime Bool gδ gFin gF gF_nil gF_cons false

theorem comp2 {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (g ∘ f) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString f g hf hg

end PvsNP.Units.tf_fun_gray_inv

open PvsNP.Units.tf_fun_gray_inv in
theorem PvsNP.Units.tf_fun_gray_inv :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => (List.scanr xor false x).dropLast) := by
  have h := comp2 (comp2 PvsNP.Units.m2_reverse_polytime cpt_g) PvsNP.Units.m2_reverse_polytime
  have e : (fun x : List Bool => (List.scanr xor false x).dropLast) =
      (fun x : List Bool => x.reverse) ∘ gF false ∘ (fun x : List Bool => x.reverse) := by
    funext x
    simp only [Function.comp]
    exact (key false x).symm
  rw [e]; exact h
