import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_append

/-- 追写一个固定符号的输出函数：读完输入后由终态吐出 `b`。 -/
def appF (b : Bool) : Unit → List Bool → List Bool
  | _, [] => [b]
  | _, c :: t => c :: appF b () t

def appδ (b : Bool) : Unit → Bool → Unit × Option Bool
  | _, c => ((), some c)

def appFin (b : Bool) : Unit → Option Bool := fun _ => some b

theorem appF_nil (b : Bool) (q : Unit) : appF b q [] = (appFin b q).toList := by
  cases q
  rfl

theorem appF_cons (b : Bool) (q : Unit) (c : Bool) (x : List Bool) :
    appF b q (c :: x) = (appδ b q c).2.toList ++ appF b (appδ b q c).1 x := by
  cases q
  rfl

theorem appF_eq (b : Bool) (x : List Bool) : appF b () x = x ++ [b] := by
  induction x with
  | nil => rfl
  | cons c t ih => simp [appF, ih]

/-- 追写单个符号是多项式时间可计算的（有限状态换能器）。 -/
theorem append_one_polyTime (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ [b]) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => appF b () x) :=
    PvsNP.Units.m2_transducer_polytime Unit (appδ b) (appFin b) (appF b)
      (appF_nil b) (appF_cons b) ()
  simpa [appF_eq] using h

end PvsNP.Units.tf_fun_append

theorem PvsNP.Units.tf_fun_append :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ [true, false]) := by
  have h1 := PvsNP.Units.tf_fun_append.append_one_polyTime true
  have h2 := PvsNP.Units.tf_fun_append.append_one_polyTime false
  have hc := PvsNP.Units.m2_polytime_comp (αΓ := Bool) (βΓ := Bool) (γΓ := Bool)
    (α := List Bool) (β := List Bool) (γ := List Bool)
    PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x ++ [true]) (fun x : List Bool => x ++ [false]) h1 h2
  convert hc using 2
  simp [List.append_assoc]
