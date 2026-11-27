import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_prefix_parity

/-- 输出函数：状态是「到目前为止的奇偶」，每读一位先吐出旧奇偶，再用它更新状态；
收尾吐出最终奇偶，于是输出正好是 `scanl xor false x`。 -/
def pfF : Bool → List Bool → List Bool
  | q, [] => [q]
  | q, b :: t => q :: pfF (xor q b) t

def pfδ : Bool → Bool → Bool × Option Bool := fun q b => (xor q b, some q)

def pfFin : Bool → Option Bool := fun q => some q

theorem pfF_nil (q : Bool) : pfF q [] = (pfFin q).toList := by
  cases q <;> rfl

theorem pfF_cons (q : Bool) (b : Bool) (x : List Bool) :
    pfF q (b :: x) = (pfδ q b).2.toList ++ pfF (pfδ q b).1 x := by
  cases q <;> cases b <;> rfl

theorem pfF_eq (q : Bool) (x : List Bool) : pfF q x = List.scanl xor q x := by
  induction x generalizing q with
  | nil => rfl
  | cons b t ih => simp [pfF, ih]

theorem scanl_xor_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.scanl xor false x) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pfF false x) :=
    PvsNP.Units.m2_transducer_polytime Bool pfδ pfFin pfF pfF_nil pfF_cons false
  simpa [pfF_eq] using h

end PvsNP.Units.tf_fun_prefix_parity

theorem PvsNP.Units.tf_fun_prefix_parity :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.scanl xor false x) :=
  PvsNP.Units.tf_fun_prefix_parity.scanl_xor_polyTime
