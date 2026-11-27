import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_erase_true

/-- 输出函数：状态 `k` 表示「第一个 true 是否已经删掉」。 -/
def erF : Bool → List Bool → List Bool
  | true, [] => []
  | true, b :: t => b :: erF true t
  | false, [] => []
  | false, b :: t => if b then erF true t else b :: erF false t

def erδ : Bool → Bool → Bool × Option Bool
  | true, b => (true, some b)
  | false, b => if b then (true, none) else (false, some b)

def erFin : Bool → Option Bool := fun _ => none

theorem erF_nil (q : Bool) : erF q [] = (erFin q).toList := by
  cases q <;> rfl

theorem erF_cons (q : Bool) (b : Bool) (x : List Bool) :
    erF q (b :: x) = (erδ q b).2.toList ++ erF (erδ q b).1 x := by
  cases q with
  | true => rfl
  | false => cases b <;> rfl

/-- 已经删过之后输出就是原样照抄。 -/
theorem erF_true (x : List Bool) : erF true x = x := by
  induction x with
  | nil => rfl
  | cons b t ih => simp [erF, ih]

/-- 起点状态输出正是「删掉第一个 true」。 -/
theorem erF_false (x : List Bool) : erF false x = x.erase true := by
  induction x with
  | nil => rfl
  | cons b t ih => cases b <;> simp [erF, erF_true, ih]

theorem erase_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.erase true) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => erF false x) :=
    PvsNP.Units.m2_transducer_polytime Bool erδ erFin erF erF_nil erF_cons false
  simpa [erF_false] using h

end PvsNP.Units.tf_fun_erase_true

theorem PvsNP.Units.tf_fun_erase_true :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.erase true) :=
  PvsNP.Units.tf_fun_erase_true.erase_polyTime
