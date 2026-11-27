import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

theorem PvsNP.Units.m2_tm_count_false_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.count false) true) := by
  exact m2_transducer_polytime Unit
    (fun _ b => ((), if b then none else some true))
    (fun _ => none) (fun _ x => List.replicate (x.count false) true)
    (by intro q; rfl)
    (by intro q b x; cases b <;> simp [List.count_cons, List.replicate_succ]) ()
