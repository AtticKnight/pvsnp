import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

theorem PvsNP.Units.tf_fun_scan :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.scanl (fun a b => a && b) true x) := by
  exact PvsNP.Units.m2_transducer_polytime Bool
    (fun q b => (q && b, some q)) (fun q => some q)
    (fun q x => List.scanl (fun a b => a && b) q x)
    (fun _ => rfl) (fun q b xs => by simp [List.scanl_cons]) true
