import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed

namespace PvsNP.Units.m2_fixed_quotient_p_np

theorem cpt_appR (w : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ w) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const w)

theorem cpt_appL (w : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => w ++ x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const w)
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id

theorem karpR (w : List Bool) (L : Language Bool) :
    PvsNP.KarpReducible ({x : List Bool | x ++ w ∈ L} : Language Bool) L :=
  ⟨fun x => x ++ w, cpt_appR w, fun _ => Iff.rfl⟩

theorem karpL (w : List Bool) (L : Language Bool) :
    PvsNP.KarpReducible ({x : List Bool | w ++ x ∈ L} : Language Bool) L :=
  ⟨fun x => w ++ x, cpt_appL w, fun _ => Iff.rfl⟩

end PvsNP.Units.m2_fixed_quotient_p_np

theorem PvsNP.Units.m2_fixed_quotient_p_np :
∀ (w : List Bool) (L : Language Bool),
  (L ∈ PvsNP.P → ({x : List Bool | x ++ w ∈ L} : Language Bool) ∈ PvsNP.P ∧
      ({x : List Bool | w ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
    (L ∈ PvsNP.NP → ({x : List Bool | x ++ w ∈ L} : Language Bool) ∈ PvsNP.NP ∧
      ({x : List Bool | w ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) := by
  intro w L
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · exact PvsNP.Units.m2_p_down_closed _ _ (PvsNP.Units.m2_fixed_quotient_p_np.karpR w L) h
  · exact PvsNP.Units.m2_p_down_closed _ _ (PvsNP.Units.m2_fixed_quotient_p_np.karpL w L) h
  · exact PvsNP.Units.m2_np_down_closed _ _ (PvsNP.Units.m2_fixed_quotient_p_np.karpR w L) h
  · exact PvsNP.Units.m2_np_down_closed _ _ (PvsNP.Units.m2_fixed_quotient_p_np.karpL w L) h
