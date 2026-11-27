import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_ite_polytime

/-- Two polynomial-time functions can be combined by cases on a language in P (TM2). -/
theorem PvsNP.Units.m2_polytime_case_on_p :
    ∀ (E : Language Bool) (a b : List Bool → List Bool), E ∈ PvsNP.P →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString a →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString b →
          ∃ g : List Bool → List Bool,
            PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g ∧
            ∀ x : List Bool, (x ∈ E → g x = a x) ∧ (x ∉ E → g x = b x) := by
  rintro E a b ⟨e, he, hdec⟩ ha hb
  refine ⟨fun x => if e x = true then a x else b x,
    PvsNP.Units.m2_ite_polytime e a b he ha hb, fun x => ⟨fun hx => ?_, fun hnx => ?_⟩⟩
  · simp [(hdec x).mp hx]
  · have hne : e x ≠ true := fun h => hnx ((hdec x).mpr h)
    simp [hne]
