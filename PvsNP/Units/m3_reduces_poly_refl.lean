import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_to_flat

set_option autoImplicit false

theorem PvsNP.Units.m3_reduces_poly_refl :
    ∀ Q : List Bool → Prop, CookLevin.reducesPoly Q Q := by
  intro Q
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime _⟩
  obtain ⟨t, M, ht, hM, h1, hc⟩ :=
    PvsNP.Units.m1_st_to_flat id (PvsNP.Units.m1_tm2_to_st PvsNP.encodeString PvsNP.encodeString id hid)
  exact ⟨id, t, M, ht, hM, h1, hc, fun _ => Iff.rfl⟩
