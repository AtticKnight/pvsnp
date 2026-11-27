import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_conp_down_closed

namespace PvsNP.Units.m2_nexp_hard_outside_np_conp

theorem dlang_in_nexp :
    ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true :=
  ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.RD, 2,
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_RD, fun _ => Iff.rfl⟩

theorem dlang_not_np :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang ∉ PvsNP.NP := by
  intro h
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang_not_NP
    ((PvsNP.Units.fr_ladner.NP_iff _).1 h)

theorem np_sub_nexp (A : Language Bool) (hA : A ∈ PvsNP.NP) :
    ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ A ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true := by
  obtain ⟨R, k, ⟨V, hf, hV⟩, hmem⟩ :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.L048 ((PvsNP.Units.fr_ladner.NP_iff A).1 hA)
  exact ⟨V, k, hV, fun x =>
    (hmem x).trans (exists_congr fun w => and_congr_right fun _ => hf (x, w))⟩

theorem main (L : Language Bool)
    (hhard : ∀ L' : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L' ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
        PvsNP.KarpReducible L' L) :
    L ∉ PvsNP.NP ∧ L ∉ PvsNP.coNP := by
  let L₀ := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang
  refine ⟨?_, ?_⟩
  · intro hLnp
    exact dlang_not_np (PvsNP.Units.m2_np_down_closed L₀ L (hhard L₀ dlang_in_nexp) hLnp)
  · intro hLconp
    have hL₀_conp : L₀ ∈ PvsNP.coNP :=
      PvsNP.Units.m2_conp_down_closed L₀ L (hhard L₀ dlang_in_nexp) hLconp
    have hL₀c_np : L₀ᶜ ∈ PvsNP.NP := hL₀_conp
    have hL₀c_nexp := np_sub_nexp (L₀ᶜ) hL₀c_np
    have hL₀c_conp : L₀ᶜ ∈ PvsNP.coNP :=
      PvsNP.Units.m2_conp_down_closed (L₀ᶜ) L (hhard (L₀ᶜ) hL₀c_nexp) hLconp
    have hL₀cc_np : L₀ᶜᶜ ∈ PvsNP.NP := hL₀c_conp
    rw [compl_compl] at hL₀cc_np
    exact dlang_not_np hL₀cc_np

end PvsNP.Units.m2_nexp_hard_outside_np_conp

theorem PvsNP.Units.m2_nexp_hard_outside_np_conp :
    ∀ L : Language Bool, (∀ L' : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L' ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
        PvsNP.KarpReducible L' L) → L ∉ PvsNP.NP ∧ L ∉ PvsNP.coNP :=
  PvsNP.Units.m2_nexp_hard_outside_np_conp.main
