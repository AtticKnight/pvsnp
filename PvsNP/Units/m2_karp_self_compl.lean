import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_np_down_closed

set_option autoImplicit false

/-- A language Karp-reduces to its complement iff its complement reduces to it (`m2_karp_compl_iff`
with `compl_compl`), and if it is also in NP then `m2_np_down_closed` puts its complement in NP,
hence the language in `NP ∩ coNP`. -/
theorem PvsNP.Units.m2_karp_self_compl :
    ∀ L : Language Bool, (PvsNP.KarpReducible L Lᶜ ↔ PvsNP.KarpReducible Lᶜ L) ∧
      (PvsNP.KarpReducible L Lᶜ → L ∈ PvsNP.NP → L ∈ PvsNP.NP ∩ PvsNP.coNP) := by
  intro L
  have hiff : PvsNP.KarpReducible L Lᶜ ↔ PvsNP.KarpReducible Lᶜ L := by
    have h := PvsNP.Units.m2_karp_compl_iff L Lᶜ
    rw [compl_compl] at h
    exact h
  exact ⟨hiff, fun hred hnp => ⟨hnp, PvsNP.Units.m2_np_down_closed Lᶜ L (hiff.1 hred) hnp⟩⟩
