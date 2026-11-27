import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

/-
Proof plan: class-level, no machine is built. The bridges translate the
campaign's verifier-based classes (`PvsNP.Defs`) to the library's
(`fr_ladner`, already built); the library lemma `L017` (NP downward
closed under Karp reductions) and the complement reduction do the work.
The complement reduction uses a direct `exact not_congr`, since
`x ∈ Lᶜ` is definitionally `¬ (x ∈ L)`.
-/

namespace PvsNP.Units.m2_npc_reduces_characterizes

theorem karp_iff (L₁ L₂ : Language Bool) :
    PvsNP.KarpReducible L₁ L₂ ↔
      PvsNP.Units.fr_ladner.PEqualNP.Library.PolyTimeReducible L₁ L₂ := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, h⟩

theorem NP_iff (L : Language Bool) :
    L ∈ PvsNP.NP ↔ L ∈ PvsNP.Units.fr_ladner.PEqualNP.Library.NP := by
  constructor
  · rintro ⟨V, p, hV, hL⟩
    exact ⟨{xw | V xw = true}, p, ⟨V, fun _ => Iff.rfl, hV⟩, hL⟩
  · rintro ⟨R, p, ⟨f, hf, hc⟩, hL⟩
    refine ⟨f, p, hc, fun x => (hL x).trans ?_⟩
    exact exists_congr fun w => and_congr_right fun _ => hf (x, w)

/-- The complement of a Karp reduction is a Karp reduction (same machine). -/
theorem compl_reducible {L₁ L₂ : Language Bool}
    (h : PvsNP.KarpReducible L₁ L₂) :
    PvsNP.KarpReducible L₁ᶜ L₂ᶜ := by
  obtain ⟨f, hf, hiff⟩ := h
  refine ⟨f, hf, fun x => ?_⟩
  exact not_congr (hiff x)

/-- NP is downward closed under Karp reductions, on the campaign's classes. -/
theorem np_down_closed {L₁ L₂ : Language Bool}
    (h : PvsNP.KarpReducible L₁ L₂) (h₂ : L₂ ∈ PvsNP.NP) : L₁ ∈ PvsNP.NP :=
  (NP_iff L₁).2 (PvsNP.Units.fr_ladner.PEqualNP.Library.L017 L₁ L₂
    ((karp_iff L₁ L₂).1 h) ((NP_iff L₂).1 h₂))

end PvsNP.Units.m2_npc_reduces_characterizes

/-- For an NP-complete L₀, NP is what reduces to L₀ and coNP what reduces to its complement (TM2). -/
theorem PvsNP.Units.m2_npc_reduces_characterizes :
    ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ∀ L : Language Bool,
      (L ∈ PvsNP.NP ↔ PvsNP.KarpReducible L L₀) ∧
        (L ∈ PvsNP.coNP ↔ PvsNP.KarpReducible L L₀ᶜ) := by
  intro L₀ hc L
  obtain ⟨hL₀, hhard⟩ := hc
  constructor
  · constructor
    · intro hL
      exact hhard L hL
    · intro hred
      exact PvsNP.Units.m2_npc_reduces_characterizes.np_down_closed hred hL₀
  · constructor
    · intro hco
      have hLc : Lᶜ ∈ PvsNP.NP := hco
      have hred : PvsNP.KarpReducible Lᶜ L₀ := hhard Lᶜ hLc
      have h := PvsNP.Units.m2_npc_reduces_characterizes.compl_reducible hred
      rwa [compl_compl] at h
    · intro hred
      have h := PvsNP.Units.m2_npc_reduces_characterizes.compl_reducible hred
      rw [compl_compl] at h
      have hLc : Lᶜ ∈ PvsNP.NP :=
        PvsNP.Units.m2_npc_reduces_characterizes.np_down_closed h hL₀
      exact hLc
