import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_np_projection

import PvsNP.Units.m2_p_finite

import PvsNP.Units.m2_p_subset_np

import PvsNP.Units.m2_conp_forall_projection

set_option autoImplicit false

/-- NP equals coNP exactly when NP is closed under bounded universal projection:
forward by the settled closure of coNP under the same projection, backward by
verifying the complement with the verifier's answer as a one-bit output. -/
theorem PvsNP.Units.m2_np_eq_conp_iff_forall_projection :
    PvsNP.NP = PvsNP.coNP ↔ ∀ (E : Language Bool)
      (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.NP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} :
          Language Bool) ∈ PvsNP.NP := by
  constructor
  · intro h E g p hE hg
    have hE' : E ∈ PvsNP.coNP := by rwa [← h]
    have hS := PvsNP.Units.m2_conp_forall_projection E g p hE' hg
    rwa [← h] at hS
  · intro H
    have hsub : PvsNP.coNP ⊆ PvsNP.NP := by
      intro L hL
      have hLc : Lᶜ ∈ PvsNP.NP := hL
      obtain ⟨V, p, hV⟩ := hLc
      have hE : ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} : Language Bool)
          ∈ PvsNP.NP :=
        PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_finite {[false]})
      have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
          (fun q => [V q]) := by
        obtain ⟨h⟩ := hV.1
        exact ⟨⟨h.toTM2ComputableAux, h.time, fun a => h.outputsFun a⟩⟩
      have hmain := H _ _ p hE hg
      have hset : ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length →
          (fun q => [V q]) (x, c) ∈
            ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} : Language Bool)} :
          Language Bool) = L := by
        ext x
        constructor
        · intro hx
          by_contra hxL
          have hxLc : x ∈ Lᶜ := hxL
          obtain ⟨w, hwlen, hwV⟩ := (hV.2 x).1 hxLc
          have h := hx w hwlen
          have h2 : V (x, w) = false := by simpa using h
          rw [hwV] at h2
          cases h2
        · intro hxL c hc
          have hfalse : V (x, c) = false := by
            by_contra hne
            have htrue : V (x, c) = true := by
              cases hVc : V (x, c) with
              | false => exact absurd hVc hne
              | true => rfl
            have hxLc : x ∈ Lᶜ := (hV.2 x).2 ⟨c, hc, htrue⟩
            exact hxLc hxL
          simp [hfalse]
      exact (congrArg (fun S : Language Bool => S ∈ PvsNP.NP) hset).mp hmain
    apply Set.Subset.antisymm _ hsub
    intro L hL
    have h1 : Lᶜ ∈ PvsNP.coNP := by
      show (Lᶜ)ᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    exact hsub h1
