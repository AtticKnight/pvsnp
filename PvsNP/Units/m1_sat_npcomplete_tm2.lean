import Mathlib
import PvsNP.Defs
import CookLevin

/-- Closing unit: given the three bridges (flat machines to single-tape, vendored NP to
single-tape NP, single-tape to multi-stack polynomial-time computability), carry the vendored
Cook–Levin theorem across to the campaign's own NP-completeness. -/
theorem PvsNP.Units.m1_sat_npcomplete_tm2 :
    (∀ (f : List Bool → List Bool) (t : ℕ → ℕ) (M : FlatTM), inOPoly t → validFlatTM M →
        M.tapes = 1 → CookLevin.computesInTime M f t →
          PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) →
    (∀ L : Language Bool, CookLevin.inNP (fun x => x ∈ L) ↔ L ∈ PvsNP.SingleTape.NP) →
    (∀ {α β A B : Type} [Finite A] [Finite B] (ea : α → List A) (eb : β → List B) (f : α → β),
        PvsNP.SingleTape.PolyTimeComputable ea eb f ↔ PvsNP.PolyTimeComputable ea eb f) →
    ∀ L : Language Bool, (∀ x, x ∈ L ↔ SATStr x) → PvsNP.NPComplete L := by
  intro hbridge hnp hconv L hL
  -- Membership: `SATStr` is in the vendored `inNP`, hence so is `L` (same members),
  -- hence `L` is in single-tape NP, hence in (multi-stack) NP via the third bridge.
  have hSAT_inNP : CookLevin.inNP (fun x => x ∈ L) := by
    obtain ⟨R, a, k, b, t, M, acc, rej, ht, hM, htape, hmem, hdec⟩ :=
      CookLevin.cook_levin.2
    exact ⟨R, a, k, b, t, M, acc, rej, ht, hM, htape, fun x => (hL x).trans (hmem x), hdec⟩
  have hL_STNP : L ∈ PvsNP.SingleTape.NP := (hnp L).mp hSAT_inNP
  have hL_NP : L ∈ PvsNP.NP := by
    obtain ⟨V, p, hV, hcond⟩ := hL_STNP
    exact ⟨V, p, (hconv PvsNP.encodePair PvsNP.encodeAnswer V).mp hV, hcond⟩
  refine ⟨hL_NP, fun L' hL' => ?_⟩
  -- Hardness: any `L'` in NP is in single-tape NP (third bridge on its verifier),
  -- hence in the vendored `inNP`, hence reduces to `SATStr` by Cook–Levin; the reduction
  -- function is polynomial-time by the first bridge, then by the third.
  obtain ⟨V, p, hV, hcond⟩ := hL'
  have hL'_STNP : L' ∈ PvsNP.SingleTape.NP :=
    ⟨V, p, (hconv PvsNP.encodePair PvsNP.encodeAnswer V).mpr hV, hcond⟩
  have hL'_inNP : CookLevin.inNP (fun x => x ∈ L') := (hnp L').mpr hL'_STNP
  obtain ⟨f, t, M, ht, hM, htape, hcomp, hred⟩ := CookLevin.cook_levin.1 _ hL'_inNP
  refine ⟨f, ?_, fun x => (hred x).trans (hL (f x)).symm⟩
  exact (hconv PvsNP.encodeString PvsNP.encodeString f).mp
    (hbridge f t M ht hM htape hcomp)
