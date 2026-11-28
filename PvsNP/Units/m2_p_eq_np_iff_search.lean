import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_search
import PvsNP.Units.m2_np_verifier_normal
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_p_subset_np

/-- P = NP exactly when every polynomial-time verifier has a polynomial-time
certificate finder: left to right is the settled unit `m2_p_eq_np_search`;
right to left takes a normal verifier (one refusing over-long certificates)
and its finder, so `x ↦ V (x, F x)` decides the language in polynomial time,
giving NP ⊆ P alongside P ⊆ NP. -/
theorem PvsNP.Units.m2_p_eq_np_iff_search :
    PvsNP.P = PvsNP.NP ↔ ∀ (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
  PvsNP.PolyTimeVerifier L V p →
    ∃ F : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F ∧
      ∀ x ∈ L, (F x).length ≤ p.eval x.length ∧ V (x, F x) = true := by
  constructor
  · exact PvsNP.Units.m2_p_eq_np_search
  · intro H
    apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
    intro L hL
    obtain ⟨V, p, hV, hnorm⟩ := PvsNP.Units.m2_np_verifier_normal L hL
    obtain ⟨F, hF, hFx⟩ := H L V p hV
    have hrev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => x.reverse.reverse) :=
      PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.m2_reverse_polytime
        PvsNP.Units.m2_reverse_polytime
    have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun x : List Bool => (x.reverse.reverse, F x)) :=
      PvsNP.Units.m2_pair_build_polytime _ _ hrev hF
    have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (V ∘ fun x : List Bool => (x.reverse.reverse, F x)) :=
      PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpair hV.1
    have hfun : (fun x : List Bool => V (x, F x)) =
        V ∘ fun x : List Bool => (x.reverse.reverse, F x) := by
      funext x
      simp only [Function.comp_apply, List.reverse_reverse]
    show PvsNP.PolyTimeDecidable L
    refine ⟨fun x => V (x, F x), ?_, ?_⟩
    · rwa [hfun]
    · intro x
      constructor
      · intro hx
        exact (hFx x hx).2
      · intro hx
        exact (hV.2 x).2 ⟨F x, hnorm x (F x) hx, hx⟩
