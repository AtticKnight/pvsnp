import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_eq_np_search
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_eq_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- A witness for image membership is a bounded preimage. Search in the image gives a right inverse there. -/
theorem PvsNP.Units.m2_p_eq_np_inverts_honest :
    PvsNP.P = PvsNP.NP → ∀ (f : List Bool → List Bool) (q : Polynomial ℕ),
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
    (∀ x : List Bool, x.length ≤ q.eval (f x).length) →
      ∃ g : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g ∧
        ∀ x : List Bool, f (g (f x)) = f x := by
  intro hPNP f q hf hbound
  let V : List Bool × List Bool → Bool := fun p => decide (p.1 = f p.2)
  have hs : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2) := cpt_snd
  have hh : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) := cpt_fst
  have hv : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V :=
    PvsNP.Units.m2_pair_build_polytime.cpt_comp
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ hh (PvsNP.Units.m2_pair_build_polytime.cpt_comp hs hf))
      PvsNP.Units.m2_eq_polytime
  have verify : PvsNP.PolyTimeVerifier (Set.range f) V q := by
    refine ⟨hv, fun y => ?_⟩
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hbound x, by simp [V]⟩
    · rintro ⟨x, _, hx⟩
      exact ⟨x, ((decide_eq_true_eq.mp hx) : y = f x).symm⟩
  obtain ⟨g, hg, recover⟩ := PvsNP.Units.m2_p_eq_np_search hPNP (Set.range f) V q verify
  refine ⟨g, hg, fun x => ?_⟩
  have good := (recover (f x) ⟨x, rfl⟩).2
  exact ((decide_eq_true_eq.mp good) : f x = f (g (f x))).symm
