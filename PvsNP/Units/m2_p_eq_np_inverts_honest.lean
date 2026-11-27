import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_search
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

theorem PvsNP.Units.m2_p_eq_np_inverts_honest :
    PvsNP.P = PvsNP.NP → ∀ (f : List Bool → List Bool) (q : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        (∀ x : List Bool, x.length ≤ q.eval (f x).length) →
          ∃ g : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g ∧
            ∀ x : List Bool, f (g (f x)) = f x := by
  intro hPNP f q hf hq
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime _⟩
  have hm := PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x) f hid hf
  have hV := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    _ _ hm PvsNP.Units.m2_eq_polytime
  let V : List Bool × List Bool → Bool := fun p => decide (p.1 = f p.2)
  have hVe : ((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
      (fun p : List Bool × List Bool => ((fun x : List Bool => x) p.1, f p.2))) = V := rfl
  rw [hVe] at hV
  have hver : PvsNP.PolyTimeVerifier {y : List Bool | ∃ x, f x = y} V q := by
    refine ⟨hV, fun y => ?_⟩
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hq x, by simp [V]⟩
    · rintro ⟨w, _, hw⟩
      exact ⟨w, by simpa [V, eq_comm] using hw⟩
  obtain ⟨F, hF, hFs⟩ := PvsNP.Units.m2_p_eq_np_search hPNP _ V q hver
  refine ⟨F, hF, fun x => ?_⟩
  have := (hFs (f x) ⟨x, rfl⟩).2
  simp only [V, decide_eq_true_eq] at this
  exact this.symm
