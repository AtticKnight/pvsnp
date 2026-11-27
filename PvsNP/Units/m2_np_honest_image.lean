import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.m2_np_honest_image

open PvsNP.Units.m2_np_down_closed.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

lemma honest_image_np
    (f : List Bool → List Bool) (L : Language Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hhonest : ∀ x : List Bool, x.length ≤ (f x).length)
    (hL : L ∈ PvsNP.NP) :
    ({y : List Bool | ∃ x ∈ L, f x = y} : Language Bool) ∈ PvsNP.NP := by
  obtain ⟨R, p, ⟨V, hVR, hV⟩, hbound, hmem⟩ :=
    PvsNP.Units.m2_np_down_closed.PEqualNP.Library.L045 L
      ((PvsNP.Units.m2_np_down_closed.NP_iff L).1 hL)
  let A : List (Bool ⊕ Bool) → Bool :=
    fun l => decide ((nfDec l).1 = f (unpairB (nfDec l).2).1)
  let B : List (Bool ⊕ Bool) → Bool :=
    fun l => V (unpairB (nfDec l).2)
  have hf_unpair1 :
      PvsNP.Units.m2_np_down_closed.PEqualNP.Library.ComputableInPolyTime
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun s : List Bool => f (unpairB s).1) :=
    cpt_comp cpt_unpairB1 hf
  have hA :
      PvsNP.Units.m2_np_down_closed.PEqualNP.Library.ComputableInPolyTime
        (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool A :=
    cpt_comp (cpt_comp nfDec_polyTime (cpt_second hf_unpair1)) PvsNP.Units.m2_eq_polytime
  have hB :
      PvsNP.Units.m2_np_down_closed.PEqualNP.Library.ComputableInPolyTime
        (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool B :=
    cpt_comp (cpt_comp (cpt_comp nfDec_polyTime cpt_snd) cpt_unpairB) hV
  have hW : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun q : List Bool × List Bool =>
        B (PvsNP.Units.m2_np_down_closed.PEqualNP.Library.encodePair q) &&
          A (PvsNP.Units.m2_np_down_closed.PEqualNP.Library.encodePair q)) :=
    nf_restrict (nf_and hA hB)
  refine ⟨fun q =>
      B (PvsNP.Units.m2_np_down_closed.PEqualNP.Library.encodePair q) &&
        A (PvsNP.Units.m2_np_down_closed.PEqualNP.Library.encodePair q),
    Polynomial.C 2 * Polynomial.X + p + 1, hW, fun y => ?_⟩
  constructor
  · rintro ⟨x, hxL, rfl⟩
    obtain ⟨w, hwR⟩ := (hmem x).1 hxL
    refine ⟨pairB x w, ?_, ?_⟩
    · have hlen := hbound x w hwR
      have hpx := eval_mono p (hhonest x)
      have hxh := hhonest x
      rw [pairB_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      omega
    · simp only [B, A, nfDec_encodePair, unpairB_pairB, (hVR (x, w)).1 hwR,
        decide_true, Bool.and_self]
  · rintro ⟨z, -, hWz⟩
    simp only [B, A, nfDec_encodePair, Bool.and_eq_true, decide_eq_true_eq] at hWz
    obtain ⟨hVz, hfy⟩ := hWz
    refine ⟨(unpairB z).1, (hmem (unpairB z).1).2 ⟨(unpairB z).2, ?_⟩, hfy.symm⟩
    exact (hVR ((unpairB z).1, (unpairB z).2)).2 (by simpa using hVz)

end PvsNP.Units.m2_np_honest_image

theorem PvsNP.Units.m2_np_honest_image :
    ∀ (f : List Bool → List Bool) (L : Language Bool),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
      (∀ x : List Bool, x.length ≤ (f x).length) → L ∈ PvsNP.NP →
        ({y : List Bool | ∃ x ∈ L, f x = y} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_honest_image.honest_image_np
