import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_projection

set_option autoImplicit false

namespace PvsNP.Units.m2_np_iff_p_projection

theorem main (L : Language Bool) :
    L ∈ PvsNP.NP ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.P ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E := by
  constructor
  · rintro ⟨V, p, ⟨M⟩, hspec⟩
    let E : Language Bool := {x : List Bool | x ∈ ({[true]} : Finset (List Bool))}
    have hE : E ∈ PvsNP.P := PvsNP.Units.m2_p_finite {[true]}
    let g : List Bool × List Bool → List Bool := fun q => [V q]
    have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g :=
      ⟨⟨M.toTM2ComputableAux, M.time, fun a => by
        have henc : PvsNP.encodeAnswer (V a) = PvsNP.encodeString [V a] := rfl
        show Turing.TM2OutputsInTime M.toTM2ComputableAux.tm
            (List.map M.toTM2ComputableAux.inputAlphabet.invFun (PvsNP.encodePair a))
            (Option.some (List.map M.toTM2ComputableAux.outputAlphabet.invFun
              (PvsNP.encodeString [V a])))
            (M.time.eval (PvsNP.encodePair a).length)
        rw [← henc]
        exact M.outputsFun a⟩⟩
    refine ⟨E, g, p, hE, hg, fun x => ?_⟩
    rw [hspec x]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    show V (x, c) = true ↔ [V (x, c)] ∈ ({[true]} : Finset (List Bool))
    simp
  · rintro ⟨E, g, p, hE, hg, hspec⟩
    have hENP : E ∈ PvsNP.NP := PvsNP.Units.m2_p_subset_np hE
    have hProj := PvsNP.Units.m2_np_projection E g p hENP hg
    have heq : ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) = L := by
      ext x
      exact (hspec x).symm
    rwa [heq] at hProj

end PvsNP.Units.m2_np_iff_p_projection

/-- NP is exactly the bounded existential projections of P (TM2). -/
theorem PvsNP.Units.m2_np_iff_p_projection :
    ∀ L : Language Bool, L ∈ PvsNP.NP ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.P ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E :=
  PvsNP.Units.m2_np_iff_p_projection.main
