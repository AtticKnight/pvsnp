import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_conp_verifier_iff

open Turing

/-- Bool negation as an equivalence. -/
def negEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := fun b => Bool.not_not b
  right_inv := fun b => Bool.not_not b

/-- Reading a polynomial-time yes/no machine's answer through negation computes the negated
function with the same machine and the same time bound. -/
noncomputable def negPoly {α αΓ : Type} {ea : α → List αΓ} {V : α → Bool}
    (c : TM2ComputableInPolyTime ea Computability.encodeBool V) :
    TM2ComputableInPolyTime ea Computability.encodeBool (fun a => !V a) where
  tm := c.tm
  inputAlphabet := c.inputAlphabet
  outputAlphabet := c.outputAlphabet.trans negEquiv
  time := c.time
  outputsFun a := by
    have h := c.outputsFun a
    have e : (List.map (c.outputAlphabet.trans negEquiv).invFun
        (Computability.encodeBool (!V a))) =
        List.map c.outputAlphabet.invFun (Computability.encodeBool (V a)) := by
      simp [Computability.encodeBool, Equiv.trans, negEquiv]
    rw [e]
    exact h

lemma neg_ptc {α αΓ : Type} {ea : α → List αΓ} {V : α → Bool}
    (h : PvsNP.PolyTimeComputable ea Computability.encodeBool V) :
    PvsNP.PolyTimeComputable ea Computability.encodeBool (fun a => !V a) :=
  let ⟨c⟩ := h; ⟨negPoly c⟩

end PvsNP.Units.m2_conp_verifier_iff

theorem PvsNP.Units.m2_conp_verifier_iff :
    ∀ L : Language Bool, L ∈ PvsNP.coNP ↔
      ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∀ w : List Bool, w.length ≤ p.eval x.length → V (x, w) = true := by
  intro L
  constructor
  · rintro ⟨V, p, hV, hL⟩
    refine ⟨fun q => !V q, p, PvsNP.Units.m2_conp_verifier_iff.neg_ptc hV, fun x => ?_⟩
    have hx := hL x
    constructor
    · intro hxL w hw
      by_contra hne
      have : V (x, w) = true := by simpa using hne
      exact (hx.mpr ⟨w, hw, this⟩) hxL
    · intro hall
      by_contra hxc
      obtain ⟨w, hw, hv⟩ := hx.mp hxc
      have := hall w hw
      simp [hv] at this
  · rintro ⟨V, p, hV, hL⟩
    refine ⟨fun q => !V q, p, PvsNP.Units.m2_conp_verifier_iff.neg_ptc hV, fun x => ?_⟩
    have hx := hL x
    constructor
    · intro hxc
      have hn : ¬ ∀ w : List Bool, w.length ≤ p.eval x.length → V (x, w) = true :=
        fun h => hxc (hx.mpr h)
      push_neg at hn
      obtain ⟨w, hw, hv⟩ := hn
      exact ⟨w, hw, by simpa using hv⟩
    · rintro ⟨w, hw, hv⟩ hxL
      have := hx.mp hxL w hw
      simp [this] at hv
