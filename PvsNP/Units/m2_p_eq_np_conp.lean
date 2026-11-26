import Mathlib
import PvsNP.Defs
import CookLevin

/-!
# P = NP implies NP = coNP

The proof goes through the closure of `P` under complement, which costs nothing at the
machine level: a polynomial-time decider for `L` is already a polynomial-time decider for
`Lᶜ` once its output symbols are read through Boolean negation. The machine, its time
bound and its input alphabet are untouched; only the output alphabet equivalence is
post-composed with negation, and the output list is then literally the same list.
-/

namespace PvsNP.Units.m2_p_eq_np_conp

/-- Boolean negation as an equivalence of `Bool` with itself. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := (!·)
  invFun := (!·)
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b

/-- A polynomial-time decider can have its answer flipped for free: keep the same machine,
the same time bound and the same input alphabet, and only reinterpret its output symbols
through Boolean negation. The output list is then literally unchanged. -/
theorem polyTimeComputable_not {f : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x => !f x) := by
  obtain ⟨c⟩ := hf
  have hfun : ∀ a, Turing.TM2OutputsInTime c.tm
      (List.map c.inputAlphabet.invFun (PvsNP.encodeString a))
      (some (List.map (c.outputAlphabet.trans boolNotEquiv).invFun
        (PvsNP.encodeAnswer (!f a)))) (c.time.eval (PvsNP.encodeString a).length) := by
    intro a
    have h := c.outputsFun a
    have heq : List.map (c.outputAlphabet.trans boolNotEquiv).invFun
          (PvsNP.encodeAnswer (!f a))
        = List.map c.outputAlphabet.invFun (PvsNP.encodeAnswer (f a)) := by
      show [(c.outputAlphabet.trans boolNotEquiv).invFun (!f a)]
        = [c.outputAlphabet.invFun (f a)]
      congr 1
      show c.outputAlphabet.invFun (!(!f a)) = c.outputAlphabet.invFun (f a)
      rw [Bool.not_not]
    rw [heq]
    exact h
  exact ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet.trans boolNotEquiv
    time := c.time
    outputsFun := hfun }⟩

/-- `P` is closed under complement: flip the decider's answer. -/
theorem p_compl {L : Language Bool} (hL : L ∈ PvsNP.P) : Lᶜ ∈ PvsNP.P := by
  have hL' : PvsNP.PolyTimeDecidable L := hL
  obtain ⟨f, hf, hdec⟩ := hL'
  refine ⟨fun x => !f x, polyTimeComputable_not hf, fun x => ?_⟩
  simp only [Set.mem_compl_iff]
  show x ∉ L ↔ !f x = true
  cases hfx : f x with
  | true =>
    constructor
    · intro hx
      exact absurd ((hdec x).mpr hfx) hx
    · intro hx
      exact absurd hx (by simp)
  | false =>
    constructor
    · intro _
      rfl
    · intro _ hxL
      exact absurd ((hdec x).mp hxL) (by simp [hfx])

end PvsNP.Units.m2_p_eq_np_conp

/-- If the campaign's `P` equals its `NP`, then its `NP` equals its `coNP`: membership in
`NP` is membership in `P`, and membership in `coNP` is membership in `NP` of the complement,
so both directions are the closure of `P` under complement. -/
theorem PvsNP.Units.m2_p_eq_np_conp :
    PvsNP.P = PvsNP.NP → PvsNP.NP = PvsNP.coNP := by
  intro h
  ext L
  constructor
  · intro hL
    have hLP : L ∈ PvsNP.P := by rw [h]; exact hL
    have hLcP : Lᶜ ∈ PvsNP.P := PvsNP.Units.m2_p_eq_np_conp.p_compl hLP
    have hLcNP : Lᶜ ∈ PvsNP.NP := by rw [← h]; exact hLcP
    show Lᶜ ∈ PvsNP.NP
    exact hLcNP
  · intro hL
    have hLcNP : Lᶜ ∈ PvsNP.NP := hL
    have hLcP : Lᶜ ∈ PvsNP.P := by rw [h]; exact hLcNP
    have hLP : L ∈ PvsNP.P := by
      have hcc := PvsNP.Units.m2_p_eq_np_conp.p_compl (L := Lᶜ) hLcP
      simpa using hcc
    rw [← h]
    exact hLP
