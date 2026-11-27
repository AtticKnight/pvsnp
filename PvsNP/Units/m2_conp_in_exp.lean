import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_np_in_exp

set_option autoImplicit false

namespace PvsNP.Units.m2_conp_in_exp

/-- Boolean negation as an equivalence of `Bool` with itself. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := (!·)
  invFun := (!·)
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b

/-- Flipping the yes/no answer of a time-bounded multi-stack machine costs zero extra steps:
reinterpret the output alphabet through Boolean negation while keeping the machine and time
function unchanged. -/
def tm2ComputableInTime_not {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => !f x) where
  tm := c.tm
  inputAlphabet := c.inputAlphabet
  outputAlphabet := c.outputAlphabet.trans boolNotEquiv
  time := c.time
  outputsFun a := by
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

end PvsNP.Units.m2_conp_in_exp

/-- Every coNP language is decided in exponential time: its complement is in NP, hence decided
within `2 ^ (n ^ k + k)` steps by `PvsNP.Units.fr_np_in_exp`, and negating the output alphabet
flips the answer bit with the exact same step bound. -/
theorem PvsNP.Units.m2_conp_in_exp :
    ∀ L ∈ PvsNP.coNP, ∃ f : List Bool → Bool, (∀ x, x ∈ L ↔ f x = true) ∧
      ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (k : ℕ),
        ∀ n, h.time n ≤ 2 ^ (n ^ k + k) := by
  intro L hL
  obtain ⟨f, hf, h, k, hk⟩ := PvsNP.Units.fr_np_in_exp Lᶜ hL
  refine ⟨fun x => !f x, fun x => ?_, PvsNP.Units.m2_conp_in_exp.tm2ComputableInTime_not h, k, hk⟩
  show x ∈ L ↔ (!f x) = true
  have hxc : x ∉ L ↔ f x = true := hf x
  cases hfx : f x with
  | true =>
    constructor
    · intro hx
      exact absurd hx (hxc.mpr hfx)
    · intro hfalse
      exact absurd hfalse (by decide)
  | false =>
    constructor
    · intro _
      rfl
    · intro _
      by_contra hnot
      exact absurd (hxc.mp hnot) (by simp [hfx])
