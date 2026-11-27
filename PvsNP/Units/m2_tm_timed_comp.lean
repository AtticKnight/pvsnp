import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

theorem PvsNP.Units.m2_tm_timed_comp :
    ∀ (f g : List Bool → List Bool) (t₁ t₂ len : ℕ → ℕ), Monotone t₂ →
      (∀ x : List Bool, (f x).length ≤ len x.length) →
        (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString f, ∀ n : ℕ, M.time n ≤ t₁ n) →
          (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString g, ∀ n : ℕ, M.time n ≤ t₂ n) →
            ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => g (f x)),
              ∀ n : ℕ, M.time n ≤ t₁ n + 2 * len n + 2 + t₂ (len n) := by
  intro f g t₁ t₂ len hmono hlen h1 h2
  obtain ⟨M, hM⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.comp_time
    PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString f g t₁ t₂ len h1 h2 hmono hlen
  refine ⟨M, fun n => ?_⟩
  have hn := hM n
  omega
