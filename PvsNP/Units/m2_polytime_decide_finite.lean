import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_p_finite

set_option autoImplicit false

/-- Membership in a fixed finite set of strings is a polynomial-time test: the
settled unit `m2_p_finite` gives a polynomial-time decider `f` for the set,
and that decider is exactly `fun x => decide (x ∈ S)` (funext, cases on
`f x`). -/
theorem PvsNP.Units.m2_polytime_decide_finite :
    ∀ S : Finset (List Bool),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => decide (x ∈ S)) := by
  intro S
  have hdec : ∃ f : List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f ∧
        ∀ x : List Bool, x ∈ S ↔ f x = true :=
    PvsNP.Units.m2_p_finite S
  obtain ⟨f, hf, hiff⟩ := hdec
  have hfeq : f = fun x : List Bool => decide (x ∈ S) := by
    funext x
    show f x = decide (x ∈ S)
    cases hfx : f x with
    | true =>
      have hx : x ∈ S := (hiff x).mpr hfx
      simp [hfx, hx]
    | false =>
      have hx : x ∉ S := by
        intro h
        have h1 := (hiff x).mp h
        rw [hfx] at h1
        exact Bool.noConfusion h1
      simp [hfx, hx]
  rw [← hfeq]
  exact hf
