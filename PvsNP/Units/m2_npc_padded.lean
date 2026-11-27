import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_honest_image

set_option autoImplicit false

namespace PvsNP.Units.m2_npc_padded

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def padSq (x : List Bool) : List Bool :=
  x ++ false :: List.replicate (x.length ^ 2) true

theorem cpt_padSq :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString padSq := by
  have h1 := L055 (Polynomial.X ^ 2 : Polynomial ℕ)
  have hsq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true) := by
    have heq : (fun x : List Bool =>
        List.replicate ((Polynomial.X ^ 2 : Polynomial ℕ).eval x.length) true) =
        (fun x : List Bool => List.replicate (x.length ^ 2) true) := by
      funext x
      simp
    rw [heq] at h1
    exact h1
  have h2 := cpt_app2 cpt_id (cpt_app2 (cpt_const [false]) hsq)
  have heq : (fun x : List Bool => x ++ ([false] ++ List.replicate (x.length ^ 2) true)) = padSq := by
    funext x
    rfl
  rw [heq] at h2
  exact h2

theorem padSq_honest (x : List Bool) : x.length ≤ (padSq x).length := by
  simp only [padSq, List.length_append, List.length_cons, List.length_replicate]
  omega

theorem padSq_inj {x y : List Bool} (h : padSq x = padSq y) : x = y := by
  have hlen : x.length + (x.length ^ 2 + 1) = y.length + (y.length ^ 2 + 1) := by
    have := congrArg List.length h
    simpa only [padSq, List.length_append, List.length_cons, List.length_replicate] using this
  have hxlen : x.length = y.length := by
    rcases lt_trichotomy x.length y.length with hlt | heq | hgt
    · have : x.length ^ 2 ≤ y.length ^ 2 := Nat.pow_le_pow_left hlt.le 2
      omega
    · exact heq
    · have : y.length ^ 2 ≤ x.length ^ 2 := Nat.pow_le_pow_left hgt.le 2
      omega
  have ht := congrArg (List.take x.length) h
  simp only [padSq] at ht
  rw [List.take_left, hxlen, List.take_left] at ht
  exact ht

theorem npc_padded_main (L : Language Bool) (hL : PvsNP.NPComplete L) :
    PvsNP.NPComplete
      ({y : List Bool | ∃ x ∈ L, y = x ++ false :: List.replicate (x.length ^ 2) true} :
        Language Bool) := by
  refine ⟨?_, ?_⟩
  · have himg := PvsNP.Units.m2_np_honest_image padSq L cpt_padSq padSq_honest hL.1
    have heq : ({y : List Bool | ∃ x ∈ L, padSq x = y} : Language Bool) =
        ({y : List Bool | ∃ x ∈ L, y = x ++ false :: List.replicate (x.length ^ 2) true} :
          Language Bool) := by
      ext y
      constructor <;> rintro ⟨x, hx, h⟩ <;> exact ⟨x, hx, h.symm⟩
    rw [← heq]
    exact himg
  · intro L' hL'
    obtain ⟨g, hg, hred⟩ := hL.2 L' hL'
    refine ⟨fun z => padSq (g z), cpt_comp hg cpt_padSq, fun z => ?_⟩
    rw [hred z]
    constructor
    · intro hgz
      exact ⟨g z, hgz, rfl⟩
    · rintro ⟨x, hx, hfx⟩
      have heq : g z = x := padSq_inj hfx
      rw [heq]
      exact hx

end PvsNP.Units.m2_npc_padded

theorem PvsNP.Units.m2_npc_padded :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPComplete ({y : List Bool | ∃ x ∈ L, y = x ++ false :: List.replicate (x.length ^ 2) true} : Language Bool) :=
  PvsNP.Units.m2_npc_padded.npc_padded_main
