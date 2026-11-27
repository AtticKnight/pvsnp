import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_verifier_normal
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.fr_ladner

/-
Every NP language has a verifier whose certificates have one exact length: pad.
Start from a verifier (V, p) that accepts nothing past its bound (the settled unit
`m2_np_verifier_normal`). Take q = p + 1 and read a certificate w' as
w ++ false :: 1^(p(|x|) - |w|): the new verifier strips the padding — reverse,
drop the leading trues and the false before them (`dropN` from the settled unit
`fr_ladner`), reverse — and runs V. A padded certificate has length exactly
p(|x|) + 1 = q(|x|); conversely every exact-length certificate the new verifier
accepts unpads to a certificate V accepts within its bound.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_np_exact_certificates

open Turing

/-- Strip the padding `false :: 1^n` from the end of a padded certificate. -/
def unpad (w' : List Bool) : List Bool :=
  (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN w'.reverse).reverse

theorem unpad_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString unpad := by
  have hrev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      List.reverse := PvsNP.Units.m2_reverse_polytime
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString List.reverse
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN hrev hdrop
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN ∘ List.reverse)
    List.reverse h1 hrev
  exact h2

/-- Applying `unpad` to the second component of a pair is polynomial-time. -/
theorem pair_unpad_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, unpad p.2)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_second unpad_polyTime

/-- The padded verifier is polynomial-time: it is V after the pair-map. -/
theorem verifier_polyTime (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun pw : List Bool × List Bool => V (pw.1, unpad pw.2)) := by
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeAnswer (fun p : List Bool × List Bool => (p.1, unpad p.2)) V
    pair_unpad_polyTime hV
  exact hcomp

/-- `dropN` drops a run of `n` trues and the false after them. -/
theorem dropN_replicate (n : ℕ) (r : List Bool) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
        (List.replicate n true ++ false :: r) = r :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un n r

/-- Unpadding a padded certificate recovers it. -/
theorem unpad_pad (w₀ : List Bool) (n : ℕ) :
    unpad (w₀ ++ false :: List.replicate n true) = w₀ := by
  have hrev : (w₀ ++ false :: List.replicate n true).reverse =
      List.replicate n true ++ false :: w₀.reverse := by
    simp [List.reverse_append]
  simp only [unpad, hrev, dropN_replicate, List.reverse_reverse]

end PvsNP.Units.m2_np_exact_certificates

/-- Every NP language has a verifier whose certificates have one exact length. -/
theorem PvsNP.Units.m2_np_exact_certificates :
    ∀ L ∈ PvsNP.NP, ∃ (V : List Bool × List Bool → Bool) (q : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length = q.eval x.length ∧
          V (x, w) = true := by
  intro L hL
  obtain ⟨V, p, hVer, hnorm⟩ := PvsNP.Units.m2_np_verifier_normal L hL
  obtain ⟨hVpoly, hVcorr⟩ := hVer
  refine ⟨fun pw : List Bool × List Bool => V (pw.1,
    PvsNP.Units.m2_np_exact_certificates.unpad pw.2), p + 1,
    PvsNP.Units.m2_np_exact_certificates.verifier_polyTime V hVpoly, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨w₀, hw₀le, hw₀V⟩ := (hVcorr x).mp hx
    refine ⟨w₀ ++ false :: List.replicate (p.eval x.length - w₀.length) true, ?_, ?_⟩
    · have hq : (p + 1).eval x.length = p.eval x.length + 1 := by simp
      rw [hq]
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_nil]
      omega
    · show V (x, PvsNP.Units.m2_np_exact_certificates.unpad
          (w₀ ++ false :: List.replicate (p.eval x.length - w₀.length) true)) = true
      rw [PvsNP.Units.m2_np_exact_certificates.unpad_pad]
      exact hw₀V
  · intro h
    obtain ⟨w, _, hwV⟩ := h
    have hle := hnorm x (PvsNP.Units.m2_np_exact_certificates.unpad w) hwV
    exact (hVcorr x).mpr ⟨PvsNP.Units.m2_np_exact_certificates.unpad w, hle, hwV⟩
