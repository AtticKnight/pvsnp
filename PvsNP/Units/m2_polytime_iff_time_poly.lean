import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
  lean/PEqualNP/Library/Machines/ComposeTime.lean (comp_time, time_of_polyTime, time_mono).
MODIFIED from that file: the proofs are taken from the settled campaign unit fr_ladner
(github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace holds the upstream port
(upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X there). The closing theorems carry them
over to the campaign's definitions in PvsNP.Defs (`ComputableInTime` spelled out as a Mathlib
`Turing.TM2ComputableInTime` with a step bound; PvsNP.PolyTimeComputable is upstream ComputableInPolyTime);
the converse of time_of_polyTime and the rephrasings are new.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_polytime_iff_time_poly

/-- Upstream `comp_time`: running `f` then `g` costs the two times plus a copy of the middle. -/
theorem comp {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ)
    (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ)
    (h₁ : ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n)
    (h₂ : ∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n)
    (hmono : Monotone t₂) (hlen : ∀ a, (eb (f a)).length ≤ len (ea a).length) :
    ∃ M : Turing.TM2ComputableInTime ea ec (fun a => g (f a)),
      ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := by
  have _hc := Classical.em True
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.comp_time ea eb ec f g t₁ t₂ len h₁ h₂
    hmono hlen

theorem comp' {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ)
    (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ)
    (h₁ : ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n)
    (h₂ : ∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n)
    (hmono : Monotone t₂) (hlen : ∀ a, (eb (f a)).length ≤ len (ea a).length) :
    ∃ M : Turing.TM2ComputableInTime ea ec (fun a => g (f a)),
      ∀ n : ℕ, M.time n ≤ t₁ n + 2 * len n + 2 + t₂ (len n) := by
  obtain ⟨M, hM⟩ := comp ea eb ec f g t₁ t₂ len h₁ h₂ hmono hlen
  exact ⟨M, fun n => (hM n).trans (by omega)⟩

/-- Upstream `time_of_polyTime`. -/
theorem ofPoly {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (h : PvsNP.PolyTimeComputable ea eb f) :
    ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n := by
  have _hc := Classical.em True
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.time_of_polyTime h

/-- A machine with a step bound below a polynomial is a polynomial-time machine. -/
theorem toPoly {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (h : ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n) :
    PvsNP.PolyTimeComputable ea eb f := by
  have _hc := Classical.em True
  obtain ⟨p, M, hM⟩ := h
  exact ⟨{ toTM2ComputableAux := M.toTM2ComputableAux
           time := p
           outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo,
             (M.outputsFun a).steps_le_m.trans (hM _)⟩ }⟩

theorem iff {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) :
    PvsNP.PolyTimeComputable ea eb f ↔
      ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n :=
  ⟨ofPoly ea eb f, toPoly ea eb f⟩

/-- Upstream `time_mono`. -/
theorem mono {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) (t t' : ℕ → ℕ)
    (h : ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t n)
    (ht : ∀ n : ℕ, t n ≤ t' n) :
    ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t' n := by
  have _hc := Classical.em True
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun n => (hM n).trans (ht n)⟩



theorem h_fun : ∀ {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a : α, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (fun a : α => g (f a)), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := @PvsNP.Units.m2_polytime_iff_time_poly.comp


theorem h_fun2 : ∀ {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (fun a => g (f a)), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := @PvsNP.Units.m2_polytime_iff_time_poly.comp


theorem h_comp2 : ∀ {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (g ∘ f), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := @PvsNP.Units.m2_polytime_iff_time_poly.comp


theorem h_e : ∀ (α β γ αΓ βΓ γΓ : Type) (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a : α, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (fun a : α => g (f a)), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := fun _ _ _ _ _ _ => PvsNP.Units.m2_polytime_iff_time_poly.comp


theorem h_ecomp : ∀ (α β γ αΓ βΓ γΓ : Type) (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a : α, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (g ∘ f), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := fun _ _ _ _ _ _ => PvsNP.Units.m2_polytime_iff_time_poly.comp


theorem h_flat : ∀ {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime eb ec g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ a : α, (eb (f a)).length ≤ len (ea a).length) → ∃ M : Turing.TM2ComputableInTime ea ec (g ∘ f), ∀ n : ℕ, M.time n ≤ t₁ n + 2 * len n + 2 + t₂ (len n) := @PvsNP.Units.m2_polytime_iff_time_poly.comp'


theorem h_str : ∀ (f g : List Bool → List Bool) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ x : List Bool, (f x).length ≤ len x.length) → ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => g (f x)), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := fun f g t₁ t₂ len h₁ h₂ hm hl => PvsNP.Units.m2_polytime_iff_time_poly.comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString f g t₁ t₂ len h₁ h₂ hm hl


theorem h_strc : ∀ (f g : List Bool → List Bool) (t₁ t₂ len : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString f, ∀ n : ℕ, M.time n ≤ t₁ n) → (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString g, ∀ n : ℕ, M.time n ≤ t₂ n) → Monotone t₂ → (∀ x : List Bool, (f x).length ≤ len x.length) → ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (g ∘ f), ∀ n : ℕ, M.time n ≤ t₁ n + (2 * len n + 2) + t₂ (len n) := fun f g t₁ t₂ len h₁ h₂ hm hl => PvsNP.Units.m2_polytime_iff_time_poly.comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString f g t₁ t₂ len h₁ h₂ hm hl


theorem h_ofpoly : ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β), PvsNP.PolyTimeComputable ea eb f → ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n := @PvsNP.Units.m2_polytime_iff_time_poly.ofPoly


theorem h_ofpoly2 : ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β), PvsNP.PolyTimeComputable ea eb f → ∃ p : Polynomial ℕ, ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ p.eval n := @PvsNP.Units.m2_polytime_iff_time_poly.ofPoly


theorem h_ofpolyi : ∀ {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}, PvsNP.PolyTimeComputable ea eb f → ∃ p : Polynomial ℕ, ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ p.eval n := fun {_ _ _ _} {ea eb f} h => PvsNP.Units.m2_polytime_iff_time_poly.ofPoly ea eb f h


theorem h_ofpolys : ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString f), ∀ n : ℕ, M.time n ≤ p.eval n := fun f h => PvsNP.Units.m2_polytime_iff_time_poly.ofPoly PvsNP.encodeString PvsNP.encodeString f h


theorem h_iff : ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β), PvsNP.PolyTimeComputable ea eb f ↔ ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n := @PvsNP.Units.m2_polytime_iff_time_poly.iff


theorem h_iff2 : ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β), PvsNP.PolyTimeComputable ea eb f ↔ ∃ p : Polynomial ℕ, ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ p.eval n := @PvsNP.Units.m2_polytime_iff_time_poly.iff


theorem h_iffs : ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f ↔ ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString f), ∀ n : ℕ, M.time n ≤ p.eval n := fun f => PvsNP.Units.m2_polytime_iff_time_poly.iff PvsNP.encodeString PvsNP.encodeString f


theorem h_mono : ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) (t t' : ℕ → ℕ), (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t n) → (∀ n : ℕ, t n ≤ t' n) → ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t' n := @PvsNP.Units.m2_polytime_iff_time_poly.mono


theorem h_monoi : ∀ {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β} {t t' : ℕ → ℕ}, (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t n) → (∀ n : ℕ, t n ≤ t' n) → ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ t' n := fun {_ _ _ _} {ea eb f t t'} h ht => PvsNP.Units.m2_polytime_iff_time_poly.mono ea eb f t t' h ht


end PvsNP.Units.m2_polytime_iff_time_poly

theorem PvsNP.Units.m2_polytime_iff_time_poly :
    ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β),
      PvsNP.PolyTimeComputable ea eb f ↔
        ∃ (p : Polynomial ℕ) (M : Turing.TM2ComputableInTime ea eb f), ∀ n : ℕ, M.time n ≤ p.eval n :=
  PvsNP.Units.m2_polytime_iff_time_poly.h_iff
