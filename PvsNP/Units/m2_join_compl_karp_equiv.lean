import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_finite_patch

/-
The join of the complements and the complement of the join differ only at the empty string, which
lies in the complement of the join but not in the join of the complements. Each direction is the
identity patched at the empty string to a fixed string `false :: c` of the right membership.
Built on the settled units PvsNP.Units.fr_ladner (`cpt_id`) and m2_polytime_finite_patch of
github.com/makedotfun/pvsnp (Apache License 2.0). Nothing is copied; the units are imported.
-/

namespace PvsNP.Units.m2_join_compl_karp_equiv

theorem patch_poly (c : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if x = [] then c else x) :=
  PvsNP.Units.m2_polytime_finite_patch (fun x => x) _ {[]}
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    (fun x hx => by
      have hne : x ≠ [] := by simpa using hx
      simp [hne])

end PvsNP.Units.m2_join_compl_karp_equiv

theorem PvsNP.Units.m2_join_compl_karp_equiv :
    ∀ L₁ L₂ : Language Bool, (∃ y : List Bool, y ∈ L₁) → (∃ z : List Bool, z ∉ L₁) →
  PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁ᶜ, x = false :: y) ∨ (∃ y ∈ L₂ᶜ, x = true :: y)} : Language Bool)
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)ᶜ ∧
    PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)ᶜ
      ({x : List Bool | (∃ y ∈ L₁ᶜ, x = false :: y) ∨ (∃ y ∈ L₂ᶜ, x = true :: y)} : Language Bool) := by
  intro L₁ L₂ ⟨y₀, hy₀⟩ ⟨z₀, hz₀⟩
  have h1 : ∀ y : List Bool, y ∈ L₁ᶜ ↔ y ∉ L₁ := fun _ => Iff.rfl
  have h2 : ∀ y : List Bool, y ∈ L₂ᶜ ↔ y ∉ L₂ := fun _ => Iff.rfl
  refine ⟨⟨fun x => if x = [] then false :: y₀ else x,
      PvsNP.Units.m2_join_compl_karp_equiv.patch_poly _, fun x => ?_⟩,
    ⟨fun x => if x = [] then false :: z₀ else x,
      PvsNP.Units.m2_join_compl_karp_equiv.patch_poly _, fun x => ?_⟩⟩
  · show ((∃ y ∈ L₁ᶜ, x = false :: y) ∨ (∃ y ∈ L₂ᶜ, x = true :: y)) ↔
      ¬ ((∃ y ∈ L₁, (if x = [] then false :: y₀ else x) = false :: y) ∨
        (∃ y ∈ L₂, (if x = [] then false :: y₀ else x) = true :: y))
    rcases x with _ | ⟨b, y⟩
    · simp [hy₀]
    · cases b <;> simp [h1, h2]
  · show ¬ ((∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)) ↔
      ((∃ y ∈ L₁ᶜ, (if x = [] then false :: z₀ else x) = false :: y) ∨
        (∃ y ∈ L₂ᶜ, (if x = [] then false :: z₀ else x) = true :: y))
    rcases x with _ | ⟨b, y⟩
    · simp [h1, hz₀]
    · cases b <;> simp [h1, h2]
