import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.m2_join_lub

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library

/-- The reduction for the join: `[]` goes to the fixed non-member `z`, `false :: y` to
`f₁ y` and `true :: y` to `f₂ y`, chosen by emptiness and by the first bit (`sel` picks by
whether its first argument is empty; `hd` is the leading run of `true`s, empty exactly
when the list is empty or starts with `false`). -/
def joinRed (z : List Bool) (f₁ f₂ : List Bool → List Bool) : List Bool → List Bool :=
  fun x => sel x z (sel (hd x) (f₁ x.tail) (f₂ x.tail))

theorem joinRed_nil (z : List Bool) (f₁ f₂ : List Bool → List Bool) :
    joinRed z f₁ f₂ [] = z := rfl

theorem joinRed_false (z : List Bool) (f₁ f₂ : List Bool → List Bool) (y : List Bool) :
    joinRed z f₁ f₂ (false :: y) = f₁ y := by
  simp [joinRed, sel, hd]

theorem joinRed_true (z : List Bool) (f₁ f₂ : List Bool → List Bool) (y : List Bool) :
    joinRed z f₁ f₂ (true :: y) = f₂ y := by
  simp [joinRed, sel, hd]

/-- The join reduction runs in polynomial time: the tail, the head-run and the constant
are polynomial-time (the settled unit `fr_ladner`), the two reductions run on the tail,
and the two choices are `sel`. -/
theorem joinRed_polyTime {z : List Bool} {f₁ f₂ : List Bool → List Bool}
    (hf₁ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f₁)
    (hf₂ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f₂) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (joinRed z f₁ f₂) := by
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => f₁ x.tail) := cpt_comp cpt_tail hf₁
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => f₂ x.tail) := cpt_comp cpt_tail hf₂
  have hinner : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => sel (hd x) (f₁ x.tail) (f₂ x.tail)) := cpt_sel cpt_hd h1 h2
  have houter : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => sel x z (sel (hd x) (f₁ x.tail) (f₂ x.tail))) :=
    cpt_sel cpt_id (cpt_const z) hinner
  exact houter

end PvsNP.Units.m2_join_lub

/-- The join reduces to every language both sides reduce to, short of everything (TM2):
send `[]` to a fixed non-member, `false :: y` through the first reduction and `true :: y`
through the second. -/
theorem PvsNP.Units.m2_join_lub :
    ∀ L₁ L₂ L₃ : Language Bool, PvsNP.KarpReducible L₁ L₃ → PvsNP.KarpReducible L₂ L₃ →
      (∃ z : List Bool, z ∉ L₃) →
        PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) L₃ := by
  intro L₁ L₂ L₃ h₁ h₂ ⟨z, hz⟩
  obtain ⟨f₁, hf₁, hfm₁⟩ := h₁
  obtain ⟨f₂, hf₂, hfm₂⟩ := h₂
  refine ⟨PvsNP.Units.m2_join_lub.joinRed z f₁ f₂,
    PvsNP.Units.m2_join_lub.joinRed_polyTime hf₁ hf₂, fun x => ?_⟩
  cases x with
  | nil =>
    constructor
    · intro h
      have h' : (∃ y ∈ L₁, ([] : List Bool) = false :: y) ∨
          (∃ y ∈ L₂, ([] : List Bool) = true :: y) := h
      rcases h' with ⟨y, _, h⟩ | ⟨y, _, h⟩ <;> cases h
    · intro h
      rw [PvsNP.Units.m2_join_lub.joinRed_nil] at h
      exact absurd h hz
  | cons b y =>
    cases b with
    | false =>
      simp only [Set.mem_setOf_eq, PvsNP.Units.m2_join_lub.joinRed_false]
      constructor
      · intro h
        rcases h with ⟨y', hy', hxy⟩ | ⟨y', hy', hxy⟩
        · obtain ⟨-, rfl⟩ := List.cons.inj hxy
          exact (hfm₁ y).mp hy'
        · exact absurd (List.cons.inj hxy).1 (by simp)
      · intro h
        exact Or.inl ⟨y, (hfm₁ y).mpr h, rfl⟩
    | true =>
      simp only [Set.mem_setOf_eq, PvsNP.Units.m2_join_lub.joinRed_true]
      constructor
      · intro h
        rcases h with ⟨y', hy', hxy⟩ | ⟨y', hy', hxy⟩
        · exact absurd (List.cons.inj hxy).1 (by simp)
        · obtain ⟨-, rfl⟩ := List.cons.inj hxy
          exact (hfm₂ y).mp hy'
      · intro h
        exact Or.inr ⟨y, (hfm₂ y).mpr h, rfl⟩
