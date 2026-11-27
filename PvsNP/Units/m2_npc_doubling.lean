import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_hom_np
import PvsNP.Units.tf_fun_flatmap_all
import PvsNP.Units.m2_npc_transfer

/-
Closes m2_npc_doubling: doubling every bit of an NP-complete language keeps it
NP-complete. Membership in NP follows from `tc_closure_hom_np`, and the
bit-doubling map itself (`tf_fun_flatmap_all`) is an injective Karp reduction
from `L`, so `m2_npc_transfer` transfers NP-completeness.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_npc_doubling

theorem dbl_inj : ∀ x₁ x₂ : List Bool,
    x₁.flatMap (fun b => [b, b]) = x₂.flatMap (fun b => [b, b]) → x₁ = x₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
    injection h with hab htail
    injection htail with _ hrest
    exact congrArg₂ List.cons hab (dbl_inj xs ys hrest)

end PvsNP.Units.m2_npc_doubling

/-- Doubling every bit of the strings of an NP-complete language keeps it NP-complete (TM2). -/
theorem PvsNP.Units.m2_npc_doubling :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPComplete ({y : List Bool | ∃ x ∈ L, y = x.flatMap (fun b => [b, b])} : Language Bool) := by
  intro L hL
  have hNP : ({y : List Bool | ∃ x ∈ L, y = x.flatMap (fun b => [b, b])} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.tc_closure_hom_np (fun b => [b, b]) (fun _ => by simp) L hL.1
  have hRed : PvsNP.KarpReducible L
      ({y : List Bool | ∃ x ∈ L, y = x.flatMap (fun b => [b, b])} : Language Bool) :=
    ⟨fun x => x.flatMap (fun b => [b, b]),
      PvsNP.Units.tf_fun_flatmap_all (fun b => [b, b]),
      fun x => ⟨fun hx => ⟨x, hx, rfl⟩,
        fun ⟨x', hx', hEq⟩ => by
          have hxEq := PvsNP.Units.m2_npc_doubling.dbl_inj x x' hEq
          rwa [hxEq]⟩⟩
  exact PvsNP.Units.m2_npc_transfer L _ hL hNP hRed
