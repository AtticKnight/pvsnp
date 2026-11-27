import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

import PvsNP.Units.m2_conp_down_closed

import PvsNP.Units.m2_exp_down_closed

/-
  Original work for the make.fun desk campaign `pvsnp`, unit `m2_fixed_quotient_conp_exp`:
  coNP and exponential time are closed under appending or prepending a fixed word.

  Proof idea: both languages are the preimage of `L` under a fixed polynomial-time map,
  `x ↦ x ++ w` or `x ↦ w ++ x`, which the settled unit `fr_ladner` computes with `cpt_app2`
  out of the identity and a constant machine; the settled units `m2_conp_down_closed` and
  `m2_exp_down_closed` close coNP and exponential time under Karp preimages.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_fixed_quotient_conp_exp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem cpt_append_right (w : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ w) :=
  cpt_app2 (u := fun x : List Bool => x) (v := fun _ : List Bool => w) cpt_id (cpt_const w)

theorem cpt_append_left (w : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => w ++ x) :=
  cpt_app2 (u := fun _ : List Bool => w) (v := fun x : List Bool => x) (cpt_const w) cpt_id

theorem main (w : List Bool) (L : Language Bool) :
    (L ∈ PvsNP.coNP → ({x : List Bool | x ++ w ∈ L} : Language Bool) ∈ PvsNP.coNP ∧
        ({x : List Bool | w ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) ∧
      ((∃ k : ℕ, ∃ (f : List Bool → Bool)
            (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
        (∃ k : ℕ, ∃ (f : List Bool → Bool)
            (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({y : List Bool | y ++ w ∈ L} : Language Bool) ↔ f x = true) ∧
              ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
          (∃ k : ℕ, ∃ (f : List Bool → Bool)
              (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ ({y : List Bool | w ++ y ∈ L} : Language Bool) ↔ f x = true) ∧
                ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) := by
  have hR : PvsNP.KarpReducible ({x : List Bool | x ++ w ∈ L} : Language Bool) L :=
    ⟨fun x => x ++ w, cpt_append_right w, fun x => Iff.rfl⟩
  have hL : PvsNP.KarpReducible ({x : List Bool | w ++ x ∈ L} : Language Bool) L :=
    ⟨fun x => w ++ x, cpt_append_left w, fun x => Iff.rfl⟩
  exact ⟨fun h => ⟨PvsNP.Units.m2_conp_down_closed _ _ hR h,
      PvsNP.Units.m2_conp_down_closed _ _ hL h⟩,
    fun h => ⟨PvsNP.Units.m2_exp_down_closed _ _ hR h,
      PvsNP.Units.m2_exp_down_closed _ _ hL h⟩⟩

end PvsNP.Units.m2_fixed_quotient_conp_exp

/-- coNP and exponential time are closed under a fixed prefix or suffix (TM2). -/
theorem PvsNP.Units.m2_fixed_quotient_conp_exp :
    ∀ (w : List Bool) (L : Language Bool),
  (L ∈ PvsNP.coNP → ({x : List Bool | x ++ w ∈ L} : Language Bool) ∈ PvsNP.coNP ∧
      ({x : List Bool | w ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) ∧
    ((∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ ({y : List Bool | y ++ w ∈ L} : Language Bool) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
        (∃ k : ℕ, ∃ (f : List Bool → Bool)
            (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({y : List Bool | w ++ y ∈ L} : Language Bool) ↔ f x = true) ∧
              ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) :=
  PvsNP.Units.m2_fixed_quotient_conp_exp.main
