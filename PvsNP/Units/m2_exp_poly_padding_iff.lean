import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_subset_exp

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_poly_padding_iff

theorem dropN_pad (m : ℕ) (x : List Bool) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN (List.replicate (x.length ^ m) true ++ false :: x) = x :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ m) x

end PvsNP.Units.m2_exp_poly_padding_iff

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem PvsNP.Units.m2_exp_poly_padding_iff :
    ∀ (L : Language Bool) (m : ℕ),
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({s : List Bool | ∃ y : List Bool, y ∈ L ∧ s = List.replicate (y.length ^ m) true ++ false :: y} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  intro L m
  constructor
  · intro hL
    have hShape := PvsNP.Units.m2_p_subset_exp _
      (PvsNP.Units.m2_np_poly_padding_iff.shape_in_P m)
    have hPull : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({s : List Bool | dropN s ∈ L} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
      PvsNP.Units.m2_exp_down_closed _ L ⟨dropN, cpt_dropN, fun _ => Iff.rfl⟩ hL
    have heq : (({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly m x} : Language Bool) ⊓
        ({s : List Bool | dropN s ∈ L} : Language Bool)) =
        ({s : List Bool | ∃ y : List Bool, y ∈ L ∧ s = List.replicate (y.length ^ m) true ++ false :: y} : Language Bool) := by
      ext s
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        have hdx := PvsNP.Units.m2_exp_poly_padding_iff.dropN_pad m x
        change dropN (PvsNP.Units.m2_np_poly_padding_iff.padPoly m x) ∈ L at hx
        have hp : PvsNP.Units.m2_np_poly_padding_iff.padPoly m x = List.replicate (x.length ^ m) true ++ false :: x := rfl
        rw [hp, hdx] at hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, rfl⟩, ?_⟩
        show dropN (List.replicate (x.length ^ m) true ++ false :: x) ∈ L
        rw [PvsNP.Units.m2_exp_poly_padding_iff.dropN_pad m x]
        exact hx
    rw [← heq]
    exact PvsNP.Units.m2_exp_inter _ _ hShape hPull
  · intro hPad
    refine PvsNP.Units.m2_exp_down_closed L _
      ⟨PvsNP.Units.m2_np_poly_padding_iff.padPoly m,
        PvsNP.Units.m2_np_poly_padding_iff.cpt_padPoly m, fun x => ?_⟩ hPad
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hd := congrArg dropN hxy
      have hdx : dropN (PvsNP.Units.m2_np_poly_padding_iff.padPoly m x) = x :=
        dropN_un (x.length ^ m) x
      have hdy := PvsNP.Units.m2_exp_poly_padding_iff.dropN_pad m y
      rw [hdx, hdy] at hd
      subst hd
      exact hy
