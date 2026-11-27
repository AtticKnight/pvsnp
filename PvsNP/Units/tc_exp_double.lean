import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_exp_down_closed

namespace PvsNP.Units.tc_exp_double

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private abbrev firstHalf (x : List Bool) : List Bool := (unpairB (half x ++ false :: x)).1

private theorem firstHalf_eq (x : List Bool) : firstHalf x = x.take (x.length / 2) := by
  simp [firstHalf, half_eq, unpairB, un]

private theorem cpt_firstHalf :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString firstHalf :=
  cpt_comp (ea := fun x : List Bool => x) (eb := fun x : List Bool => x)
    (ec := fun x : List Bool => x)
    (f := fun x : List Bool => half x ++ false :: x) (g := fun s : List Bool => (unpairB s).1)
    (cpt_app2 cpt_half (cpt_cons1 false cpt_id)) cpt_unpairB1

private theorem exp_firstHalf (L : Language Bool)
    (h : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ ({x | firstHalf x ∈ L} : Language Bool) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_exp_down_closed _ L ⟨firstHalf, cpt_firstHalf, fun _ => Iff.rfl⟩ h

theorem main : ∀ L : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u ∈ L, x = u ++ u) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L h
  have hww := PvsNP.Units.m2_p_subset_exp _ PvsNP.Units.m2_ww_in_p
  obtain ⟨k, f, M, hf, hM⟩ :=
    PvsNP.Units.m2_exp_inter _ _ hww (exp_firstHalf L h)
  refine ⟨k, f, M, fun x => ?_, hM⟩
  rw [← hf x]
  change (∃ u ∈ L, x = u ++ u) ↔ (∃ y : List Bool, x = y ++ y) ∧ firstHalf x ∈ L
  rw [firstHalf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hlen : (u ++ u).length / 2 = u.length := by
      rw [List.length_append]
      omega
    rw [hlen, List.take_left]
    exact ⟨⟨u, rfl⟩, hu⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    have hlen : (y ++ y).length / 2 = y.length := by
      rw [List.length_append]
      omega
    rw [hlen, List.take_left] at hy
    exact ⟨y, hy, rfl⟩

end PvsNP.Units.tc_exp_double

theorem PvsNP.Units.tc_exp_double :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u ∈ L, x = u ++ u) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_double.main
