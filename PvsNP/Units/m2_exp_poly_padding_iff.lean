import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_subset_exp

namespace PvsNP.Units.m2_exp_poly_padding_iff

abbrev InExp (L : Language Bool) : Prop :=
  ∃ k : ℕ, ∃ (f : List Bool → Bool)
    (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
    (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k

theorem decode (m : ℕ) (x : List Bool) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
      (PvsNP.Units.m2_np_poly_padding_iff.padPoly m x) = x :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ m) x

end PvsNP.Units.m2_exp_poly_padding_iff

/-- Check the padding shape in P and extract the suffix. Encoding supplies a reduction in the reverse direction. -/
theorem PvsNP.Units.m2_exp_poly_padding_iff :
    ∀ (L : Language Bool) (m : ℕ),
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({s : List Bool | ∃ y : List Bool, y ∈ L ∧ s = List.replicate (y.length ^ m) true ++ false :: y} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  intro L m
  let padded : Language Bool := {s | ∃ y ∈ L, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly m y}
  let shape : Language Bool := {s | ∃ y, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly m y}
  let tail : Language Bool := {s | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈ L}
  change PvsNP.Units.m2_exp_poly_padding_iff.InExp L ↔ PvsNP.Units.m2_exp_poly_padding_iff.InExp padded
  have split : shape ⊓ tail = padded := by
    ext s
    constructor
    · rintro ⟨⟨y, rfl⟩, h⟩
      change PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
        (PvsNP.Units.m2_np_poly_padding_iff.padPoly m y) ∈ L at h
      exact ⟨y, (PvsNP.Units.m2_exp_poly_padding_iff.decode m y) ▸ h, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
        (PvsNP.Units.m2_np_poly_padding_iff.padPoly m y) ∈ L
      rwa [PvsNP.Units.m2_exp_poly_padding_iff.decode]
  constructor
  · intro hL
    have hS := PvsNP.Units.m2_p_subset_exp shape (PvsNP.Units.m2_np_poly_padding_iff.shape_in_P m)
    have red : PvsNP.KarpReducible tail L :=
      ⟨_, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN, fun _ => Iff.rfl⟩
    have hT := PvsNP.Units.m2_exp_down_closed tail L red hL
    exact split ▸ PvsNP.Units.m2_exp_inter shape tail hS hT
  · intro hP
    refine PvsNP.Units.m2_exp_down_closed L padded ⟨_, PvsNP.Units.m2_np_poly_padding_iff.cpt_padPoly m, ?_⟩ hP
    intro x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, eq⟩
      have et := congrArg PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN eq
      have exy : x = y := by simpa only [PvsNP.Units.m2_exp_poly_padding_iff.decode] using et
      exact exy.symm ▸ hy
