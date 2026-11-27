import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_padded_test_exp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp

/-
Original proof of `PvsNP.Units.m2_exp_iff_padded_p`, from the settled units it imports. Forward:
`m2_upward_padding` puts the padding of an exponential-time language in P. Backward: if a
polynomial-time `g` decides the padding with exponent `k`, then `z ↦ g (pad z)` is
`z ↦ (g ∘ Prod.fst) (pad z, z)`, which `m2_padded_test_exp` (with `u = v = id`, the projection of
`m2_pair_split_polytime` composed with `g` by `m2_polytime_comp`) computes within
`2 ^ (n ^ j) + j` steps; and since the padding is injective, `g (pad x) = true` exactly when
`x ∈ L`.
-/

namespace PvsNP.Units.m2_exp_iff_padded_p

/-- The padding `1^a 0 u` determines `a` and `u`. -/
theorem rep_inj : ∀ (a b : ℕ) (u v : List Bool),
    List.replicate a true ++ false :: u = List.replicate b true ++ false :: v → a = b ∧ u = v
  | 0, 0, _, _, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, u, v, h => by
    have := rep_inj a b u v (by simpa [List.replicate_succ] using h)
    exact ⟨by omega, this.2⟩

end PvsNP.Units.m2_exp_iff_padded_p

theorem PvsNP.Units.m2_exp_iff_padded_p :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
        ∃ k : ℕ, ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
            s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈
          PvsNP.P := by
  intro L
  constructor
  · rintro ⟨k, hexp⟩
    exact ⟨k, PvsNP.Units.m2_upward_padding L k hexp⟩
  · rintro ⟨k, g, hg, hdec⟩
    have hfst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1) := PvsNP.Units.m2_pair_split_polytime.1
    have hh := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
      PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1) g hfst hg
    have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (id : List Bool → List Bool) := ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
    obtain ⟨j, M, hM⟩ := PvsNP.Units.m2_padded_test_exp k id id _ hid hid hh
    refine ⟨j, _, M, fun x => ?_, hM⟩
    show x ∈ L ↔ g (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = true
    rw [← hdec]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have := PvsNP.Units.m2_exp_iff_padded_p.rep_inj _ _ _ _ he
      rw [this.2]
      exact hy
