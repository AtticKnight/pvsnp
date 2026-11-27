import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_finite_patch
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_nphard_transfer
import PvsNP.Units.m2_karp_trans

theorem PvsNP.Units.m2_hard_finite_patch :
∀ (L L' : Language Bool) (S : Finset (List Bool)), (∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) →
  (∃ y : List Bool, y ∈ L') → (∃ z : List Bool, z ∉ L') →
    (PvsNP.NPHard L → PvsNP.NPHard L') ∧
      ((∀ L' : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
          PvsNP.KarpReducible L' L) →
        (∀ L' : Language Bool,
          (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
            PvsNP.KarpReducible L' L')) := by
  intro L L' S hAgree hy hz
  have hred : PvsNP.KarpReducible L L' :=
    PvsNP.Units.m2_karp_finite_patch L' L L' S (PvsNP.Units.m2_karp_refl L') hy hz
      (fun x hx => (hAgree x hx).symm)
  constructor
  · exact fun hNP => PvsNP.Units.m2_nphard_transfer L L' hNP hred
  · intro _ L'' _
    exact PvsNP.Units.m2_karp_refl L''
