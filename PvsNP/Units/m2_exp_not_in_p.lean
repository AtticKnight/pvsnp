import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-!
Some language decidable in time `2 ^ (n ^ k) + k` is not in P. The diagonal language is the one
built upstream (pequalnp-proofs, Apache-2.0, commit 8df87a862bd9a618faecf10ba65bff72706442c9,
`Universal/ExpHierarchy.lean`) and settled in `PvsNP.Units.fr_ladner`, which this file imports;
only the bridge to the campaign's definitions is written here.
-/

namespace PvsNP.Units.m2_exp_not_in_p

theorem bridge :
    ∃ L : Language Bool,
      (∃ k : ℕ, L ∈ PvsNP.Units.fr_ladner.PEqualNP.Library.DTIME
        (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧
      L ∉ PvsNP.Units.fr_ladner.PEqualNP.Library.P :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expHierarchy

end PvsNP.Units.m2_exp_not_in_p

theorem PvsNP.Units.m2_exp_not_in_p : ∃ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
  L ∉ PvsNP.P := by
  obtain ⟨L, ⟨k, f, hf, M, hM⟩, hP⟩ := PvsNP.Units.m2_exp_not_in_p.bridge
  exact ⟨L, ⟨k, f, M, hf, hM⟩, fun h => hP ((PvsNP.Units.fr_ladner.P_iff L).1 h)⟩
