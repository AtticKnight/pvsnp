import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Machines/ConstList.lean (constList, constList_run, constList_polyTime: time X + 1) and
  lean/PEqualNP/Library/Machines/Reverse.lean (reverseComputable: time X + 1).
MODIFIED from those files: the machines are taken from the settled campaign units fr_ladner
(github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean: constList, constListProg, constList_run) and
m2_reverse_polytime (PvsNP/Units/m2_reverse_polytime.lean: revTM, rev_outputs), both imported. The closing
theorems keep the upstream step bound `n + 1` explicit, with the campaign's definitions in PvsNP.Defs.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_const_time

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Upstream `constList_polyTime` with its time `X + 1` as a step bound. -/
theorem constTime (l : List Bool) :
    ∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l), ∀ n : ℕ, M.time n ≤ n + 1 := by
  have _hc := Classical.em True
  exact ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => n + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := le_refl _ } }, fun _ => le_refl _⟩

theorem constM (u : List Bool) :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => u), ∀ n : ℕ, M.time n ≤ n + 1 := by
  obtain ⟨M, hM⟩ := constTime u
  exact ⟨M, hM⟩

theorem revM : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.reverse), ∀ n : ℕ, M.time n ≤ n + 1 := by
  have _hc := Classical.em True
  exact ⟨{ tm := PvsNP.Units.m2_reverse_polytime.revTM
           inputAlphabet := PvsNP.Units.m2_reverse_polytime.inEquiv
           outputAlphabet := PvsNP.Units.m2_reverse_polytime.outEquiv
           time := fun n => (Polynomial.X + Polynomial.C 1).eval n
           outputsFun := PvsNP.Units.m2_reverse_polytime.rev_outputs }, fun n => by simp⟩

theorem revP : ∃ M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.reverse), M.time = Polynomial.X + 1 := by
  have _hc := Classical.em True
  exact ⟨{ tm := PvsNP.Units.m2_reverse_polytime.revTM
           inputAlphabet := PvsNP.Units.m2_reverse_polytime.inEquiv
           outputAlphabet := PvsNP.Units.m2_reverse_polytime.outEquiv
           time := Polynomial.X + Polynomial.C 1
           outputsFun := PvsNP.Units.m2_reverse_polytime.rev_outputs }, by simp⟩

theorem revC : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.reverse)), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨M, hM⟩ := revM
  exact ⟨1, M, fun n => by simpa using hM n⟩

theorem constC (u : List Bool) :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => u)), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨M, hM⟩ := constM u
  exact ⟨1, M, fun n => by simpa using hM n⟩



theorem h_rev_n : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse), ∀ n, M.time n ≤ n + 1 := PvsNP.Units.m2_tm_const_time.revM


theorem h_rev_h : ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse), ∀ n : ℕ, h.time n ≤ n + 1 := PvsNP.Units.m2_tm_const_time.revM


theorem h_rev_c : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse)), ∀ n : ℕ, M.time n ≤ c * n + c := PvsNP.Units.m2_tm_const_time.revC


theorem h_rev_p : ∃ M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse), M.time = Polynomial.X + 1 := PvsNP.Units.m2_tm_const_time.revP


theorem h_const : ∀ u : List Bool, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun _ : List Bool => u), ∀ n : ℕ, M.time n ≤ n + 1 := PvsNP.Units.m2_tm_const_time.constM


theorem h_const_n : ∀ u : List Bool, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun _ : List Bool => u), ∀ n, M.time n ≤ n + 1 := PvsNP.Units.m2_tm_const_time.constM


theorem h_const_l : ∀ l : List Bool, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun _ : List Bool => l), ∀ n : ℕ, M.time n ≤ n + 1 := PvsNP.Units.m2_tm_const_time.constM


theorem h_const_c : ∀ u : List Bool, ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun _ : List Bool => u)), ∀ n : ℕ, M.time n ≤ c * n + c := PvsNP.Units.m2_tm_const_time.constC


end PvsNP.Units.m2_tm_const_time

theorem PvsNP.Units.m2_tm_const_time :
    ∀ u : List Bool, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun _ : List Bool => u), ∀ n : ℕ, M.time n ≤ n + 1 :=
  PvsNP.Units.m2_tm_const_time.h_const
