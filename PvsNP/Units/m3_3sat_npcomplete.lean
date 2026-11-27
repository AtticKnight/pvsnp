import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_3sat_in_np

/-!
# m3_3sat_npcomplete: the Tseytin 3-CNF trick, for any language in the vendored NP

The settled unit `m3_sat_to_3sat` (github.com/makedotfun/pvsnp, PvsNP/Units/m3_sat_to_3sat.lean) observes that
the vendored hardness chain, run on a language's own verifier program, ends in a Tseytin transform whose every
clause has exactly three literals. `gen3` runs the same argument for any language `Q` in the vendored NP
(`CookLevin.Sim.inNP_inNPCmd` gives its verifier program); the rest are corollaries. 3SAT's membership in NP is
the settled unit `m3_3sat_in_np`, imported.
-/

open CookLevin.Lang

namespace PvsNP.Units.m3_3sat_npcomplete

/-- Any language in the vendored NP reduces, by a polynomial-time single-tape machine, to SAT strings whose
formulas have exactly three literals per clause. -/
theorem gen3 (Q : List Bool → Prop) (hQ : CookLevin.inNP Q) :
    ∃ (f : List Bool → List Bool) (t : ℕ → ℕ) (M : FlatTM), inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧
      CookLevin.computesInTime M f t ∧
      ∀ x, (Q x ↔ SAT (SATStr.cnfOf (f x))) ∧ ∀ C ∈ SATStr.cnfOf (f x), C.length = 3 := by
  obtain ⟨W⟩ := CookLevin.Sim.inNP_inNPCmd hQ
  obtain ⟨cm, km, dm, cs, ks, ds, hmax, hsteps⟩ :=
    FrontWitness.exists_front_constants W.toNPWitness
  obtain ⟨t, M, ht, hM, h1, hcomp⟩ :=
    (SATStrComp.front_to_SATStr_witness W.toNPWitness cm km dm cs ks ds).toMachine
      (fun x => W.encX_canonical x)
      (SATStrComp.front_to_SATStr_decodeOut W.toNPWitness cm km dm cs ks ds)
  refine ⟨_, t, M, ht, hM, h1, hcomp, fun x => ?_⟩
  have hcnf : ∀ N, SATStr.cnfOf (SATToSATStr.satToStr N) = N := fun N => by
    unfold SATStr.cnfOf
    rw [SATToSATStr.strBits_satToStr, CnfWellFormed.parseTotal_encodeCnf]
  have hfront := FrontLifting.fQ_correct W.toNPWitness (FrontWitness.MmaxF W.toNPWitness cm km dm)
      (FrontWitness.MstepF W.toNPWitness cs ks ds) hmax hsteps x
  have hchain := S1SATComp.s1_to_SAT_correct
    (FrontLifting.fQ W.toNPWitness (FrontWitness.MmaxF W.toNPWitness cm km dm)
      (FrontWitness.MstepF W.toNPWitness cs ks ds) x)
  have key := hfront.symm.trans hchain
  simp only [Function.comp_apply] at key ⊢
  rw [hcnf]
  exact ⟨key, fun C hC => (kCNF_clause_length 3 _).mp (PreTseytin.preTseytin_kCNF3 _ _) C hC⟩

/-- Every language in the vendored NP reduces to 3SAT. -/
theorem to3 : ∀ Q : List Bool → Prop, CookLevin.inNP Q →
    CookLevin.reducesPoly Q (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) := by
  intro Q hQ
  obtain ⟨f, t, M, ht, hM, h1, hc, h⟩ := gen3 Q hQ
  exact ⟨f, t, M, ht, hM, h1, hc, fun x =>
    ⟨fun hx => ⟨fun C hC => le_of_eq ((h x).2 C hC), (h x).1.mp hx⟩, fun hx => (h x).1.mpr hx.2⟩⟩

/-- Every language in the vendored NP reduces to exactly-3 SAT. -/
theorem toE3 : ∀ Q : List Bool → Prop, CookLevin.inNP Q →
    CookLevin.reducesPoly Q (fun x => (∀ C ∈ SATStr.cnfOf x, C.length = 3) ∧ SAT (SATStr.cnfOf x)) := by
  intro Q hQ
  obtain ⟨f, t, M, ht, hM, h1, hc, h⟩ := gen3 Q hQ
  exact ⟨f, t, M, ht, hM, h1, hc, fun x => ⟨fun hx => ⟨(h x).2, (h x).1.mp hx⟩, fun hx => (h x).1.mpr hx.2⟩⟩

/-- SAT reduces to exactly-3 SAT (vendored model). -/
theorem e3 : CookLevin.reducesPoly SATStr
    (fun x => (∀ C ∈ SATStr.cnfOf x, C.length = 3) ∧ SAT (SATStr.cnfOf x)) :=
  toE3 _ CookLevin.cook_levin.2

/-- SAT reduces to k-SAT for every k ≥ 3 (vendored model). -/
theorem ksat : ∀ k : ℕ, 3 ≤ k → CookLevin.reducesPoly SATStr
    (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ k) ∧ SAT (SATStr.cnfOf x)) := by
  intro k hk
  obtain ⟨f, t, M, ht, hM, h1, hc, h⟩ := gen3 SATStr CookLevin.cook_levin.2
  exact ⟨f, t, M, ht, hM, h1, hc, fun x =>
    ⟨fun hx => ⟨fun C hC => by have := (h x).2 C hC; omega, (h x).1.mp hx⟩, fun hx => (h x).1.mpr hx.2⟩⟩

/-- 3SAT is NP-hard in the vendored model. -/
theorem hard3 : CookLevin.NPhard (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) :=
  fun Q hQ => to3 Q hQ

/-- Exactly-3 SAT is NP-hard in the vendored model. -/
theorem hardE3 : CookLevin.NPhard (fun x => (∀ C ∈ SATStr.cnfOf x, C.length = 3) ∧ SAT (SATStr.cnfOf x)) :=
  fun Q hQ => toE3 Q hQ

/-- 3SAT is NP-complete in the vendored model. -/
theorem npc3 : CookLevin.NPcomplete (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) :=
  ⟨hard3, PvsNP.Units.m3_3sat_in_np⟩

end PvsNP.Units.m3_3sat_npcomplete


theorem PvsNP.Units.m3_3sat_npcomplete :
    CookLevin.NPcomplete (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) :=
  PvsNP.Units.m3_3sat_npcomplete.npc3
