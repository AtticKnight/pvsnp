import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin.Lang

/-- SAT reduces to 3SAT in the vendored model: the vendored hardness proof of `SATStr`, run on
`SATStr`'s own verifier program, already ends in a Tseytin transform, whose every clause has
three literals. -/
theorem PvsNP.Units.m3_sat_to_3sat : CookLevin.reducesPoly SATStr
    (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) := by
  obtain ⟨W⟩ := SATStr.inNPCmd_SATStr
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
  have hfront : FlatSingleTMGenNP
      (FrontLifting.fQ W.toNPWitness (FrontWitness.MmaxF W.toNPWitness cm km dm)
        (FrontWitness.MstepF W.toNPWitness cs ks ds) x) ↔ SATStr x :=
    FrontLifting.fQ_correct W.toNPWitness (FrontWitness.MmaxF W.toNPWitness cm km dm)
      (FrontWitness.MstepF W.toNPWitness cs ks ds) hmax hsteps x
  have hchain := S1SATComp.s1_to_SAT_correct
    (FrontLifting.fQ W.toNPWitness (FrontWitness.MmaxF W.toNPWitness cm km dm)
      (FrontWitness.MstepF W.toNPWitness cs ks ds) x)
  have key := hfront.symm.trans hchain
  simp only [Function.comp_apply] at key ⊢
  rw [hcnf]
  refine ⟨fun h => ⟨fun C hC => ?_, key.mp h⟩, fun h => key.mpr h.2⟩
  exact le_of_eq ((kCNF_clause_length 3 _).mp (PreTseytin.preTseytin_kCNF3 _ _) C hC)
