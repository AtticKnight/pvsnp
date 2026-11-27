import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its machines (filterMap_polyTime, cpt_sel, cpt_const, cpt_comp) are
those of github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

/-- Every function of an answer bit is polynomial-time (TM2): keep the bit as a string, keep its
symbol only when it is true, and write `g true` or `g false` by that flag. -/
theorem PvsNP.Units.m2_tm_answer_decoder :
    ∀ g : Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeAnswer PvsNP.encodeString g := by
  intro g
  have h0 : PvsNP.PolyTimeComputable PvsNP.encodeAnswer PvsNP.encodeString (fun b : Bool => [b]) :=
    ⟨⟨(Turing.idComputableInPolyTime PvsNP.encodeAnswer).toTM2ComputableAux,
      (Turing.idComputableInPolyTime PvsNP.encodeAnswer).time,
      (Turing.idComputableInPolyTime PvsNP.encodeAnswer).outputsFun⟩⟩
  have hf : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.filterMap (fun b : Bool => if b then some true else none)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none)
      (fun _ => rfl)
  have hsel := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_sel hf (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const (g false))
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const (g true))
  have hc := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp h0 hsel
  have e : g = fun b : Bool => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel
      ([b].filterMap (fun b : Bool => if b then some true else none)) (g false) (g true) := by
    funext b
    cases b <;> simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel]
  rw [e]
  exact hc
