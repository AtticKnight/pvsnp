import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_p_time_hierarchy

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def padPoly (q : Polynomial ℕ) (z : List Bool) : List Bool :=
  un (q.eval z.length) ++ false :: z

lemma cpt_padPoly (q : Polynomial ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (padPoly q) := by
  have hFalseCons : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z : List Bool => false :: z) := by
    have h := cpt_comp (cpt_pair (constList_polyTime [false]) cpt_id) cpt_append
    exact h
  have h := cpt_comp (cpt_pair (L055 q) hFalseCons) cpt_append
  exact h

lemma expQ_padPoly (q : Polynomial ℕ) (z : List Bool) :
    expQ (padPoly q z) = pairB (unpairB z).1 (pairB z (un (q.eval z.length))) := by
  simp only [expQ, padPoly, hd_un, dropN_un]

end PvsNP.Units.m2_p_time_hierarchy

/-- Polynomial time hierarchy: for every degree `k`, there is a language in `P` not decidable in
time `n ^ k + k`. -/
theorem PvsNP.Units.m2_p_time_hierarchy :
    ∀ k : ℕ, ∃ L ∈ PvsNP.P,
      ¬ ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ n ^ k + k := by
  intro k
  let q : Polynomial ℕ := (Polynomial.X ^ k + Polynomial.C k + Polynomial.X) ^ 2
  let g : List Bool → Bool := fun z =>
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expG
      (PvsNP.Units.m2_p_time_hierarchy.padPoly q z)
  let L : Language Bool := {z | g z = true}
  have hL_in_P : L ∈ PvsNP.P := by
    refine ⟨g, ?_, fun _ => Iff.rfl⟩
    exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.m2_p_time_hierarchy.cpt_padPoly q)
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_expG
  refine ⟨L, hL_in_P, ?_⟩
  rintro ⟨f, M, hf, htime⟩
  obtain ⟨c, d, hc⟩ :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.compileBool
      M.tm M.inputAlphabet M.outputAlphabet
  let m : ℕ := max (2 * (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.encCode c).length + 1)
    (d + 1)
  let z : List Bool :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.encCode c)
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.un
        (m - (2 * (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.encCode c).length + 1)))
  have hzl : z.length = m := by
    simp only [z, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB_length,
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.un, List.length_replicate]
    omega
  have hq : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
      (PvsNP.Units.m2_p_time_hierarchy.padPoly q z) =
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.encCode c)
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB z
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.un (q.eval m))) := by
    rw [PvsNP.Units.m2_p_time_hierarchy.expQ_padPoly, hzl]
    simp only [z, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
  obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ M.time z.length ∧
      (flip bind (Turing.TM2.step M.tm.m))^[n]
        (some (Turing.initList M.tm (z.map M.inputAlphabet.invFun))) =
      some (Turing.haltList M.tm [M.outputAlphabet.invFun (f z)]) :=
    ⟨(M.outputsFun z).steps, (M.outputsFun z).steps_le_m, (M.outputsFun z).evals_in_steps⟩
  have ho := hc z (f z) n hev
  have hle : d * n + d ≤ q.eval m := by
    rw [hzl] at hn
    have hnm : n ≤ m ^ k + k := hn.trans (htime m)
    have hdm : d + 1 ≤ m := le_max_right _ _
    have hbase : m ^ k + k + m = Polynomial.eval m (Polynomial.X ^ k + Polynomial.C k + Polynomial.X) := by
      simp
    have hqeval : q.eval m = (m ^ k + k + m) ^ 2 := by
      simp [q]
    rw [hqeval]
    have h1 : d * n + d ≤ (d + 1) * (m ^ k + k + m) := by nlinarith
    have h2 : (d + 1) * (m ^ k + k + m) ≤ (m ^ k + k + m) * (m ^ k + k + m) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [sq]
    exact h1.trans h2
  have ho' := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.Code.outputsWithin_mono
    c _ hle _ ho
  have hV : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) (q.eval m) [1] := by
    rw [hq, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  have hiff : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) = true ↔ f z = true := by
    rw [hV]
    constructor
    · intro h1
      have heq : [1] = [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.bitCode (f z)] :=
        h1.2.symm.trans ho'.2
      cases hb : f z with
      | true => rfl
      | false =>
          rw [hb] at heq
          simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.bitCode] at heq
    · intro hb
      rw [hb] at ho'
      exact ho'
  have hneg : z ∈ L ↔ PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) = false := by
    change g z = true ↔ _
    simp only [g, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expG, Bool.not_eq_true']
  have hcontra : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) = true ↔
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) = false :=
    hiff.trans ((hf z).symm.trans hneg)
  cases hv : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.V
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.expQ
        (PvsNP.Units.m2_p_time_hierarchy.padPoly q z), []) with
  | true => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.1 rfl)
  | false => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.2 rfl)
