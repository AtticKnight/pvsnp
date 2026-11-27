import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_padded_test_exp

/-
Built on the settled units PvsNP.Units.fr_ladner (`pairB`, `unpairB`, `unpairB_pairB`, `hd`,
`hd_un`, `un`, `mulU`, `sel`, `V`, `V_spec`, `compileBool`, `encCode`, `bitCode`, `cpt_pairB`,
`cpt_pairB2`, `cpt_unpairB1`, `cpt_unpairB2`, `cpt_unpairB1_1`, `cpt_unpairB2_1`, `cpt_app2`,
`cpt_cons1`, `cpt_const`, `cpt_id`, `cpt_pair`, `cpt_mulU2`, `cpt_sel`, `cpt_hd1`, `cpt_Vflag`,
`fst_polyTime`, `Iter.iter_polyTime`), m2_transducer_polytime, m2_polytime_comp, and
m2_padded_test_exp of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.tc_exp_pow

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem map_true_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => u.map (fun _ => true)) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some true))
    (fun _ => none)
    (fun _ u => u.map (fun _ => true))
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

private theorem unpairB_map_true (u x : List Bool) :
    unpairB (u.map (fun _ => true) ++ false :: x) = (x.take u.length, x.drop u.length) := by
  have h1 : (u.map (fun _ => true) ++ false :: x).takeWhile id = u.map (fun _ => true) := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  have h2 : (u.map (fun _ => true) ++ false :: x).dropWhile id = false :: x := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  simp [unpairB]

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [fstRun, ih]

private theorem cpt_neU :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons _ l =>
        simp [fstRun, neU_true, PvsNP.encodeString, PvsNP.encodeAnswer,
          Computability.encodingList, Computability.encodeBool])

private theorem cpt_isEmpty :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun l : List Bool => l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
    (fun q => some q) true (fun l => by
      cases l with
      | nil => rfl
      | cons _ l =>
        have hfalse : ∀ m : List Bool,
            fstRun (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
              (fun q => some q) false m = [false] := by
          intro m
          induction m with
          | nil => rfl
          | cons _ t ih => simp [fstRun, ih]
        simp [fstRun, hfalse, PvsNP.encodeString, PvsNP.encodeAnswer,
          Computability.encodingList, Computability.encodeBool])

private theorem lift_bound (k₁ k₂ n : ℕ) :
    2 ^ (n ^ k₁) + k₁ ≤ 2 ^ (n ^ (k₁ + k₂ + 1)) + (k₁ + k₂ + 1) := by
  cases n with
  | zero =>
    cases k₁ with
    | zero => simp; omega
    | succ k₁' =>
      have h1 : 0 ^ (k₁' + 1) = 0 := zero_pow (by omega)
      have h2 : 0 ^ (k₁' + 1 + k₂ + 1) = 0 := zero_pow (by omega)
      rw [h1, h2]; omega
  | succ m =>
    have hpow : (m + 1) ^ k₁ ≤ (m + 1) ^ (k₁ + k₂ + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos m) (by omega)
    have h2 : 2 ^ ((m + 1) ^ k₁) ≤ 2 ^ ((m + 1) ^ (k₁ + k₂ + 1)) :=
      Nat.pow_le_pow_right (by decide) hpow
    omega

private theorem mono_exp_bound (k : ℕ) (hk : 1 ≤ k) {a b : ℕ} (hab : a ≤ b) :
    2 ^ (a ^ k) + k ≤ 2 ^ (b ^ k) + k := by
  have h1 : a ^ k ≤ b ^ k := Nat.pow_le_pow_left hab k
  have h2 : 2 ^ (a ^ k) ≤ 2 ^ (b ^ k) := Nat.pow_le_pow_right (by decide) h1
  omega

private theorem V_eq_f {f : List Bool → Bool}
    (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)
    {c : Code} {d : ℕ}
    (hc : ∀ (x : List Bool) (b : Bool) (t : ℕ),
      (flip bind (Turing.TM2.step M.tm.m))^[t]
        (some (Turing.initList M.tm (x.map M.inputAlphabet.invFun))) =
        some (Turing.haltList M.tm [M.outputAlphabet.invFun b]) →
      c.outputsWithin (x.map (fun b => cond b 1 0)) (d * t + d) [bitCode b])
    (y : List Bool) (T : ℕ) (hT : M.time y.length ≤ T) :
    V (pairB (encCode c) (pairB y (un (d * T + d))), []) = f y := by
  have hev : (flip bind (Turing.TM2.step M.tm.m))^[((M.outputsFun y).steps)]
      (some (Turing.initList M.tm (y.map M.inputAlphabet.invFun))) =
      some (Turing.haltList M.tm [M.outputAlphabet.invFun (f y)]) :=
    (M.outputsFun y).evals_in_steps
  have hsteps : (M.outputsFun y).steps ≤ T :=
    (M.outputsFun y).steps_le_m.trans hT
  have hcw := hc y (f y) (M.outputsFun y).steps hev
  have hle : d * (M.outputsFun y).steps + d ≤ d * T + d := by
    have := Nat.mul_le_mul_left d hsteps
    omega
  have hcw' : c.outputsWithin (y.map (fun b => cond b 1 0)) (d * T + d) [bitCode (f y)] :=
    Code.outputsWithin_mono c _ hle _ hcw
  cases hfy : f y with
  | true =>
    rw [hfy] at hcw'
    rw [V_spec]
    exact ⟨by simp, by simpa [bitCode] using hcw'⟩
  | false =>
    rw [hfy] at hcw'
    by_contra hne
    have hVtrue : V (pairB (encCode c) (pairB y (un (d * T + d))), []) = true := by
      cases hv : V (pairB (encCode c) (pairB y (un (d * T + d))), []) <;> simp_all
    rw [V_spec] at hVtrue
    have hcw1 : c.outputsWithin (y.map (fun b => cond b 1 0)) (d * T + d) [1] := by
      simpa using hVtrue.2
    have heq : [1] = [bitCode false] := hcw1.2.symm.trans hcw'.2
    simp [bitCode] at heq

private def Vflag (c : Code) (arg clk : List Bool) : List Bool :=
  if V (pairB (encCode c) (pairB arg clk), []) = true then [true] else []

private def rawMulStep (c₁ c₂ : Code) (st : List Bool) : List Bool :=
  let imm := (unpairB st).1
  let clks := (unpairB imm).1
  let clk₁ := (unpairB clks).1
  let clk₂ := (unpairB clks).2
  let x := (unpairB imm).2
  let var := (unpairB st).2
  let cnt := (unpairB var).1
  let found := (unpairB var).2
  let sp := unpairB (cnt.map (fun _ => true) ++ false :: x)
  let hit := sel (Vflag c₁ sp.1 clk₁) [] (Vflag c₂ sp.2 clk₂)
  let found' := sel found hit [true]
  pairB imm (pairB (true :: cnt) found')

private def mulStep (c₁ c₂ : Code) (st : List Bool) : List Bool :=
  let ns := rawMulStep c₁ c₂ st
  let bound := true :: true :: true :: st
  sel (ns.drop bound.length) ns st

private theorem mulStep_length_le (c₁ c₂ : Code) (st : List Bool) :
    (mulStep c₁ c₂ st).length ≤ st.length + 3 := by
  unfold mulStep sel
  dsimp only
  split_ifs with h
  · have hle := List.drop_eq_nil_iff.1 h
    simp only [List.length_cons] at hle
    omega
  · omega

private theorem mulStep_poly (c₁ c₂ : Code) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (mulStep c₁ c₂) := by
  have himm : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).1) := cpt_unpairB1
  have hclks : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).1).1) := cpt_unpairB1_1 himm
  have hclk₁ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB (unpairB st).1).1).1) := cpt_unpairB1_1 hclks
  have hclk₂ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB (unpairB st).1).1).2) := cpt_unpairB2_1 hclks
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).1).2) := cpt_unpairB2_1 himm
  have hvar : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).2) := cpt_unpairB2
  have hcnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).1) := cpt_unpairB1_1 hvar
  have hfound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).2) := cpt_unpairB2_1 hvar
  have hcnt_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => (unpairB (unpairB st).2).1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hcnt map_true_poly
  have hsp_code : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => ((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB (unpairB st).1).2) :=
    cpt_app2 hcnt_map (cpt_cons1 false hx)
  have hp1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB (unpairB st).1).2)).1) :=
    cpt_unpairB1_1 hsp_code
  have hp2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB (unpairB st).1).2)).2) :=
    cpt_unpairB2_1 hsp_code
  have hvf1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        if V (pairB (encCode c₁) (pairB (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB (unpairB st).1).2)).1
          (unpairB (unpairB (unpairB st).1).1).1), []) = true then [true] else []) :=
    cpt_Vflag (cpt_pairB2 (cpt_const (encCode c₁)) (cpt_pairB2 hp1 hclk₁)) (cpt_const [])
  have hvf2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        if V (pairB (encCode c₂) (pairB (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB (unpairB st).1).2)).2
          (unpairB (unpairB (unpairB st).1).1).2), []) = true then [true] else []) :=
    cpt_Vflag (cpt_pairB2 (cpt_const (encCode c₂)) (cpt_pairB2 hp2 hclk₂)) (cpt_const [])
  have hhit := cpt_sel hvf1 (cpt_const []) hvf2
  have hfound' := cpt_sel hfound hhit (cpt_const [true])
  have hraw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (rawMulStep c₁ c₂) :=
    cpt_pairB2 himm (cpt_pairB2 (cpt_cons1 true hcnt) hfound')
  have hbound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => true :: true :: true :: st) :=
    cpt_cons1 true (cpt_cons1 true (cpt_cons1 true cpt_id))
  have hbound_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => true :: true :: true :: st)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hbound map_true_poly
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawMulStep c₁ c₂ st)).2) :=
    cpt_unpairB2_1 (cpt_app2 hbound_map (cpt_cons1 false hraw))
  have hsel := cpt_sel hdrop hraw cpt_id
  have heq : (fun st : List Bool =>
      sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawMulStep c₁ c₂ st)).2
        (rawMulStep c₁ c₂ st) st) = mulStep c₁ c₂ := by
    funext st
    simp only [mulStep, unpairB_map_true]
  rwa [heq] at hsel

private theorem mulStep_valid (c₁ c₂ : Code) (clk₁ clk₂ x : List Bool) (i : ℕ) (b : Bool) :
    let imm := pairB (pairB clk₁ clk₂) x
    let found := if b then [true] else []
    mulStep c₁ c₂ (pairB imm (pairB (un i) found)) =
      pairB imm (pairB (un (i + 1))
        (if (b || (V (pairB (encCode c₁) (pairB (x.take i) clk₁), []) &&
                   V (pairB (encCode c₂) (pairB (x.drop i) clk₂), []))) then [true] else [])) := by
  intro imm found
  have hraw : rawMulStep c₁ c₂ (pairB imm (pairB (un i) found)) =
      pairB imm (pairB (un (i + 1))
        (if (b || (V (pairB (encCode c₁) (pairB (x.take i) clk₁), []) &&
                   V (pairB (encCode c₂) (pairB (x.drop i) clk₂), []))) then [true] else [])) := by
    unfold rawMulStep
    simp only [unpairB_pairB, unpairB_map_true, un_length, Vflag]
    have hcons : true :: un i = un (i + 1) := by simp [un, List.replicate_succ]
    rw [hcons]
    have himm1 : (unpairB (unpairB imm).1).1 = clk₁ := by simp [imm, unpairB_pairB]
    have himm2 : (unpairB (unpairB imm).1).2 = clk₂ := by simp [imm, unpairB_pairB]
    have himmx : (unpairB imm).2 = x := by simp [imm, unpairB_pairB]
    rw [himm1, himm2, himmx]
    congr 1; congr 1
    cases b <;> cases h1 : V (pairB (encCode c₁) (pairB (x.take i) clk₁), []) <;>
      cases h2 : V (pairB (encCode c₂) (pairB (x.drop i) clk₂), []) <;>
      simp [found, sel]
  have hlen : (rawMulStep c₁ c₂ (pairB imm (pairB (un i) found))).length ≤
      (pairB imm (pairB (un i) found)).length + 3 := by
    rw [hraw]
    simp only [pairB_length, un_length]
    cases b <;>
      cases (V (pairB (encCode c₁) (pairB (x.take i) clk₁), []) &&
             V (pairB (encCode c₂) (pairB (x.drop i) clk₂), [])) <;>
      simp [found] <;> omega
  unfold mulStep
  dsimp only
  have hnil : (rawMulStep c₁ c₂ (pairB imm (pairB (un i) found))).drop
      (true :: true :: true :: pairB imm (pairB (un i) found)).length = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_cons]
    omega
  rw [hnil]
  simp only [sel, ↓reduceIte]
  exact hraw

private theorem iter_mulStep (c₁ c₂ : Code) (clk₁ clk₂ x : List Bool) :
    ∀ (t i : ℕ) (b : Bool),
      let imm := pairB (pairB clk₁ clk₂) x
      (mulStep c₁ c₂)^[t] (pairB imm (pairB (un i) (if b then [true] else []))) =
        pairB imm (pairB (un (i + t))
          (if (b || (List.range t).any (fun r =>
              V (pairB (encCode c₁) (pairB (x.take (i + r)) clk₁), []) &&
              V (pairB (encCode c₂) (pairB (x.drop (i + r)) clk₂), [])))
           then [true] else [])) := by
  intro t
  induction t with
  | zero =>
    intro i b
    simp
  | succ t ih =>
    intro i b
    dsimp only
    rw [Function.iterate_succ_apply, mulStep_valid, ih (i + 1)]
    have hadd : i + 1 + t = i + (t + 1) := by omega
    rw [hadd]
    congr 1; congr 1
    have heq : (b || (V (pairB (encCode c₁) (pairB (x.take i) clk₁), []) &&
        V (pairB (encCode c₂) (pairB (x.drop i) clk₂), [])) ||
        (List.range t).any (fun r =>
          V (pairB (encCode c₁) (pairB (x.take (i + 1 + r)) clk₁), []) &&
          V (pairB (encCode c₂) (pairB (x.drop (i + 1 + r)) clk₂), []))) =
      (b || (List.range (t + 1)).any (fun r =>
          V (pairB (encCode c₁) (pairB (x.take (i + r)) clk₁), []) &&
          V (pairB (encCode c₂) (pairB (x.drop (i + r)) clk₂), []))) := by
      cases b with
      | true => simp
      | false =>
        simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_range]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨r, hr, h1, h2⟩)
          · exact ⟨0, by omega, by simpa using h1, by simpa using h2⟩
          · refine ⟨r + 1, by omega, ?_, ?_⟩
            · have : i + (r + 1) = i + 1 + r := by omega
              rw [this]; exact h1
            · have : i + (r + 1) = i + 1 + r := by omega
              rw [this]; exact h2
        · rintro ⟨r, hr, h1, h2⟩
          cases r with
          | zero => exact Or.inl ⟨by simpa using h1, by simpa using h2⟩
          | succ r' =>
            right
            refine ⟨r', by omega, ?_, ?_⟩
            · have : i + 1 + r' = i + (r' + 1) := by omega
              rw [this]; exact h1
            · have : i + 1 + r' = i + (r' + 1) := by omega
              rw [this]; exact h2
    rw [heq]

private theorem exp_one :
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ (1 : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => pairB q.1 q.2) := by
    rw [← encodePair_eq]; exact cpt_pairB
  have hdecS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (List.isEmpty ∘ (fun s : List Bool => (unpairB s).2)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ cpt_unpairB2 cpt_isEmpty
  have hdecP := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpb hdecS
  have heq : ((List.isEmpty ∘ (fun s : List Bool => (unpairB s).2)) ∘
      (fun q : List Bool × List Bool => pairB q.1 q.2)) = (fun q : List Bool × List Bool => q.2.isEmpty) := by
    funext ⟨a, b⟩; simp [unpairB_pairB]
  obtain ⟨j, M, hM⟩ := PvsNP.Units.m2_padded_test_exp 1 id id
    (fun q : List Bool × List Bool => q.2.isEmpty) cpt_id cpt_id (by rwa [heq] at hdecP)
  refine ⟨j, _, M, fun x => ?_, hM⟩
  rw [Language.mem_one]
  cases x <;> simp

private theorem exp_mul (L₁ L₂ : Language Bool)
    (h₁ : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)
    (h₂ : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ * L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rcases h₁ with ⟨k₁, f₁, M₁, hf₁, ht₁⟩
  rcases h₂ with ⟨k₂, f₂, M₂, hf₂, ht₂⟩
  obtain ⟨c₁, d₁, hc₁⟩ := compileBool M₁.tm M₁.inputAlphabet M₁.outputAlphabet
  obtain ⟨c₂, d₂, hc₂⟩ := compileBool M₂.tm M₂.inputAlphabet M₂.outputAlphabet
  let k := k₁ + k₂ + 1
  obtain ⟨cStep⟩ := mulStep_poly c₁ c₂
  have hIter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun q : List Bool × List Bool => (mulStep c₁ c₂)^[q.2.length] q.1) :=
    Iter.iter_polyTime (mulStep c₁ c₂) cStep 3 (mulStep_length_le c₁ c₂)
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => pairB q.1 q.2) := by
    rw [← encodePair_eq]; exact cpt_pairB
  have hpad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => hd (unpairB s).1) := cpt_hd1 cpt_unpairB1
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).2) := cpt_unpairB2
  have hclk₁ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => mulU (un d₁) (hd (unpairB s).1) ++ un d₁) :=
    cpt_app2 (cpt_mulU2 (cpt_const (un d₁)) hpad) (cpt_const (un d₁))
  have hclk₂ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => mulU (un d₂) (hd (unpairB s).1) ++ un d₂) :=
    cpt_app2 (cpt_mulU2 (cpt_const (un d₂)) hpad) (cpt_const (un d₂))
  have hInit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool =>
        pairB (pairB (pairB (mulU (un d₁) (hd (unpairB s).1) ++ un d₁)
                            (mulU (un d₂) (hd (unpairB s).1) ++ un d₂)) (unpairB s).2)
              (pairB [] [])) :=
    cpt_pairB2 (cpt_pairB2 (cpt_pairB2 hclk₁ hclk₂) hx) (cpt_const (pairB [] []))
  have hPairIter : PvsNP.PolyTimeComputable PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun s : List Bool =>
        (pairB (pairB (pairB (mulU (un d₁) (hd (unpairB s).1) ++ un d₁)
                             (mulU (un d₂) (hd (unpairB s).1) ++ un d₂)) (unpairB s).2)
               (pairB [] []),
         true :: (unpairB s).2)) :=
    cpt_pair hInit (cpt_cons1 true hx)
  have hRun := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hPairIter hIter
  have hOut := cpt_unpairB2_1 (cpt_unpairB2_1 hRun)
  have hBoolS := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hOut cpt_neU
  have hBoolP := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpb hBoolS
  let h : List Bool × List Bool → Bool := fun q =>
    !((unpairB (unpairB ((mulStep c₁ c₂)^[q.2.length + 1]
        (pairB (pairB (pairB (mulU (un d₁) (hd q.1) ++ un d₁)
                             (mulU (un d₂) (hd q.1) ++ un d₂)) q.2)
               (pairB [] [])))).2).2).isEmpty
  have hHeq : (((fun l : List Bool => !l.isEmpty) ∘
        (fun s : List Bool => (unpairB (unpairB (((fun q : List Bool × List Bool => (mulStep c₁ c₂)^[q.2.length] q.1) ∘
          (fun s : List Bool =>
            (pairB (pairB (pairB (mulU (un d₁) (hd (unpairB s).1) ++ un d₁)
                                 (mulU (un d₂) (hd (unpairB s).1) ++ un d₂)) (unpairB s).2)
                   (pairB [] []),
             true :: (unpairB s).2))) s)).2).2)) ∘
      (fun q : List Bool × List Bool => pairB q.1 q.2)) = h := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB, List.length_cons, h]
  obtain ⟨j, M, hM⟩ := PvsNP.Units.m2_padded_test_exp k id id h cpt_id cpt_id (by rwa [hHeq] at hBoolP)
  refine ⟨j, _, M, fun x => ?_, hM⟩
  set T := 2 ^ (x.length ^ k) + k
  have hhd : hd (List.replicate T true ++ false :: x) = un T := hd_un T x
  have hclk1_eq : mulU (un d₁) (un T) ++ un d₁ = un (d₁ * T + d₁) := by
    simp only [mulU, un, List.length_replicate, ← List.replicate_add]
  have hclk2_eq : mulU (un d₂) (un T) ++ un d₂ = un (d₂ * T + d₂) := by
    simp only [mulU, un, List.length_replicate, ← List.replicate_add]
  have hiter_eq := iter_mulStep c₁ c₂ (un (d₁ * T + d₁)) (un (d₂ * T + d₂)) x (x.length + 1) 0 false
  simp only [zero_add, Bool.false_or, un_zero, Bool.false_eq_true, ↓reduceIte] at hiter_eq
  have hh_val : h (List.replicate T true ++ false :: x, x) =
      (List.range (x.length + 1)).any (fun j =>
        V (pairB (encCode c₁) (pairB (x.take j) (un (d₁ * T + d₁))), []) &&
        V (pairB (encCode c₂) (pairB (x.drop j) (un (d₂ * T + d₂))), [])) := by
    dsimp only [h]
    rw [hhd, hclk1_eq, hclk2_eq, hiter_eq, unpairB_pairB, unpairB_pairB]
    cases (List.range (x.length + 1)).any (fun j =>
        V (pairB (encCode c₁) (pairB (x.take j) (un (d₁ * T + d₁))), []) &&
        V (pairB (encCode c₂) (pairB (x.drop j) (un (d₂ * T + d₂))), [])) <;> rfl
  simp only [id_eq]
  rw [hh_val, List.any_eq_true, Language.mem_mul]
  have hk_pos : 1 ≤ k := by omega
  have hV1 : ∀ j, V (pairB (encCode c₁) (pairB (x.take j) (un (d₁ * T + d₁))), []) = f₁ (x.take j) := by
    intro j
    apply V_eq_f M₁ hc₁ (x.take j) T
    have hlen : (x.take j).length ≤ x.length := by simp
    exact (ht₁ _).trans ((lift_bound k₁ k₂ _).trans (mono_exp_bound k hk_pos hlen))
  have hV2 : ∀ j, V (pairB (encCode c₂) (pairB (x.drop j) (un (d₂ * T + d₂))), []) = f₂ (x.drop j) := by
    intro j
    apply V_eq_f M₂ hc₂ (x.drop j) T
    have hlen : (x.drop j).length ≤ x.length := by simp
    have hlift : 2 ^ ((x.drop j).length ^ k₂) + k₂ ≤ 2 ^ ((x.drop j).length ^ k) + k := by
      have := lift_bound k₂ k₁ (x.drop j).length
      have hcomm : k₂ + k₁ + 1 = k := by omega
      rwa [hcomm] at this
    exact (ht₂ _).trans (hlift.trans (mono_exp_bound k hk_pos hlen))
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a.length, List.mem_range.2 ?_, ?_⟩
    · have : a.length + b.length = x.length := by rw [← List.length_append, hab]
      omega
    · simp only [Bool.and_eq_true, hV1, hV2]
      exact ⟨by rw [← hab, List.take_left]; exact (hf₁ a).1 ha,
             by rw [← hab, List.drop_left]; exact (hf₂ b).1 hb⟩
  · rintro ⟨j, _, hv⟩
    simp only [Bool.and_eq_true, hV1, hV2] at hv
    exact ⟨x.take j, (hf₁ _).2 hv.1, x.drop j, (hf₂ _).2 hv.2, List.take_append_drop j x⟩

theorem main :
    ∀ m : ℕ, ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ^ m ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro m L hL
  induction m with
  | zero =>
    simpa only [pow_zero] using exp_one
  | succ m ih =>
    simpa only [pow_succ] using exp_mul (L ^ m) L ih hL

end PvsNP.Units.tc_exp_pow

theorem PvsNP.Units.tc_exp_pow :
    ∀ m : ℕ, ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ^ m ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_pow.main
