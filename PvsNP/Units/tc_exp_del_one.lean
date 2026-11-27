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

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_del_one

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

private def bigK (k₀ : ℕ) : ℕ := 2 ^ (2 ^ k₀) + 2 * k₀ + 4

private theorem bound_K (k₀ : ℕ) (n : ℕ) :
    2 ^ ((n + 1) ^ k₀) + k₀ ≤ 2 ^ (n ^ bigK k₀) + bigK k₀ := by
  have hK2k : 2 * k₀ ≤ bigK k₀ := by
    unfold bigK
    exact le_trans (Nat.le_add_left (2 * k₀) _) (Nat.le_add_right _ 4)
  have hkk : k₀ ≤ bigK k₀ := le_trans (by omega : k₀ ≤ 2 * k₀) hK2k
  have hKk : 2 ^ (2 ^ k₀) + k₀ ≤ bigK k₀ := by
    unfold bigK
    exact le_trans (Nat.add_le_add_left (by omega : k₀ ≤ 2 * k₀) _) (Nat.le_add_right _ 4)
  cases n with
  | zero =>
    have h1 : (0 + 1) ^ k₀ = 1 := one_pow k₀
    have h2 : 2 ^ 1 = 2 := rfl
    rw [h1, h2]
    have hstep : 2 + k₀ ≤ 2 * k₀ + 4 := by omega
    have hleK : 2 * k₀ + 4 ≤ bigK k₀ := by
      unfold bigK
      exact Nat.add_le_add_right (Nat.le_add_left _ _) 4
    exact le_trans (le_trans hstep hleK) (Nat.le_add_left _ _)
  | succ n' =>
    cases n' with
    | zero =>
      exact le_trans hKk (Nat.le_add_left _ _)
    | succ n'' =>
      have hn : n'' + 2 + 1 ≤ (n'' + 2) ^ 2 := by nlinarith
      have hp1 : (n'' + 2 + 1) ^ k₀ ≤ ((n'' + 2) ^ 2) ^ k₀ := Nat.pow_le_pow_left hn k₀
      have hp2 : ((n'' + 2) ^ 2) ^ k₀ = (n'' + 2) ^ (2 * k₀) := (Nat.pow_mul _ 2 k₀).symm
      have hp3 : (n'' + 2) ^ (2 * k₀) ≤ (n'' + 2) ^ bigK k₀ := Nat.pow_le_pow_right (by omega) hK2k
      have hexp : 2 ^ ((n'' + 2 + 1) ^ k₀) ≤ 2 ^ ((n'' + 2) ^ bigK k₀) :=
        Nat.pow_le_pow_right (by decide) (hp1.trans (hp2 ▸ hp3))
      exact Nat.add_le_add hexp hkk

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

-- State: pairB (pairB clk x) (pairB idx found)
private def rawDelStep (c : Code) (st : List Bool) : List Bool :=
  let imm := (unpairB st).1
  let clk := (unpairB imm).1
  let x := (unpairB imm).2
  let var := (unpairB st).2
  let idx := (unpairB var).1
  let found := (unpairB var).2
  let sp := idx.map (fun _ => true) ++ false :: x
  let u := (unpairB sp).1
  let v := (unpairB sp).2
  let hF := Vflag c (u ++ false :: v) clk
  let hT := Vflag c (u ++ true :: v) clk
  let hit := sel hF hT [true]
  let found' := sel found hit [true]
  pairB imm (pairB (true :: idx) found')

private def delStep (c : Code) (st : List Bool) : List Bool :=
  let ns := rawDelStep c st
  let bound := true :: true :: true :: st
  sel (ns.drop bound.length) ns st

private theorem delStep_length_le (c : Code) (st : List Bool) :
    (delStep c st).length ≤ st.length + 3 := by
  unfold delStep sel
  dsimp only
  split_ifs with h
  · have hle := List.drop_eq_nil_iff.1 h
    simp only [List.length_cons] at hle
    omega
  · omega

private theorem delStep_poly (c : Code) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (delStep c) := by
  have himm : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).1) := cpt_unpairB1
  have hclk : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).1).1) := cpt_unpairB1_1 himm
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).1).2) := cpt_unpairB2_1 himm
  have hvar : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).2) := cpt_unpairB2
  have hidx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).1) := cpt_unpairB1_1 hvar
  have hfound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).2) := cpt_unpairB2_1 hvar
  have hidx_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => (unpairB (unpairB st).2).1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hidx map_true_poly
  have hsp := cpt_app2 hidx_map (cpt_cons1 false hx)
  have hu := cpt_unpairB1_1 hsp
  have hv := cpt_unpairB2_1 hsp
  have hcandF := cpt_app2 hu (cpt_cons1 false hv)
  have hcandT := cpt_app2 hu (cpt_cons1 true hv)
  have hF := cpt_Vflag (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 hcandF hclk)) (cpt_const [])
  have hT := cpt_Vflag (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 hcandT hclk)) (cpt_const [])
  have hhit := cpt_sel hF hT (cpt_const [true])
  have hfound' := cpt_sel hfound hhit (cpt_const [true])
  have hnextIdx := cpt_cons1 true hidx
  have hraw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (rawDelStep c) :=
    cpt_pairB2 himm (cpt_pairB2 hnextIdx hfound')
  have hbound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => true :: true :: true :: st) :=
    cpt_cons1 true (cpt_cons1 true (cpt_cons1 true cpt_id))
  have hbound_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => true :: true :: true :: st)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hbound map_true_poly
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawDelStep c st)).2) :=
    cpt_unpairB2_1 (cpt_app2 hbound_map (cpt_cons1 false hraw))
  have hsel : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawDelStep c st)).2
          (rawDelStep c st) st) :=
    cpt_sel hdrop hraw cpt_id
  have heq : (fun st : List Bool =>
      sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawDelStep c st)).2
        (rawDelStep c st) st) = delStep c := by
    funext st
    simp only [delStep, unpairB_map_true]
  rwa [heq] at hsel

private theorem delStep_valid (c : Code) (clk x : List Bool) (i : ℕ) (b : Bool) :
    let imm := pairB clk x
    delStep c (pairB imm (pairB (un i) (if b then [true] else []))) =
      pairB imm (pairB (un (i + 1))
        (if (b || V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), [])
               || V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), []))
         then [true] else [])) := by
  intro imm
  have hraw : rawDelStep c (pairB imm (pairB (un i) (if b then [true] else []))) =
      pairB imm (pairB (un (i + 1))
        (if (b || V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), [])
               || V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), []))
         then [true] else [])) := by
    unfold rawDelStep
    simp only [unpairB_pairB, unpairB_map_true, un_length, Vflag]
    have himm1 : (unpairB imm).1 = clk := by simp [imm, unpairB_pairB]
    have himm2 : (unpairB imm).2 = x := by simp [imm, unpairB_pairB]
    rw [himm1, himm2]
    have hcons : true :: un i = un (i + 1) := by
      simp [un, List.replicate_succ]
    rw [hcons]
    congr 1; congr 1
    cases b <;>
      cases hVf : V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), []) <;>
      cases hVt : V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), []) <;>
      simp [sel]
  have hlen : (rawDelStep c (pairB imm (pairB (un i) (if b then [true] else [])))).length ≤
      (pairB imm (pairB (un i) (if b then [true] else []))).length + 3 := by
    rw [hraw]
    simp only [pairB_length, un_length]
    cases b <;>
      cases (V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), []) ||
             V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), [])) <;>
      cases V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), []) <;>
      cases V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), []) <;>
      simp <;> omega
  unfold delStep
  dsimp only
  have hnil : (rawDelStep c (pairB imm (pairB (un i) (if b then [true] else [])))).drop
      (true :: true :: true :: pairB imm (pairB (un i) (if b then [true] else []))).length = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_cons]
    omega
  rw [hnil]
  simp only [sel, ↓reduceIte]
  exact hraw

private theorem iter_delStep (c : Code) (clk x : List Bool) :
    ∀ (t i : ℕ) (b : Bool),
      let imm := pairB clk x
      (delStep c)^[t] (pairB imm (pairB (un i) (if b then [true] else []))) =
        pairB imm (pairB (un (i + t))
          (if (b || (List.range t).any (fun r =>
              V (pairB (encCode c) (pairB (x.take (i + r) ++ false :: x.drop (i + r)) clk), []) ||
              V (pairB (encCode c) (pairB (x.take (i + r) ++ true :: x.drop (i + r)) clk), [])))
           then [true] else [])) := by
  intro t
  induction t with
  | zero => intro i b; simp
  | succ t ih =>
    intro i b
    dsimp only
    rw [Function.iterate_succ_apply, delStep_valid, ih (i + 1)]
    have hadd : i + 1 + t = i + (t + 1) := by omega
    rw [hadd]
    congr 1; congr 1
    have heq : (b || V (pairB (encCode c) (pairB (x.take i ++ false :: x.drop i) clk), [])
                 || V (pairB (encCode c) (pairB (x.take i ++ true :: x.drop i) clk), []) ||
        (List.range t).any (fun r =>
          V (pairB (encCode c) (pairB (x.take (i + 1 + r) ++ false :: x.drop (i + 1 + r)) clk), []) ||
          V (pairB (encCode c) (pairB (x.take (i + 1 + r) ++ true :: x.drop (i + 1 + r)) clk), []))) =
      (b || (List.range (t + 1)).any (fun r =>
          V (pairB (encCode c) (pairB (x.take (i + r) ++ false :: x.drop (i + r)) clk), []) ||
          V (pairB (encCode c) (pairB (x.take (i + r) ++ true :: x.drop (i + r)) clk), []))) := by
      cases b with
      | true => simp
      | false =>
        simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
        constructor
        · rintro ((hF | hT) | ⟨r, hr, hFT⟩)
          · exact ⟨0, by omega, Or.inl (by simpa using hF)⟩
          · exact ⟨0, by omega, Or.inr (by simpa using hT)⟩
          · refine ⟨r + 1, by omega, ?_⟩
            have ha : i + (r + 1) = i + 1 + r := by omega
            rw [ha]
            exact hFT
        · rintro ⟨r, hr, hFT⟩
          cases r with
          | zero =>
            simp only [Nat.add_zero] at hFT
            exact Or.inl hFT
          | succ r' =>
            right
            refine ⟨r', by omega, ?_⟩
            have ha : i + 1 + r' = i + (r' + 1) := by omega
            rw [ha]
            exact hFT
    rw [heq]

theorem main :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k₀, f, M, hf, ht⟩
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  let K := bigK k₀
  obtain ⟨cStep⟩ := delStep_poly c
  have hIter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun q : List Bool × List Bool => (delStep c)^[q.2.length] q.1) :=
    Iter.iter_polyTime (delStep c) cStep 3 (delStep_length_le c)
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => pairB q.1 q.2) := by
    rw [← encodePair_eq]; exact cpt_pairB
  have hpad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => hd (unpairB s).1) := cpt_hd1 cpt_unpairB1
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).2) := cpt_unpairB2
  have hclk : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => mulU (un d) (hd (unpairB s).1) ++ un d) :=
    cpt_app2 (cpt_mulU2 (cpt_const (un d)) hpad) (cpt_const (un d))
  have hInit := cpt_pairB2 (cpt_pairB2 hclk hx) (cpt_const (pairB [] []))
  have hCnt := cpt_cons1 true hx
  have hPairIter := cpt_pair hInit hCnt
  have hRun := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hPairIter hIter
  have hOut := cpt_unpairB2_1 (cpt_unpairB2_1 hRun)
  have hBoolS := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hOut cpt_neU
  have hBoolP := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpb hBoolS
  let h : List Bool × List Bool → Bool := fun q =>
    !((unpairB (unpairB ((delStep c)^[(true :: q.2).length]
        (pairB (pairB (mulU (un d) (hd q.1) ++ un d) q.2) (pairB [] [])))).2).2).isEmpty
  have hHeq : (((fun l : List Bool => !l.isEmpty) ∘
        (fun s : List Bool => (unpairB (unpairB (((fun q : List Bool × List Bool => (delStep c)^[q.2.length] q.1) ∘
          (fun s : List Bool =>
            (pairB (pairB (mulU (un d) (hd (unpairB s).1) ++ un d) (unpairB s).2) (pairB [] []),
             true :: (unpairB s).2))) s)).2).2)) ∘
      (fun q : List Bool × List Bool => pairB q.1 q.2)) = h := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB, h]
  obtain ⟨j, Mdel, hMdel⟩ :=
    PvsNP.Units.m2_padded_test_exp K id id h cpt_id cpt_id (by rwa [hHeq] at hBoolP)
  refine ⟨j, _, Mdel, fun x => ?_, hMdel⟩
  simp only [id_eq]
  set T := 2 ^ (x.length ^ K) + K
  have hhd : hd (List.replicate T true ++ false :: x) = un T := hd_un T x
  have hclk_eq : mulU (un d) (un T) ++ un d = un (d * T + d) := by
    simp only [mulU, un, List.length_replicate, ← List.replicate_add]
  have hiter := iter_delStep c (un (d * T + d)) x (x.length + 1) 0 false
  simp only [Nat.zero_add, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hiter
  have hh_val : h (List.replicate T true ++ false :: x, x) =
      (List.range (x.length + 1)).any (fun r =>
        V (pairB (encCode c) (pairB (x.take r ++ false :: x.drop r) (un (d * T + d))), []) ||
        V (pairB (encCode c) (pairB (x.take r ++ true :: x.drop r) (un (d * T + d))), [])) := by
    dsimp only [h]
    have hlen1 : (true :: x).length = x.length + 1 := rfl
    have hpair0 : pairB ([] : List Bool) [] = pairB (un 0) [] := rfl
    rw [hhd, hclk_eq, hlen1, hpair0, hiter, unpairB_pairB, unpairB_pairB]
    cases (List.range (x.length + 1)).any (fun r =>
        V (pairB (encCode c) (pairB (x.take r ++ false :: x.drop r) (un (d * T + d))), []) ||
        V (pairB (encCode c) (pairB (x.take r ++ true :: x.drop r) (un (d * T + d))), [])) <;> rfl
  rw [hh_val, List.any_eq_true]
  have hV_ok : ∀ (r : ℕ) (b : Bool), r ≤ x.length →
      V (pairB (encCode c) (pairB (x.take r ++ b :: x.drop r) (un (d * T + d))), []) =
        f (x.take r ++ b :: x.drop r) := by
    intro r b hr
    apply V_eq_f M hc (x.take r ++ b :: x.drop r) T
    have hlen : (x.take r ++ b :: x.drop r).length = x.length + 1 := by
      simp [List.length_take, List.length_drop]
      omega
    rw [hlen]
    exact (ht (x.length + 1)).trans (bound_K k₀ x.length)
  constructor
  · rintro ⟨u, v, b, hxuv, hmem⟩
    have hulen : u.length ≤ x.length := by
      rw [hxuv]; simp
    have htake : x.take u.length = u := by
      rw [hxuv]; simp
    have hdrop : x.drop u.length = v := by
      rw [hxuv]; simp
    refine ⟨u.length, List.mem_range.2 (by omega), ?_⟩
    rw [Bool.or_eq_true, hV_ok u.length false hulen, hV_ok u.length true hulen, htake, hdrop]
    cases b with
    | false => exact Or.inl ((hf _).1 hmem)
    | true => exact Or.inr ((hf _).1 hmem)
  · rintro ⟨r, hr, hor⟩
    have hrle : r ≤ x.length := by
      rw [List.mem_range] at hr; omega
    rw [Bool.or_eq_true, hV_ok r false hrle, hV_ok r true hrle] at hor
    rcases hor with hF | hT
    · exact ⟨x.take r, x.drop r, false, (List.take_append_drop r x).symm, (hf _).2 hF⟩
    · exact ⟨x.take r, x.drop r, true, (List.take_append_drop r x).symm, (hf _).2 hT⟩

end PvsNP.Units.tc_exp_del_one

theorem PvsNP.Units.tc_exp_del_one :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_del_one.main
