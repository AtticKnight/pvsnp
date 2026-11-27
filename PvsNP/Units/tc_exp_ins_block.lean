import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_padded_test_exp

/-
Built on the settled units PvsNP.Units.fr_ladner, m2_transducer_polytime, m2_polytime_comp, and
m2_padded_test_exp of github.com/makedotfun/pvsnp (Apache License 2.0), adapting the bounded
universal-simulation search structure of PvsNP.Units.tc_exp_del_one to inserting [true, false].
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_ins_block

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

private def rawStep (c : Code) (st : List Bool) : List Bool :=
  let imm := (unpairB st).1
  let clk := (unpairB imm).1
  let x := (unpairB imm).2
  let var := (unpairB st).2
  let idx := (unpairB var).1
  let found := (unpairB var).2
  let sp := idx.map (fun _ => true) ++ false :: x
  let u := (unpairB sp).1
  let r := (unpairB sp).2
  let r1 := r.tail
  let v := r1.tail
  let candOk := Vflag c (u ++ v) clk
  let hit := sel r [] (sel (hd r) [] (sel r1 [] (sel (hd r1) candOk [])))
  let found' := sel found hit [true]
  pairB imm (pairB (true :: idx) found')

private def stepFn (c : Code) (st : List Bool) : List Bool :=
  let ns := rawStep c st
  let bound := true :: true :: true :: st
  sel (ns.drop bound.length) ns st

private theorem stepFn_length_le (c : Code) (st : List Bool) :
    (stepFn c st).length ≤ st.length + 3 := by
  unfold stepFn sel
  dsimp only
  split_ifs with h
  · have hle := List.drop_eq_nil_iff.1 h
    simp only [List.length_cons] at hle
    omega
  · omega

private theorem stepFn_poly (c : Code) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (stepFn c) := by
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
  have hr := cpt_unpairB2_1 hsp
  have hr1 := cpt_comp hr cpt_tail
  have hv := cpt_comp hr1 cpt_tail
  have hhdr := cpt_hd1 hr
  have hhdr1 := cpt_hd1 hr1
  have hcand := cpt_app2 hu hv
  have hcandOk := cpt_Vflag (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 hcand hclk)) (cpt_const [])
  have hhit := cpt_sel hr (cpt_const [])
    (cpt_sel hhdr (cpt_const []) (cpt_sel hr1 (cpt_const []) (cpt_sel hhdr1 hcandOk (cpt_const []))))
  have hfound' := cpt_sel hfound hhit (cpt_const [true])
  have hnextIdx := cpt_cons1 true hidx
  have hraw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (rawStep c) :=
    cpt_pairB2 himm (cpt_pairB2 hnextIdx hfound')
  have hbound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => true :: true :: true :: st) :=
    cpt_cons1 true (cpt_cons1 true (cpt_cons1 true cpt_id))
  have hbound_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => true :: true :: true :: st)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hbound map_true_poly
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep c st)).2) :=
    cpt_unpairB2_1 (cpt_app2 hbound_map (cpt_cons1 false hraw))
  have hsel : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep c st)).2
          (rawStep c st) st) :=
    cpt_sel hdrop hraw cpt_id
  have heq : (fun st : List Bool =>
      sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep c st)).2
        (rawStep c st) st) = stepFn c := by
    funext st
    simp only [stepFn, unpairB_map_true]
  rwa [heq] at hsel

private def hitAt (c : Code) (clk x : List Bool) (i : ℕ) : Bool :=
  match x.drop i with
  | true :: false :: v => V (pairB (encCode c) (pairB (x.take i ++ v) clk), [])
  | _ => false

private theorem sel_nil (b c : List Bool) : sel [] b c = b := by
  simp only [sel, ↓reduceIte]

private theorem sel_cons (a : Bool) (r b c : List Bool) : sel (a :: r) b c = c := by
  simp only [sel, List.cons_ne_nil, ↓reduceIte]

private theorem bool_sel_eq (b vb : Bool) :
    sel (if b then [true] else []) (if vb then [true] else []) [true] =
      if (b || vb) then [true] else [] := by
  cases b <;> cases vb <;>
    simp only [sel_nil, sel_cons, Bool.true_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem hd_false (s : List Bool) : hd (false :: s) = [] := by
  simp only [hd, List.takeWhile_cons, id_eq, Bool.false_eq_true, ↓reduceIte]

private theorem hd_true (s : List Bool) : hd (true :: s) = true :: List.takeWhile id s := by
  simp only [hd, List.takeWhile_cons, id_eq, ↓reduceIte]

private theorem hitExpr_eq (r w : List Bool) :
    sel r [] (sel (hd r) [] (sel r.tail [] (sel (hd r.tail) w []))) =
      match r with | true :: false :: _ => w | _ => [] := by
  cases r with
  | nil => simp only [sel_nil]
  | cons a rest =>
    cases a with
    | false => simp only [sel_cons, hd_false, sel_nil]
    | true =>
      cases rest with
      | nil => simp only [sel_cons, hd_true, List.tail_cons, sel_nil]
      | cons a2 v =>
        cases a2 with
        | true => simp only [sel_cons, hd_true, List.tail_cons]
        | false => simp only [sel_cons, hd_true, List.tail_cons, hd_false, sel_nil]

private theorem stepFn_valid (c : Code) (clk x : List Bool) (i : ℕ) (b : Bool) :
    let imm := pairB clk x
    stepFn c (pairB imm (pairB (un i) (if b then [true] else []))) =
      pairB imm (pairB (un (i + 1)) (if (b || hitAt c clk x i) then [true] else [])) := by
  intro imm
  have hraw : rawStep c (pairB imm (pairB (un i) (if b then [true] else []))) =
      pairB imm (pairB (un (i + 1)) (if (b || hitAt c clk x i) then [true] else [])) := by
    unfold rawStep hitAt
    simp only [unpairB_pairB, unpairB_map_true, un_length]
    have himm1 : (unpairB imm).1 = clk := by simp only [imm, unpairB_pairB]
    have himm2 : (unpairB imm).2 = x := by simp only [imm, unpairB_pairB]
    rw [himm1, himm2]
    have hcons : true :: un i = un (i + 1) := by
      simp only [un, List.replicate_succ]
    rw [hcons]
    congr 1; congr 1
    rw [hitExpr_eq]
    cases hdrop : x.drop i with
    | nil =>
      cases b <;> simp only [sel_nil, sel_cons, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    | cons a rest =>
      cases a with
      | false =>
        cases b <;> simp only [sel_nil, sel_cons, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      | true =>
        cases rest with
        | nil =>
          cases b <;> simp only [sel_nil, sel_cons, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        | cons a2 v =>
          cases a2 with
          | true =>
            cases b <;> simp only [sel_nil, sel_cons, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
          | false =>
            dsimp only [List.tail_cons, Vflag]
            exact bool_sel_eq b (V (pairB (encCode c) (pairB (x.take i ++ v) clk), []))
  have hblen : ∀ z : Bool, (if z then [true] else ([] : List Bool)).length ≤ 1 := fun z => by
    cases z <;> decide
  have hlen : (rawStep c (pairB imm (pairB (un i) (if b then [true] else [])))).length ≤
      (pairB imm (pairB (un i) (if b then [true] else []))).length + 3 := by
    rw [hraw]
    simp only [pairB_length, un_length]
    have hb1 := hblen b
    have hb2 := hblen (b || hitAt c clk x i)
    omega
  unfold stepFn
  dsimp only
  have hnil : (rawStep c (pairB imm (pairB (un i) (if b then [true] else [])))).drop
      (true :: true :: true :: pairB imm (pairB (un i) (if b then [true] else []))).length = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_cons]
    omega
  rw [hnil]
  simp only [sel_nil]
  exact hraw

private theorem iter_stepFn (c : Code) (clk x : List Bool) :
    ∀ (t i : ℕ) (b : Bool),
      let imm := pairB clk x
      (stepFn c)^[t] (pairB imm (pairB (un i) (if b then [true] else []))) =
        pairB imm (pairB (un (i + t))
          (if (b || (List.range t).any (fun r => hitAt c clk x (i + r))) then [true] else [])) := by
  intro t
  induction t with
  | zero => intro i b; simp only [Function.iterate_zero, id_eq, Nat.add_zero, List.range_zero, List.any_nil, Bool.or_false]
  | succ t ih =>
    intro i b
    dsimp only
    rw [Function.iterate_succ_apply, stepFn_valid, ih (i + 1)]
    have hadd : i + 1 + t = i + (t + 1) := by omega
    rw [hadd]
    congr 1; congr 1
    have heq : (b || hitAt c clk x i ||
        (List.range t).any (fun r => hitAt c clk x (i + 1 + r))) =
      (b || (List.range (t + 1)).any (fun r => hitAt c clk x (i + r))) := by
      cases b with
      | true => simp only [Bool.true_or]
      | false =>
        simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
        constructor
        · rintro (h0 | ⟨r, hr, hr'⟩)
          · exact ⟨0, by omega, by simpa only [Nat.add_zero] using h0⟩
          · refine ⟨r + 1, by omega, ?_⟩
            have ha : i + (r + 1) = i + 1 + r := by omega
            rwa [ha]
        · rintro ⟨r, hr, hr'⟩
          cases r with
          | zero => exact Or.inl (by simpa only [Nat.add_zero] using hr')
          | succ r' =>
            refine Or.inr ⟨r', by omega, ?_⟩
            have ha : i + 1 + r' = i + (r' + 1) := by omega
            rwa [ha]
    rw [heq]

theorem main :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k₀, f, M, hf, ht⟩
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  obtain ⟨cStep⟩ := stepFn_poly c
  have hIter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun q : List Bool × List Bool => (stepFn c)^[q.2.length] q.1) :=
    Iter.iter_polyTime (stepFn c) cStep 3 (stepFn_length_le c)
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
    !((unpairB (unpairB ((stepFn c)^[(true :: q.2).length]
        (pairB (pairB (mulU (un d) (hd q.1) ++ un d) q.2) (pairB [] [])))).2).2).isEmpty
  have hHeq : (((fun l : List Bool => !l.isEmpty) ∘
        (fun s : List Bool => (unpairB (unpairB (((fun q : List Bool × List Bool => (stepFn c)^[q.2.length] q.1) ∘
          (fun s : List Bool =>
            (pairB (pairB (mulU (un d) (hd (unpairB s).1) ++ un d) (unpairB s).2) (pairB [] []),
             true :: (unpairB s).2))) s)).2).2)) ∘
      (fun q : List Bool × List Bool => pairB q.1 q.2)) = h := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB, h]
  obtain ⟨j, Mins, hMins⟩ :=
    PvsNP.Units.m2_padded_test_exp k₀ id id h cpt_id cpt_id (by rwa [hHeq] at hBoolP)
  refine ⟨j, _, Mins, fun x => ?_, hMins⟩
  simp only [id_eq]
  set T := 2 ^ (x.length ^ k₀) + k₀
  have hhd : hd (List.replicate T true ++ false :: x) = un T := hd_un T x
  have hclk_eq : mulU (un d) (un T) ++ un d = un (d * T + d) := by
    simp only [mulU, un, List.length_replicate, ← List.replicate_add]
  have hiter := iter_stepFn c (un (d * T + d)) x (x.length + 1) 0 false
  simp only [Nat.zero_add, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hiter
  have hh_val : h (List.replicate T true ++ false :: x, x) =
      (List.range (x.length + 1)).any (fun r => hitAt c (un (d * T + d)) x r) := by
    dsimp only [h]
    have hlen1 : (true :: x).length = x.length + 1 := rfl
    have hpair0 : pairB ([] : List Bool) [] = pairB (un 0) [] := rfl
    rw [hhd, hclk_eq, hlen1, hpair0, hiter, unpairB_pairB, unpairB_pairB]
    cases (List.range (x.length + 1)).any (fun r => hitAt c (un (d * T + d)) x r) <;> rfl
  rw [hh_val, List.any_eq_true]
  have hV_ok : ∀ (y : List Bool), y.length ≤ x.length →
      V (pairB (encCode c) (pairB y (un (d * T + d))), []) = f y := by
    intro y hy
    apply V_eq_f M hc y T
    refine (ht y.length).trans ?_
    cases k₀ with
    | zero => simp [T]
    | succ k' =>
      have hp1 : y.length ^ (k' + 1) ≤ x.length ^ (k' + 1) := Nat.pow_le_pow_left hy _
      have hp2 : 2 ^ (y.length ^ (k' + 1)) ≤ 2 ^ (x.length ^ (k' + 1)) :=
        Nat.pow_le_pow_right (by decide) hp1
      exact Nat.add_le_add_right hp2 _
  constructor
  · rintro ⟨u, v, hxuv, hmem⟩
    have hulen : u.length < x.length + 1 := by
      rw [hxuv]; simp
    have hdrop : x.drop u.length = true :: false :: v := by
      rw [hxuv]; simp
    have htake : x.take u.length = u := by
      rw [hxuv]; simp
    refine ⟨u.length, List.mem_range.2 hulen, ?_⟩
    unfold hitAt
    rw [hdrop]
    dsimp only
    rw [htake, hV_ok (u ++ v) (by rw [hxuv]; simp; omega)]
    exact (hf _).1 hmem
  · rintro ⟨r, hr, hhit⟩
    have hrle : r ≤ x.length := by
      rw [List.mem_range] at hr; omega
    unfold hitAt at hhit
    cases hdrop : x.drop r with
    | nil => rw [hdrop] at hhit; contradiction
    | cons a rest =>
      rw [hdrop] at hhit
      cases a with
      | false => contradiction
      | true =>
        cases rest with
        | nil => contradiction
        | cons a2 v =>
          cases a2 with
          | true => contradiction
          | false =>
            dsimp only at hhit
            have hlen_le : (x.take r ++ v).length ≤ x.length := by
              have hdlen : (x.drop r).length = v.length + 2 := by rw [hdrop]; simp
              simp only [List.length_append, List.length_take, List.length_drop] at hdlen ⊢
              omega
            rw [hV_ok _ hlen_le] at hhit
            have hsplit : x = x.take r ++ [true, false] ++ v := by
              have htd := (List.take_append_drop r x).symm
              rw [hdrop] at htd
              simpa [List.append_assoc] using htd
            exact ⟨x.take r, v, hsplit, (hf _).2 hhit⟩

end PvsNP.Units.tc_exp_ins_block

theorem PvsNP.Units.tc_exp_ins_block :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_ins_block.main
