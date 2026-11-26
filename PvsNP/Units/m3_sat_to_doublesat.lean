import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_sat_to_doublesat_aux

open CookLevin CookLevin.Lang EvalCnfCmd CnfWellFormed

/-- Appended tautology clause `[(true, n), (false, n)]` as raw bits. -/
def padClause (n : Nat) : List Bool :=
  [true, true] ++ List.replicate n true ++ [false, true, false] ++ List.replicate n true ++ [false, false]

/-- Reduction map from `SATStr` to `DoubleSAT`: append `(x_n ∨ ¬x_n)` with fresh `n = |x|`
when `x` is a well-formed CNF encoding, and map malformed strings to `[false]` (`botCnf`). -/
def doubleSatMap (x : List Bool) : List Bool :=
  if wfCnfB (strBits x) then
    x ++ padClause x.length
  else
    [false]

lemma strBits_append (a b : List Bool) : strBits (a ++ b) = strBits a ++ strBits b := by
  simp [strBits]

lemma strBits_replicate_true (n : Nat) : strBits (List.replicate n true) = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [strBits, List.replicate_succ] at ih ⊢

lemma strBits_padClause (n : Nat) :
    strBits (padClause n) = encodeClause [(true, n), (false, n)] := by
  simp [padClause, strBits_append, strBits_replicate_true, strBits, encodeClause, encodeLit,
    List.append_assoc]

lemma encodeCnf_append (N₁ N₂ : cnf) : encodeCnf (N₁ ++ N₂) = encodeCnf N₁ ++ encodeCnf N₂ := by
  induction N₁ with
  | nil => rfl
  | cons C N ih =>
      simp only [List.cons_append, CnfSerialize.encodeCnf_cons, ih, List.append_assoc]

lemma var_lt_encodeLit_length (l : literal) : l.2 < (encodeLit l).length := by
  rcases l with ⟨pol, v⟩
  simp only [encodeLit, List.length_cons, List.length_append, List.length_replicate, List.length_singleton]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self v) (Nat.le_add_right (v + 1) 2)

lemma var_lt_clauseBody_length {C : clause} {l : literal} (hl : l ∈ C) :
    l.2 < (CnfSerialize.clauseBody C).length := by
  induction C with
  | nil => cases hl
  | cons hd tl ih =>
      rw [CnfSerialize.clauseBody_cons, List.length_append]
      rcases List.mem_cons.mp hl with rfl | htl
      · exact Nat.lt_of_lt_of_le (var_lt_encodeLit_length l) (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (ih htl) (Nat.le_add_left _ _)

lemma var_lt_encodeCnf_length {N : cnf} {C : clause} {l : literal} (hC : C ∈ N) (hl : l ∈ C) :
    l.2 < (encodeCnf N).length := by
  induction N with
  | nil => cases hC
  | cons hd tl ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append]
      rcases List.mem_cons.mp hC with rfl | htl
      · rw [CnfSerialize.encodeClause_eq, List.length_append]
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (var_lt_clauseBody_length hl) (Nat.le_add_right _ _))
          (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (ih htl) (Nat.le_add_left _ _)

lemma evalClause_congr_vars {C : clause} {a b : assgn}
    (h : ∀ l ∈ C, evalVar a l.2 = evalVar b l.2) :
    evalClause a C = evalClause b C := by
  induction C with
  | nil => rfl
  | cons l tl ih =>
      simp only [evalClause, List.any_cons]
      have hl : evalLiteral a l = evalLiteral b l := by
        rcases l with ⟨pol, v⟩
        simp only [evalLiteral, h (pol, v) (List.mem_cons_self ..)]
      have htl : evalClause a tl = evalClause b tl :=
        ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
      simp only [evalClause] at htl
      rw [hl, htl]

lemma evalCnf_congr_vars {N : cnf} {a b : assgn}
    (h : ∀ C ∈ N, ∀ l ∈ C, evalVar a l.2 = evalVar b l.2) :
    evalCnf a N = evalCnf b N := by
  induction N with
  | nil => rfl
  | cons C rest ih =>
      simp only [evalCnf, List.all_cons]
      have hC := evalClause_congr_vars (fun l hl => h C (List.mem_cons_self ..) l hl)
      have hrest : evalCnf a rest = evalCnf b rest :=
        ih (fun C' hC' l hl => h C' (List.mem_cons_of_mem C hC') l hl)
      simp only [evalCnf] at hrest
      rw [hC, hrest]

lemma doubleSatMap_iff (x : List Bool) :
    SATStr x ↔
      ∃ a b : assgn,
        satisfiesCnf a (SATStr.cnfOf (doubleSatMap x)) ∧
        satisfiesCnf b (SATStr.cnfOf (doubleSatMap x)) ∧
        ∃ C ∈ SATStr.cnfOf (doubleSatMap x), ∃ l ∈ C, evalVar a l.2 ≠ evalVar b l.2 := by
  by_cases hwf : wfCnfB (strBits x) = true
  · have hmap : doubleSatMap x = x ++ padClause x.length := by simp [doubleSatMap, hwf]
    set N := SATStr.cnfOf x with hN_def
    have hstrN : encodeCnf N = strBits x := encodeCnf_parseTotal _ (strBits_bit x) hwf
    have hcnf : SATStr.cnfOf (doubleSatMap x) = N ++ [[(true, x.length), (false, x.length)]] := by
      show parseTotal (strBits (doubleSatMap x)) = _
      rw [hmap, strBits_append, ← hstrN, strBits_padClause]
      have h1 : encodeCnf N ++ encodeClause [(true, x.length), (false, x.length)] =
          encodeCnf (N ++ [[(true, x.length), (false, x.length)]]) := by
        rw [encodeCnf_append]
        simp [encodeCnf]
      rw [h1, parseTotal_encodeCnf]
    rw [hcnf]
    constructor
    · intro hsat
      obtain ⟨a, ha⟩ := hsat
      let n := x.length
      let a₀ : assgn := a.filter (fun v => decide (v ≠ n))
      let a₁ : assgn := n :: a₀
      have hne_N : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ n := by
        intro C hC l hl
        have hlt := var_lt_encodeCnf_length hC hl
        rw [hstrN, strBits_length] at hlt
        exact Nat.ne_of_lt hlt
      have ha0_eq : ∀ C ∈ N, ∀ l ∈ C, evalVar a₀ l.2 = evalVar a l.2 := by
        intro C hC l hl
        have hne := hne_N C hC l hl
        simp [evalVar, a₀, List.mem_filter, hne]
      have ha1_eq : ∀ C ∈ N, ∀ l ∈ C, evalVar a₁ l.2 = evalVar a l.2 := by
        intro C hC l hl
        have hne := hne_N C hC l hl
        simp [evalVar, a₁, a₀, List.mem_filter, hne]
      have ha0_N : satisfiesCnf a₀ N := by
        show evalCnf a₀ N = true
        rw [evalCnf_congr_vars ha0_eq]
        exact ha
      have ha1_N : satisfiesCnf a₁ N := by
        show evalCnf a₁ N = true
        rw [evalCnf_congr_vars ha1_eq]
        exact ha
      have ha0_n : evalVar a₀ n = false := by
        simp [evalVar, a₀, List.mem_filter]
      have ha1_n : evalVar a₁ n = true := by
        simp [evalVar, a₁]
      have ha0_pad : satisfiesCnf a₀ [[(true, n), (false, n)]] := by
        simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, ha0_n]
      have ha1_pad : satisfiesCnf a₁ [[(true, n), (false, n)]] := by
        simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, ha1_n]
      refine ⟨a₀, a₁, (evalCnf_app_iff a₀ N _).mpr ⟨ha0_N, ha0_pad⟩,
        (evalCnf_app_iff a₁ N _).mpr ⟨ha1_N, ha1_pad⟩,
        [(true, n), (false, n)], List.mem_append_right N (List.mem_singleton_self _),
        (true, n), List.mem_cons_self .., ?_⟩
      simp [ha0_n, ha1_n]
    · rintro ⟨a, _, ha, _, _⟩
      exact ⟨a, ((evalCnf_app_iff a N _).mp ha).1⟩
  · have hwfF : wfCnfB (strBits x) = false := Bool.eq_false_iff.mpr hwf
    have hmap : doubleSatMap x = [false] := by simp [doubleSatMap, hwfF]
    have hbotX : SATStr.cnfOf x = botCnf := parseTotal_of_not_wf _ hwfF
    have hbotF : SATStr.cnfOf [false] = botCnf := rfl
    constructor
    · intro hsat
      exact absurd (hbotX ▸ hsat) not_sat_botCnf
    · rintro ⟨a, _, ha, _, _⟩
      rw [hmap, hbotF] at ha
      exact absurd ⟨a, ha⟩ not_sat_botCnf

/-- Loop appending `|WCUR|` ones onto register `0`. -/
def appendOnesCmd : Cmd :=
  Cmd.forBnd SATStr.WIDX SATStr.WCUR (Cmd.op (.appendOne 0))

/-- Well-formed branch: append `strBits (padClause x.length)` onto register `0`. -/
def goodBranch : Cmd :=
  Cmd.op (.copy SATStr.WCUR 0) ;;
  Cmd.op (.appendOne 0) ;;
  Cmd.op (.appendOne 0) ;;
  appendOnesCmd ;;
  Cmd.op (.appendZero 0) ;;
  Cmd.op (.appendOne 0) ;;
  Cmd.op (.appendZero 0) ;;
  appendOnesCmd ;;
  Cmd.op (.appendZero 0) ;;
  Cmd.op (.appendZero 0)

/-- Malformed branch: replace register `0` with `[0]` (`strBits [false]`). -/
def badBranch : Cmd :=
  Cmd.op (.clear 0) ;;
  Cmd.op (.appendZero 0)

/-- Register-language program computing `doubleSatMap` in register `0` from `certState x`. -/
def doubleSatCmd : Cmd :=
  Cmd.op (.copy SATStr.WCUR 0) ;;
  Cmd.op (.clear SATStr.WSA) ;;
  Cmd.op (.clear SATStr.WSB) ;;
  Cmd.op (.clear SATStr.WTAL) ;;
  Cmd.forBnd SATStr.WIDX SATStr.WCUR SATStr.scanBody ;;
  Cmd.op (.nonEmpty SATStr.WHD SATStr.WSA) ;;
  Cmd.ifBit SATStr.WHD
    badBranch
    (Cmd.op (.nonEmpty SATStr.WHD SATStr.WSB) ;;
     Cmd.ifBit SATStr.WHD badBranch goodBranch)

lemma appendOnesCmd_run (s : State) :
    State.get (appendOnesCmd.eval s) 0 =
      State.get s 0 ++ List.replicate (State.get s SATStr.WCUR).length 1 ∧
    State.get (appendOnesCmd.eval s) SATStr.WCUR = State.get s SATStr.WCUR := by
  rw [appendOnesCmd, Cmd.eval_forBnd]
  have key := Cmd.foldlState_range_induct (Cmd.op (.appendOne 0)) SATStr.WIDX
    (State.get s SATStr.WCUR).length s
    (fun i st =>
      State.get st 0 = State.get s 0 ++ List.replicate i 1 ∧
      State.get st SATStr.WCUR = State.get s SATStr.WCUR)
    ⟨by simp, rfl⟩
    (by
      rintro i st _ ⟨h0, hcur⟩
      simp only [Cmd.eval_op, Op.eval]
      constructor
      · rw [State.get_set_eq, State.get_set_ne _ SATStr.WIDX _ 0 (by decide), h0,
          List.append_assoc, List.replicate_succ']
      · rw [State.get_set_ne _ 0 _ SATStr.WCUR (by decide),
          State.get_set_ne _ SATStr.WIDX _ SATStr.WCUR (by decide), hcur])
  exact key

lemma badBranch_get0 (s : State) : State.get (badBranch.eval s) 0 = [0] := by
  simp [badBranch, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]

lemma goodBranch_get0 (s : State) (l : List Nat) (h0 : State.get s 0 = l) :
    State.get (goodBranch.eval s) 0 =
      l ++ [1, 1] ++ List.replicate l.length 1 ++ [0, 1, 0] ++ List.replicate l.length 1 ++ [0, 0] := by
  unfold goodBranch
  simp only [Cmd.eval_seq]
  set s1 := (Cmd.op (.copy SATStr.WCUR 0)).eval s
  have hs1_0 : State.get s1 0 = l := by
    simp only [s1, Cmd.eval_op, Op.eval, State.get_set_ne _ SATStr.WCUR _ 0 (by decide), h0]
  have hs1_cur : State.get s1 SATStr.WCUR = l := by
    simp only [s1, Cmd.eval_op, Op.eval, State.get_set_eq, h0]
  set s2 := (Cmd.op (.appendOne 0)).eval ((Cmd.op (.appendOne 0)).eval s1)
  have hs2_0 : State.get s2 0 = l ++ [1, 1] := by
    simp [s2, Cmd.eval_op, Op.eval, State.get_set_eq, hs1_0, List.append_assoc]
  have hs2_cur : State.get s2 SATStr.WCUR = l := by
    simp [s2, Cmd.eval_op, Op.eval, State.get_set_ne _ 0 _ SATStr.WCUR (by decide), hs1_cur]
  set s3 := appendOnesCmd.eval s2
  have hs3 := appendOnesCmd_run s2
  have hs3_0 : State.get s3 0 = l ++ [1, 1] ++ List.replicate l.length 1 := by
    rw [show s3 = appendOnesCmd.eval s2 from rfl, hs3.1, hs2_0, hs2_cur]
  have hs3_cur : State.get s3 SATStr.WCUR = l := by
    rw [show s3 = appendOnesCmd.eval s2 from rfl, hs3.2, hs2_cur]
  set s4 := (Cmd.op (.appendZero 0)).eval
    ((Cmd.op (.appendOne 0)).eval ((Cmd.op (.appendZero 0)).eval s3))
  have hs4_0 : State.get s4 0 = l ++ [1, 1] ++ List.replicate l.length 1 ++ [0, 1, 0] := by
    simp [s4, Cmd.eval_op, Op.eval, State.get_set_eq, hs3_0, List.append_assoc]
  have hs4_cur : State.get s4 SATStr.WCUR = l := by
    simp [s4, Cmd.eval_op, Op.eval, State.get_set_ne _ 0 _ SATStr.WCUR (by decide), hs3_cur]
  set s5 := appendOnesCmd.eval s4
  have hs5 := appendOnesCmd_run s4
  have hs5_0 : State.get s5 0 =
      l ++ [1, 1] ++ List.replicate l.length 1 ++ [0, 1, 0] ++ List.replicate l.length 1 := by
    rw [show s5 = appendOnesCmd.eval s4 from rfl, hs5.1, hs4_0, hs4_cur]
  simp only [Cmd.eval_op, Op.eval, State.get_set_eq, hs5_0, List.append_assoc]
  rfl

lemma boolsOf_strBits : ∀ x : List Bool, boolsOf (strBits x) = x
  | [] => rfl
  | b :: t => by
      have ih := boolsOf_strBits t
      cases b
      · simpa [boolsOf, strBits] using ih
      · simpa [boolsOf, strBits] using ih

lemma doubleSatCmd_get0 (x : List Bool) :
    State.get (doubleSatCmd.eval (certState x)) 0 = strBits (doubleSatMap x) := by
  unfold doubleSatCmd
  simp only [Cmd.eval_seq]
  set s0 := (Cmd.op (.clear SATStr.WTAL)).eval
    ((Cmd.op (.clear SATStr.WSB)).eval
      ((Cmd.op (.clear SATStr.WSA)).eval
        ((Cmd.op (.copy SATStr.WCUR 0)).eval (certState x)))) with hs0_def
  have hg0 : State.get (certState x) 0 = strBits x := rfl
  have hs0_cur : State.get s0 SATStr.WCUR = strBits x := by
    simp [s0, Cmd.eval_op, Op.eval, hg0,
      State.get_set_ne _ SATStr.WTAL _ SATStr.WCUR (by decide),
      State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide),
      State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide),
      State.get_set_eq]
  have hs0_A : State.get s0 SATStr.WSA = [] := by
    simp [s0, Cmd.eval_op, Op.eval,
      State.get_set_ne _ SATStr.WTAL _ SATStr.WSA (by decide),
      State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide),
      State.get_set_eq]
  have hs0_B : State.get s0 SATStr.WSB = [] := by
    simp [s0, Cmd.eval_op, Op.eval,
      State.get_set_ne _ SATStr.WTAL _ SATStr.WSB (by decide),
      State.get_set_eq]
  have hs0_T : State.get s0 SATStr.WTAL = [] := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hs0_0 : State.get s0 0 = strBits x := by
    simp [s0, Cmd.eval_op, Op.eval, hg0,
      State.get_set_ne _ SATStr.WTAL _ 0 (by decide),
      State.get_set_ne _ SATStr.WSB _ 0 (by decide),
      State.get_set_ne _ SATStr.WSA _ 0 (by decide),
      State.get_set_ne _ SATStr.WCUR _ 0 (by decide)]
  set u := (Cmd.forBnd SATStr.WIDX SATStr.WCUR SATStr.scanBody).eval s0 with hu_def
  obtain ⟨hUA, hUB, _⟩ := SATStr.scanLoop_run (strBits x) s0 hs0_cur hs0_A hs0_B hs0_T
  have hU0 : State.get u 0 = strBits x := by
    have hfr := Cmd.eval_get_of_not_writes (Cmd.forBnd SATStr.WIDX SATStr.WCUR SATStr.scanBody) s0 0 (by decide)
    exact hfr.trans hs0_0
  have hu1_eq : (Cmd.op (.nonEmpty SATStr.WHD SATStr.WSA)).eval u =
      u.set SATStr.WHD (if (scanRun (strBits x)).1 then [1] else [0]) := by
    rw [Cmd.eval_op]
    show u.set SATStr.WHD (if (State.get u SATStr.WSA).isEmpty then [0] else [1]) = _
    rw [hUA]
    cases (scanRun (strBits x)).1 <;> rfl
  rw [hu1_eq]
  cases ha : (scanRun (strBits x)).1 with
  | true =>
      have hhd : State.get (u.set SATStr.WHD (if true then [1] else [0])) SATStr.WHD = [1] := by
        simp [State.get_set_eq]
      rw [Cmd.eval_ifBit_true _ _ _ _ hhd, badBranch_get0]
      have hnw : wfCnfB (strBits x) = false := by simp [wfCnfB, ha]
      rw [doubleSatMap, if_neg (by rw [hnw]; decide)]; rfl
  | false =>
      have hhd : State.get (u.set SATStr.WHD (if false then [1] else [0])) SATStr.WHD ≠ [1] := by
        simp [State.get_set_eq]
      rw [Cmd.eval_ifBit_false _ _ _ _ hhd, Cmd.eval_seq]
      have hu2_eq : (Cmd.op (.nonEmpty SATStr.WHD SATStr.WSB)).eval (u.set SATStr.WHD (if false then [1] else [0])) =
          u.set SATStr.WHD (if (scanRun (strBits x)).2.1 then [1] else [0]) := by
        rw [Cmd.eval_op]
        show (u.set SATStr.WHD [0]).set SATStr.WHD (if (State.get (u.set SATStr.WHD [0]) SATStr.WSB).isEmpty then [0] else [1]) = _
        rw [State.get_set_ne _ SATStr.WHD _ SATStr.WSB (by decide), hUB, State.set_set]
        cases (scanRun (strBits x)).2.1 <;> rfl
      rw [hu2_eq]
      cases hb : (scanRun (strBits x)).2.1 with
      | true =>
          have hhd2 : State.get (u.set SATStr.WHD (if true then [1] else [0])) SATStr.WHD = [1] := by
            simp [State.get_set_eq]
          rw [Cmd.eval_ifBit_true _ _ _ _ hhd2, badBranch_get0]
          have hnw : wfCnfB (strBits x) = false := by simp [wfCnfB, ha, hb]
          rw [doubleSatMap, if_neg (by rw [hnw]; decide)]; rfl
      | false =>
          have hhd2 : State.get (u.set SATStr.WHD (if false then [1] else [0])) SATStr.WHD ≠ [1] := by
            simp [State.get_set_eq]
          have hu2_0 : State.get (u.set SATStr.WHD (if false then [1] else [0])) 0 = strBits x := by
            rw [State.get_set_ne _ SATStr.WHD _ 0 (by decide)]; exact hU0
          rw [Cmd.eval_ifBit_false _ _ _ _ hhd2, goodBranch_get0 _ (strBits x) hu2_0]
          have hwf : wfCnfB (strBits x) = true := by simp [wfCnfB, ha, hb]
          rw [doubleSatMap, if_pos hwf, padClause, strBits_append, strBits_append, strBits_append,
            strBits_append, strBits_append, strBits_replicate_true, strBits_length]
          simp only [strBits, List.map_cons, List.map_nil, ite_true, ite_false, List.append_assoc]
          rfl

lemma doubleSatCmd_chk : (doubleSatCmd.chk (2 ^ 25 - 1)).1 = true := by decide

lemma doubleSatCmd_usesBelow : Cmd.UsesBelow doubleSatCmd 25 := by
  simp [doubleSatCmd, goodBranch, badBranch, appendOnesCmd, SATStr.scanBody,
    Cmd.UsesBelow, Op.UsesBelow, SATStr.WCUR, SATStr.WIDX, SATStr.WHD,
    SATStr.WSA, SATStr.WSB, SATStr.WTAL]

lemma doubleSatCmd_cost :
    ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
      (∀ x : List Bool, doubleSatCmd.cost (certState x) ≤ budget (encodable.size x)) ∧
      (∀ x : List Bool, encodable.size (doubleSatMap x) ≤ budget (encodable.size x)) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk doubleSatCmd (2 ^ 25 - 1) doubleSatCmd_chk
  refine ⟨fun n => (K + 10) * (n + 1) ^ (D + 1) + 20, ?_, ?_, ?_, ?_⟩
  · refine inOPoly_add (inOPoly_mul (inOPoly_const (K + 10)) ⟨D + 1, 2 ^ (D + 1), 1, ?_⟩) (inOPoly_const 20)
    intro n hn
    calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
  · intro a b hab
    dsimp only
    have hpow := Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) (D + 1)
    have hmul := Nat.mul_le_mul_left (K + 10) hpow
    omega
  · intro x
    dsimp only
    have hsz : State.size (certState x) ≤ encodable.size x := by
      rw [State.size_certState]
      exact length_le_size x
    have hcost := hb (certState x) (encodable.size x) hsz
    have hmul : K * (encodable.size x + 1) ^ (D + 1) ≤ (K + 10) * (encodable.size x + 1) ^ (D + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · intro x
    dsimp only
    have hlen : (doubleSatMap x).length ≤ 3 * x.length + 7 := by
      unfold doubleSatMap
      split_ifs
      · simp [padClause]; omega
      · simp
    have hsz1 : encodable.size (doubleSatMap x) ≤ 2 * (doubleSatMap x).length :=
      size_le_two_mul_length (doubleSatMap x)
    have hsz2 : x.length ≤ encodable.size x := length_le_size x
    have hpow : encodable.size x + 1 ≤ (encodable.size x + 1) ^ (D + 1) :=
      Nat.le_self_pow (by omega) _
    nlinarith

noncomputable def doubleSatPolyLang : PolyTimeComputableLang doubleSatMap where
  c := doubleSatCmd
  encodeIn := certState
  decodeOut := fun s => boolsOf (State.get s 0)
  cost_bound := doubleSatCmd_cost.choose
  cost_bound_poly := doubleSatCmd_cost.choose_spec.1
  cost_bound_mono := doubleSatCmd_cost.choose_spec.2.1
  encBound := id
  encBound_poly := inOPoly_id
  encBound_mono := fun _ _ h => h
  encodeIn_size := fun x => by
    rw [State.size_certState]; exact length_le_size x
  computes := fun x => by
    rw [doubleSatCmd_get0]
    exact boolsOf_strBits (doubleSatMap x)
  cost_le := doubleSatCmd_cost.choose_spec.2.2.1
  output_size_le := doubleSatCmd_cost.choose_spec.2.2.2
  enc_bit := fun x => by
    intro reg hreg z hz
    simp only [certState, List.mem_singleton] at hreg
    subst hreg
    exact strBits_bit x z hz
  regBound := 25
  usesBelow := doubleSatCmd_usesBelow
  width_le := fun x => by simp [certState]
  decode_agree := fun x m => by
    have hagr : AgreeBelow 25 (certState x ++ List.replicate m []) (certState x) := fun r _ =>
      State.get_append_replicate_nil (certState x) m r
    have hev := Cmd.eval_agree doubleSatCmd 25 doubleSatCmd_usesBelow hagr
    rw [hev 0 (by omega)]

end PvsNP.Units.m3_sat_to_doublesat_aux

theorem PvsNP.Units.m3_sat_to_doublesat :
    CookLevin.reducesPoly SATStr
      (fun x => ∃ a b : assgn, satisfiesCnf a (SATStr.cnfOf x) ∧ satisfiesCnf b (SATStr.cnfOf x) ∧
        ∃ C ∈ SATStr.cnfOf x, ∃ l ∈ C, evalVar a l.2 ≠ evalVar b l.2) := by
  obtain ⟨t, M, ht, hM, h1, hcomp⟩ :=
    PvsNP.Units.m3_sat_to_doublesat_aux.doubleSatPolyLang.toMachine
      (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨PvsNP.Units.m3_sat_to_doublesat_aux.doubleSatMap, t, M, ht, hM, h1, hcomp,
    PvsNP.Units.m3_sat_to_doublesat_aux.doubleSatMap_iff⟩
