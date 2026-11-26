import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_sat_to_naesat_aux

open CookLevin CookLevin.Lang EvalCnfCmd CnfWellFormed

def ZENC : Var := 24
def OUT : Var := 25

/-- Append fresh variable `n` as positive literal `(true, n)` to every clause of `N`. -/
def naeCnf (n : Nat) (N : cnf) : cnf :=
  N.map (fun C => C ++ [(true, n)])

lemma encodeLit_bit (l : literal) : ∀ v ∈ encodeLit l, v ≤ 1 := by
  rcases l with ⟨pol, v⟩
  intro z hz
  simp only [encodeLit, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | ⟨_, rfl⟩ | rfl
  · omega
  · cases pol <;> simp
  · omega
  · omega

lemma clauseBody_bit (C : clause) : ∀ v ∈ CnfSerialize.clauseBody C, v ≤ 1 := by
  induction C with
  | nil => intro z hz; cases hz
  | cons l rest ih =>
      intro z hz
      rw [CnfSerialize.clauseBody_cons, List.mem_append] at hz
      rcases hz with h | h
      · exact encodeLit_bit l z h
      · exact ih z h

lemma encodeClause_bit (C : clause) : ∀ v ∈ encodeClause C, v ≤ 1 := by
  intro z hz
  rw [CnfSerialize.encodeClause_eq, List.mem_append, List.mem_singleton] at hz
  rcases hz with h | rfl
  · exact clauseBody_bit C z h
  · omega

lemma encodeCnf_bit (N : cnf) : ∀ v ∈ encodeCnf N, v ≤ 1 := by
  induction N with
  | nil => intro z hz; cases hz
  | cons C rest ih =>
      intro z hz
      rw [CnfSerialize.encodeCnf_cons, List.mem_append] at hz
      rcases hz with h | h
      · exact encodeClause_bit C z h
      · exact ih z h

/-- Reduction map from `SATStr` to `NAE-SAT`. -/
def naeSatMap (x : List Bool) : List Bool :=
  if wfCnfB (strBits x) then
    boolsOf (encodeCnf (naeCnf x.length (SATStr.cnfOf x)))
  else
    [false]

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

lemma clauseBody_append (C₁ C₂ : clause) :
    CnfSerialize.clauseBody (C₁ ++ C₂) = CnfSerialize.clauseBody C₁ ++ CnfSerialize.clauseBody C₂ := by
  induction C₁ with
  | nil => rfl
  | cons l rest ih =>
      simp only [List.cons_append, CnfSerialize.clauseBody_cons, ih, List.append_assoc]

lemma encodeClause_append_lit (C : clause) (l : literal) :
    encodeClause (C ++ [l]) = CnfSerialize.clauseBody C ++ encodeLit l ++ [0] := by
  rw [CnfSerialize.encodeClause_eq, clauseBody_append]
  simp [CnfSerialize.clauseBody, List.append_assoc]

lemma encodeCnf_naeCnf_length (n : Nat) (N : cnf) :
    (encodeCnf (naeCnf n N)).length ≤ (encodeCnf N).length + N.length * (n + 3) := by
  induction N with
  | nil => simp [naeCnf, encodeCnf]
  | cons C rest ih =>
      have hcons : naeCnf n (C :: rest) = (C ++ [(true, n)]) :: naeCnf n rest := rfl
      rw [hcons, CnfSerialize.encodeCnf_cons, CnfSerialize.encodeCnf_cons, List.length_append,
        List.length_append, List.length_cons, encodeClause_append_lit, CnfSerialize.encodeClause_eq]
      have hlit : (encodeLit (true, n)).length = n + 3 := by simp [encodeLit]
      simp only [List.length_append, List.length_singleton, hlit]
      have : (rest.length + 1) * (n + 3) = rest.length * (n + 3) + (n + 3) := by ring
      omega

lemma length_le_encodeCnf_length (N : cnf) : N.length ≤ (encodeCnf N).length := by
  induction N with
  | nil => simp [encodeCnf]
  | cons C rest ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append, CnfSerialize.encodeClause_eq,
        List.length_append, List.length_singleton, List.length_cons]
      omega

lemma naeSatMap_iff (x : List Bool) :
    SATStr x ↔
      ∃ a : assgn, ∀ C ∈ SATStr.cnfOf (naeSatMap x),
        C.any (evalLiteral a) = true ∧ C.any (fun l => !evalLiteral a l) = true := by
  by_cases hwf : wfCnfB (strBits x) = true
  · set N := SATStr.cnfOf x with hN_def
    have hstrN : encodeCnf N = strBits x := encodeCnf_parseTotal _ (strBits_bit x) hwf
    have hmap : naeSatMap x = boolsOf (encodeCnf (naeCnf x.length N)) := by
      simp [naeSatMap, hwf, hN_def]
    have hcnf : SATStr.cnfOf (naeSatMap x) = naeCnf x.length N := by
      show parseTotal (strBits (naeSatMap x)) = _
      rw [hmap, strBits_boolsOf (encodeCnf_bit _), parseTotal_encodeCnf]
    rw [hcnf]
    set n := x.length with hn_def
    have hlt_N : ∀ C ∈ N, ∀ l ∈ C, l.2 < n := by
      intro C hC l hl
      have h := var_lt_encodeCnf_length hC hl
      rw [hstrN, strBits_length] at h
      exact h
    constructor
    · intro hsat
      obtain ⟨a, ha⟩ := hsat
      let a₀ : assgn := a.filter (fun v => decide (v ≠ n))
      refine ⟨a₀, ?_⟩
      intro C' hC'
      simp only [naeCnf, List.mem_map] at hC'
      rcases hC' with ⟨C, hC, rfl⟩
      have hCa : evalClause a C = true := (evalCnf_clause_iff a N).mp ha C hC
      obtain ⟨l, hlC, hla⟩ := (evalClause_literal_iff a C).mp hCa
      have hl_ne : l.2 ≠ n := Nat.ne_of_lt (hlt_N C hC l hlC)
      have hla0 : evalLiteral a₀ l = true := by
        have hv : evalVar a₀ l.2 = evalVar a l.2 := by simp [evalVar, a₀, List.mem_filter, hl_ne]
        rcases l with ⟨pol, v⟩
        simp only [evalLiteral] at hla ⊢
        rw [hv]; exact hla
      have hn0 : evalLiteral a₀ (true, n) = false := by
        simp [evalLiteral, evalVar, a₀, List.mem_filter]
      constructor
      · exact List.any_eq_true.mpr ⟨l, List.mem_append_left _ hlC, hla0⟩
      · exact List.any_eq_true.mpr ⟨(true, n), List.mem_append_right _ (List.mem_singleton_self _), by simp [hn0]⟩
    · rintro ⟨a, hnae⟩
      by_cases hzn : evalVar a n = false
      · refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
        intro C hC
        have hC' := hnae (C ++ [(true, n)]) (List.mem_map.mpr ⟨C, hC, rfl⟩)
        obtain ⟨l, hl_mem, hl_val⟩ := List.any_eq_true.mp hC'.1
        rcases List.mem_append.mp hl_mem with hlC | hlz
        · exact (evalClause_literal_iff a C).mpr ⟨l, hlC, hl_val⟩
        · simp only [List.mem_singleton] at hlz
          subst hlz
          simp [evalLiteral, hzn] at hl_val
      · have hzt : evalVar a n = true := Bool.eq_true_of_not_eq_false hzn
        let a' : assgn := (List.range n).filter (fun v => decide (v ∉ a))
        refine ⟨a', (evalCnf_clause_iff a' N).mpr ?_⟩
        intro C hC
        have hC' := hnae (C ++ [(true, n)]) (List.mem_map.mpr ⟨C, hC, rfl⟩)
        obtain ⟨l, hl_mem, hl_val⟩ := List.any_eq_true.mp hC'.2
        rcases List.mem_append.mp hl_mem with hlC | hlz
        · have hl_lt : l.2 < n := hlt_N C hC l hlC
          have hv : evalVar a' l.2 = !evalVar a l.2 := by
            simp only [evalVar, a', List.mem_filter, List.mem_range, hl_lt, true_and, decide_eq_true_eq]
            by_cases hm : l.2 ∈ a <;> simp [hm]
          have hlit : evalLiteral a' l = true := by
            rcases l with ⟨pol, v⟩
            simp only [evalLiteral] at hl_val hv ⊢
            rw [hv]
            cases pol <;> cases h : evalVar a v <;> simp [h] at hl_val ⊢
          exact (evalClause_literal_iff a' C).mpr ⟨l, hlC, hlit⟩
        · simp only [List.mem_singleton] at hlz
          subst hlz
          simp [evalLiteral, hzt] at hl_val
  · have hwfF : wfCnfB (strBits x) = false := Bool.eq_false_iff.mpr hwf
    have hmap : naeSatMap x = [false] := by simp [naeSatMap, hwfF]
    have hbotX : SATStr.cnfOf x = botCnf := parseTotal_of_not_wf _ hwfF
    have hbotF : SATStr.cnfOf [false] = botCnf := rfl
    constructor
    · intro hsat
      exact absurd (hbotX ▸ hsat) not_sat_botCnf
    · rintro ⟨a, hnae⟩
      rw [hmap, hbotF] at hnae
      have h := (hnae [] (by simp [botCnf])).1
      simp at h

/-- Functional model of the streaming NAE-SAT emitter. -/
def naeStep (zenc : List Nat) : (Bool × Bool × List Nat) → Nat → (Bool × Bool × List Nat)
  | (false, _, out), cell =>
      if cell = 1 then (true, false, out ++ [1])
      else (false, false, out ++ zenc)
  | (true, false, out), cell =>
      (true, true, out ++ [if cell = 1 then 1 else 0])
  | (true, true, out), cell =>
      if cell = 1 then (true, true, out ++ [1])
      else (false, true, out ++ [0])

def naeRun (zenc l : List Nat) : Bool × Bool × List Nat :=
  l.foldl (naeStep zenc) (false, false, [])

def naeTake (zenc l : List Nat) (i : Nat) : Bool × Bool × List Nat :=
  (l.take i).foldl (naeStep zenc) (false, false, [])

lemma naeTake_zero (zenc l : List Nat) : naeTake zenc l 0 = (false, false, []) := rfl

lemma naeTake_length (zenc l : List Nat) : naeTake zenc l l.length = naeRun zenc l := by
  rw [naeTake, List.take_length]; rfl

lemma naeTake_succ (zenc l : List Nat) (i : Nat) (hi : i < l.length) :
    naeTake zenc l (i + 1) = naeStep zenc (naeTake zenc l i) l[i] := by
  rw [naeTake, naeTake, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma nae_proj_scan (zenc l : List Nat) (a b : Bool) (out : List Nat) (k : Nat) :
    let r := l.foldl (naeStep zenc) (a, b, out)
    let s := l.foldl scanStep (a, b, k)
    r.1 = s.1 ∧ r.2.1 = s.2.1 := by
  induction l generalizing a b out k with
  | nil => exact ⟨rfl, rfl⟩
  | cons cell rest ih =>
      simp only [List.foldl_cons]
      cases a with
      | false =>
          by_cases hc : cell = 1
          · simpa [naeStep, scanStep, hc] using ih true false (out ++ [1]) k
          · simpa [naeStep, scanStep, hc] using ih false false (out ++ zenc) (k + 1)
      | true =>
          cases b with
          | false => simpa [naeStep, scanStep] using ih true true (out ++ [if cell = 1 then 1 else 0]) k
          | true =>
              by_cases hc : cell = 1
              · simpa [naeStep, scanStep, hc] using ih true true (out ++ [1]) k
              · simpa [naeStep, scanStep, hc] using ih false true (out ++ [0]) k

lemma naeRun_proj (zenc l : List Nat) :
    (naeRun zenc l).1 = (scanRun l).1 ∧ (naeRun zenc l).2.1 = (scanRun l).2.1 :=
  nae_proj_scan zenc l false false [] 0

lemma nae_replicate_one (zenc : List Nat) (v : Nat) (out : List Nat) :
    (List.replicate v 1).foldl (naeStep zenc) (true, true, out) = (true, true, out ++ List.replicate v 1) := by
  induction v generalizing out with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have hstep : naeStep zenc (true, true, out) 1 = (true, true, out ++ [1]) := rfl
      rw [hstep, ih (out ++ [1]), List.append_assoc]
      simp

lemma nae_encodeLit (zenc : List Nat) (l : literal) (p : Bool) (out : List Nat) :
    (encodeLit l).foldl (naeStep zenc) (false, p, out) = (false, true, out ++ encodeLit l) := by
  rcases l with ⟨pol, v⟩
  show (List.replicate v 1 ++ [0]).foldl (naeStep zenc)
      (naeStep zenc (naeStep zenc (false, p, out) 1) (if pol then 1 else 0)) = _
  have h1 : naeStep zenc (false, p, out) 1 = (true, false, out ++ [1]) := rfl
  rw [h1]
  have h2 : naeStep zenc (true, false, out ++ [1]) (if pol then 1 else 0) =
      (true, true, out ++ [1, if pol then 1 else 0]) := by
    cases pol <;> simp [naeStep, List.append_assoc]
  rw [h2, List.foldl_append, nae_replicate_one]
  simp [naeStep, encodeLit, List.append_assoc]

lemma nae_clauseBody (zenc : List Nat) (C : clause) :
    ∀ (p : Bool) (out : List Nat),
      ∃ q, (CnfSerialize.clauseBody C).foldl (naeStep zenc) (false, p, out) =
        (false, q, out ++ CnfSerialize.clauseBody C) := by
  induction C with
  | nil => intro p out; exact ⟨p, by simp [CnfSerialize.clauseBody]⟩
  | cons l rest ih =>
      intro p out
      rw [CnfSerialize.clauseBody_cons, List.foldl_append, nae_encodeLit zenc l p out]
      obtain ⟨q, hq⟩ := ih true (out ++ encodeLit l)
      exact ⟨q, by rw [hq, List.append_assoc]⟩

lemma nae_encodeClause (n : Nat) (C : clause) (p : Bool) (out : List Nat) :
    (encodeClause C).foldl (naeStep (encodeLit (true, n) ++ [0])) (false, p, out) =
      (false, false, out ++ encodeClause (C ++ [(true, n)])) := by
  obtain ⟨q, hq⟩ := nae_clauseBody (encodeLit (true, n) ++ [0]) C p out
  rw [CnfSerialize.encodeClause_eq, List.foldl_append, hq]
  simp only [List.foldl_cons, List.foldl_nil, naeStep, show (0 : Nat) ≠ 1 by decide, ↓reduceIte]
  rw [encodeClause_append_lit, List.append_assoc, List.append_assoc]

lemma nae_encodeCnf (n : Nat) (N : cnf) :
    ∀ (out : List Nat),
      (encodeCnf N).foldl (naeStep (encodeLit (true, n) ++ [0])) (false, false, out) =
        (false, false, out ++ encodeCnf (naeCnf n N)) := by
  induction N with
  | nil => intro out; simp [encodeCnf, naeCnf]
  | cons C rest ih =>
      intro out
      rw [CnfSerialize.encodeCnf_cons, List.foldl_append, nae_encodeClause n C false out, ih]
      simp [naeCnf, CnfSerialize.encodeCnf_cons, List.append_assoc]

lemma naeRun_encodeCnf (n : Nat) (N : cnf) :
    (naeRun (encodeLit (true, n) ++ [0]) (encodeCnf N)).2.2 = encodeCnf (naeCnf n N) := by
  show ((encodeCnf N).foldl (naeStep (encodeLit (true, n) ++ [0])) (false, false, [])).2.2 = _
  rw [nae_encodeCnf n N []]
  simp

/-- Build `ZENC = [1, 1] ++ 1^n ++ [0, 0] = encodeLit (true, n) ++ [0]`. -/
def buildZenc : Cmd :=
  Cmd.op (.copy SATStr.WCUR 0) ;;
  Cmd.op (.clear ZENC) ;;
  Cmd.op (.appendOne ZENC) ;;
  Cmd.op (.appendOne ZENC) ;;
  Cmd.forBnd SATStr.WIDX SATStr.WCUR (Cmd.op (.appendOne ZENC)) ;;
  Cmd.op (.appendZero ZENC) ;;
  Cmd.op (.appendZero ZENC)

/-- One cell of the NAE-SAT streaming emitter. -/
def naeBody : Cmd :=
  Cmd.op (.head SATStr.WHD SATStr.WCUR) ;;
  Cmd.op (.tail SATStr.WCUR SATStr.WCUR) ;;
  Cmd.ifBit SATStr.WSA
    (Cmd.ifBit SATStr.WSB
      (Cmd.ifBit SATStr.WHD
        (Cmd.op (.appendOne OUT))
        (Cmd.op (.clear SATStr.WSA) ;; Cmd.op (.appendZero OUT)))
      (Cmd.op (.clear SATStr.WSB) ;; Cmd.op (.appendOne SATStr.WSB) ;;
       Cmd.ifBit SATStr.WHD (Cmd.op (.appendOne OUT)) (Cmd.op (.appendZero OUT))))
    (Cmd.ifBit SATStr.WHD
      (Cmd.op (.clear SATStr.WSA) ;; Cmd.op (.appendOne SATStr.WSA) ;;
       Cmd.op (.clear SATStr.WSB) ;; Cmd.op (.appendOne OUT))
      (Cmd.op (.clear SATStr.WSB) ;; Cmd.op (.concat OUT OUT ZENC)))

def badBranch : Cmd :=
  Cmd.op (.clear 0) ;; Cmd.op (.appendZero 0)

def naeSatCmd : Cmd :=
  buildZenc ;;
  Cmd.op (.clear SATStr.WSA) ;;
  Cmd.op (.clear SATStr.WSB) ;;
  Cmd.op (.clear OUT) ;;
  Cmd.forBnd SATStr.WIDX SATStr.WCUR naeBody ;;
  Cmd.op (.nonEmpty SATStr.WHD SATStr.WSA) ;;
  Cmd.ifBit SATStr.WHD badBranch
    (Cmd.op (.nonEmpty SATStr.WHD SATStr.WSB) ;;
     Cmd.ifBit SATStr.WHD badBranch (Cmd.op (.copy 0 OUT)))

lemma eval_appendZero (s : State) (r : Var) :
    (Cmd.op (.appendZero r)).eval s = s.set r (State.get s r ++ [0]) := rfl

lemma buildZenc_run (x : List Bool) :
    State.get (buildZenc.eval (certState x)) ZENC = encodeLit (true, x.length) ++ [0] ∧
    State.get (buildZenc.eval (certState x)) SATStr.WCUR = strBits x := by
  unfold buildZenc
  simp only [Cmd.eval_seq]
  set s0 := (Cmd.op (.appendOne ZENC)).eval
    ((Cmd.op (.appendOne ZENC)).eval
      ((Cmd.op (.clear ZENC)).eval
        ((Cmd.op (.copy SATStr.WCUR 0)).eval (certState x))))
  have hg0 : State.get (certState x) 0 = strBits x := rfl
  have hs0_cur : State.get s0 SATStr.WCUR = strBits x := by
    simp [s0, Cmd.eval_op, Op.eval, hg0,
      State.get_set_ne _ ZENC _ SATStr.WCUR (by decide), State.get_set_eq]
  have hs0_z : State.get s0 ZENC = [1, 1] := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_eq]
  set s1 := (Cmd.forBnd SATStr.WIDX SATStr.WCUR (Cmd.op (.appendOne ZENC))).eval s0 with hs1_def
  have hloop : State.get s1 ZENC = [1, 1] ++ List.replicate x.length 1 ∧
      State.get s1 SATStr.WCUR = strBits x := by
    have hlen : (State.get s0 SATStr.WCUR).length = x.length := by rw [hs0_cur, strBits_length]
    rw [hs1_def, Cmd.eval_forBnd, hlen]
    exact Cmd.foldlState_range_induct (Cmd.op (.appendOne ZENC)) SATStr.WIDX x.length s0
      (fun i st => State.get st ZENC = [1, 1] ++ List.replicate i 1 ∧ State.get st SATStr.WCUR = strBits x)
      ⟨by simp [hs0_z], hs0_cur⟩
      (by
        rintro i st _ ⟨hz, hc⟩
        simp only [Cmd.eval_op, Op.eval]
        constructor
        · rw [State.get_set_eq, State.get_set_ne _ SATStr.WIDX _ ZENC (by decide), hz,
            List.append_assoc, List.replicate_succ']
        · rw [State.get_set_ne _ ZENC _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WIDX _ SATStr.WCUR (by decide), hc])
  rw [eval_appendZero s1 ZENC, eval_appendZero _ ZENC]
  constructor
  · rw [State.get_set_eq, State.get_set_eq, hloop.1]
    simp only [encodeLit, ite_true, List.cons_append, List.nil_append, List.append_assoc]
  · rw [State.get_set_ne _ ZENC _ SATStr.WCUR (by decide),
      State.get_set_ne _ ZENC _ SATStr.WCUR (by decide), hloop.2]

set_option maxHeartbeats 800000 in
lemma naeBody_run (zenc l : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hC : State.get s SATStr.WCUR = l.drop i)
    (hA : State.get s SATStr.WSA = SATStr.flagOf (naeTake zenc l i).1)
    (hB : State.get s SATStr.WSB = SATStr.flagOf (naeTake zenc l i).2.1)
    (hO : State.get s OUT = (naeTake zenc l i).2.2)
    (hZ : State.get s ZENC = zenc) :
    State.get (naeBody.eval s) SATStr.WCUR = l.drop (i + 1) ∧
    State.get (naeBody.eval s) SATStr.WSA = SATStr.flagOf (naeTake zenc l (i + 1)).1 ∧
    State.get (naeBody.eval s) SATStr.WSB = SATStr.flagOf (naeTake zenc l (i + 1)).2.1 ∧
    State.get (naeBody.eval s) OUT = (naeTake zenc l (i + 1)).2.2 ∧
    State.get (naeBody.eval s) ZENC = zenc := by
  have hcons : State.get s SATStr.WCUR = l[i] :: l.drop (i + 1) := by
    rw [hC, List.drop_eq_getElem_cons hi]
  have e1 : (Cmd.op (Op.head SATStr.WHD SATStr.WCUR)).eval s = s.set SATStr.WHD [l[i]] := by
    simp only [Cmd.eval_op, Op.eval, hcons]
  have hC1 : State.get (s.set SATStr.WHD [l[i]]) SATStr.WCUR = l[i] :: l.drop (i + 1) := by
    rw [State.get_set_ne s SATStr.WHD _ SATStr.WCUR (by decide)]; exact hcons
  have e2 : (Cmd.op (Op.tail SATStr.WCUR SATStr.WCUR)).eval (s.set SATStr.WHD [l[i]]) =
      (s.set SATStr.WHD [l[i]]).set SATStr.WCUR (l.drop (i + 1)) := by
    simp only [Cmd.eval_op, Op.eval, hC1, List.tail_cons]
  rw [naeBody, Cmd.eval_seq, e1, Cmd.eval_seq, e2]
  set t : State := (s.set SATStr.WHD [l[i]]).set SATStr.WCUR (l.drop (i + 1)) with ht
  have hT_C : State.get t SATStr.WCUR = l.drop (i + 1) := State.get_set_eq _ _ _
  have hT_HD : State.get t SATStr.WHD = [l[i]] := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WHD (by decide), State.get_set_eq]
  have hT_A : State.get t SATStr.WSA = SATStr.flagOf (naeTake zenc l i).1 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WSA (by decide),
      State.get_set_ne _ SATStr.WHD _ SATStr.WSA (by decide)]; exact hA
  have hT_B : State.get t SATStr.WSB = SATStr.flagOf (naeTake zenc l i).2.1 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WSB (by decide),
      State.get_set_ne _ SATStr.WHD _ SATStr.WSB (by decide)]; exact hB
  have hT_O : State.get t OUT = (naeTake zenc l i).2.2 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ OUT (by decide),
      State.get_set_ne _ SATStr.WHD _ OUT (by decide)]; exact hO
  have hT_Z : State.get t ZENC = zenc := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ ZENC (by decide),
      State.get_set_ne _ SATStr.WHD _ ZENC (by decide)]; exact hZ
  rw [naeTake_succ zenc l i hi]
  rcases hm : naeTake zenc l i with ⟨a, b, out⟩
  rw [hm] at hT_A hT_B hT_O
  by_cases hcell : l[i] = 1
  · have hHD : State.get t SATStr.WHD = [1] := by rw [hT_HD, hcell]
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl), Cmd.eval_ifBit_true _ _ _ _ hHD]
            simp only [Cmd.eval_op, Op.eval, naeStep, hcell, ↓reduceIte]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide)]; exact hT_A
            · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide)]; exact hT_B
            · rw [State.get_set_eq, hT_O]
            · rw [State.get_set_ne _ OUT _ ZENC (by decide)]; exact hT_Z
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [SATStr.flagOf])]
            simp only [Cmd.eval_seq, naeStep, hcell, ↓reduceIte]
            set t1 := (Cmd.op (.appendOne SATStr.WSB)).eval ((Cmd.op (.clear SATStr.WSB)).eval t)
            have ht1_eq : t1 = t.set SATStr.WSB [1] := by
              simp [t1, Cmd.eval_op, Op.eval, State.set_set, State.get_set_eq]
            have ht1_HD : State.get t1 SATStr.WHD = [1] := by
              rw [ht1_eq, State.get_set_ne _ SATStr.WSB _ SATStr.WHD (by decide)]; exact hHD
            rw [Cmd.eval_ifBit_true _ _ _ _ ht1_HD]
            simp only [Cmd.eval_op, Op.eval, ht1_eq]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
                State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide),
                State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]; exact hT_A
            · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide), State.get_set_eq]; rfl
            · rw [State.get_set_eq, State.get_set_ne _ SATStr.WSB _ OUT (by decide), hT_O]
            · rw [State.get_set_ne _ OUT _ ZENC (by decide),
                State.get_set_ne _ SATStr.WSB _ ZENC (by decide)]; exact hT_Z
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [SATStr.flagOf]), Cmd.eval_ifBit_true _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.set_set, State.get_set_eq, naeStep, hcell, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide)]; exact hT_C
        · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide), State.get_set_eq]; rfl
        · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide), State.get_set_eq]; rfl
        · rw [State.get_set_ne _ SATStr.WSB _ OUT (by decide),
            State.get_set_ne _ SATStr.WSA _ OUT (by decide), hT_O]
        · rw [State.get_set_ne _ OUT _ ZENC (by decide),
            State.get_set_ne _ SATStr.WSB _ ZENC (by decide),
            State.get_set_ne _ SATStr.WSA _ ZENC (by decide)]; exact hT_Z
  · have hHD : State.get t SATStr.WHD ≠ [1] := by rw [hT_HD]; simpa using hcell
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl), Cmd.eval_ifBit_false _ _ _ _ hHD]
            simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, naeStep, hcell, ↓reduceIte]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
                State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide), State.get_set_eq]; rfl
            · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide),
                State.get_set_ne _ SATStr.WSA _ SATStr.WSB (by decide)]; exact hT_B
            · rw [State.get_set_eq, State.get_set_ne _ SATStr.WSA _ OUT (by decide), hT_O]
            · rw [State.get_set_ne _ OUT _ ZENC (by decide),
                State.get_set_ne _ SATStr.WSA _ ZENC (by decide)]; exact hT_Z
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [SATStr.flagOf])]
            simp only [Cmd.eval_seq, naeStep, hcell, ↓reduceIte]
            set t1 := (Cmd.op (.appendOne SATStr.WSB)).eval ((Cmd.op (.clear SATStr.WSB)).eval t)
            have ht1_eq : t1 = t.set SATStr.WSB [1] := by
              simp [t1, Cmd.eval_op, Op.eval, State.set_set, State.get_set_eq]
            have ht1_HD : State.get t1 SATStr.WHD ≠ [1] := by
              rw [ht1_eq, State.get_set_ne _ SATStr.WSB _ SATStr.WHD (by decide)]; exact hHD
            rw [Cmd.eval_ifBit_false _ _ _ _ ht1_HD]
            simp only [Cmd.eval_op, Op.eval, ht1_eq]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
                State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide),
                State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]; exact hT_A
            · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide), State.get_set_eq]; rfl
            · rw [State.get_set_eq, State.get_set_ne _ SATStr.WSB _ OUT (by decide), hT_O]
            · rw [State.get_set_ne _ OUT _ ZENC (by decide),
                State.get_set_ne _ SATStr.WSB _ ZENC (by decide)]; exact hT_Z
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [SATStr.flagOf]), Cmd.eval_ifBit_false _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, naeStep, hcell, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]; exact hT_C
        · rw [State.get_set_ne _ OUT _ SATStr.WSA (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]; exact hT_A
        · rw [State.get_set_ne _ OUT _ SATStr.WSB (by decide), State.get_set_eq]; rfl
        · rw [State.get_set_eq, State.get_set_ne _ SATStr.WSB _ OUT (by decide),
            State.get_set_ne _ SATStr.WSB _ ZENC (by decide), hT_O, hT_Z]
        · rw [State.get_set_ne _ OUT _ ZENC (by decide),
            State.get_set_ne _ SATStr.WSB _ ZENC (by decide)]; exact hT_Z

lemma naeLoop_run (zenc l : List Nat) (s : State)
    (hC : State.get s SATStr.WCUR = l) (hA : State.get s SATStr.WSA = [])
    (hB : State.get s SATStr.WSB = []) (hO : State.get s OUT = [])
    (hZ : State.get s ZENC = zenc) :
    State.get ((Cmd.forBnd SATStr.WIDX SATStr.WCUR naeBody).eval s) SATStr.WSA = SATStr.flagOf (naeRun zenc l).1 ∧
    State.get ((Cmd.forBnd SATStr.WIDX SATStr.WCUR naeBody).eval s) SATStr.WSB = SATStr.flagOf (naeRun zenc l).2.1 ∧
    State.get ((Cmd.forBnd SATStr.WIDX SATStr.WCUR naeBody).eval s) OUT = (naeRun zenc l).2.2 := by
  have hlen : (State.get s SATStr.WCUR).length = l.length := by rw [hC]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct naeBody SATStr.WIDX l.length s
    (fun i st =>
      State.get st SATStr.WCUR = l.drop i ∧
      State.get st SATStr.WSA = SATStr.flagOf (naeTake zenc l i).1 ∧
      State.get st SATStr.WSB = SATStr.flagOf (naeTake zenc l i).2.1 ∧
      State.get st OUT = (naeTake zenc l i).2.2 ∧
      State.get st ZENC = zenc)
    ⟨by simpa using hC, by rw [hA]; rfl, by rw [hB]; rfl, by rw [hO]; rfl, hZ⟩
    (by
      rintro i st hi ⟨rC, rA, rB, rO, rZ⟩
      refine naeBody_run zenc l i hi _ ?_ ?_ ?_ ?_ ?_
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WCUR (by decide)]; exact rC
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WSA (by decide)]; exact rA
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WSB (by decide)]; exact rB
      · rw [State.get_set_ne _ SATStr.WIDX _ OUT (by decide)]; exact rO
      · rw [State.get_set_ne _ SATStr.WIDX _ ZENC (by decide)]; exact rZ)
  simp only [naeTake_length] at key
  exact ⟨key.2.1, key.2.2.1, key.2.2.2.1⟩

lemma badBranch_get0 (s : State) : State.get (badBranch.eval s) 0 = [0] := by
  simp [badBranch, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]

lemma boolsOf_strBits : ∀ x : List Bool, boolsOf (strBits x) = x
  | [] => rfl
  | b :: t => by
      have ih := boolsOf_strBits t
      cases b
      · simpa [boolsOf, strBits] using ih
      · simpa [boolsOf, strBits] using ih

lemma naeSatCmd_get0 (x : List Bool) :
    State.get (naeSatCmd.eval (certState x)) 0 = strBits (naeSatMap x) := by
  unfold naeSatCmd
  simp only [Cmd.eval_seq]
  obtain ⟨hbZ, hbC⟩ := buildZenc_run x
  set zenc := encodeLit (true, x.length) ++ [0]
  set s0 := (Cmd.op (.clear OUT)).eval
    ((Cmd.op (.clear SATStr.WSB)).eval
      ((Cmd.op (.clear SATStr.WSA)).eval (buildZenc.eval (certState x)))) with hs0_def
  have hs0_C : State.get s0 SATStr.WCUR = strBits x := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne _ OUT _ SATStr.WCUR (by decide),
      State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide),
      State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide), hbC]
  have hs0_A : State.get s0 SATStr.WSA = [] := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne _ OUT _ SATStr.WSA (by decide),
      State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide), State.get_set_eq]
  have hs0_B : State.get s0 SATStr.WSB = [] := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne _ OUT _ SATStr.WSB (by decide), State.get_set_eq]
  have hs0_O : State.get s0 OUT = [] := by simp [s0, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hs0_Z : State.get s0 ZENC = zenc := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne _ OUT _ ZENC (by decide),
      State.get_set_ne _ SATStr.WSB _ ZENC (by decide),
      State.get_set_ne _ SATStr.WSA _ ZENC (by decide), hbZ]
  set u := (Cmd.forBnd SATStr.WIDX SATStr.WCUR naeBody).eval s0 with hu_def
  obtain ⟨hUA, hUB, hUO⟩ := naeLoop_run zenc (strBits x) s0 hs0_C hs0_A hs0_B hs0_O hs0_Z
  obtain ⟨hp1, hp2⟩ := naeRun_proj zenc (strBits x)
  rw [hp1] at hUA; rw [hp2] at hUB
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
      rw [naeSatMap, if_neg (by rw [hnw]; decide)]; rfl
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
          rw [naeSatMap, if_neg (by rw [hnw]; decide)]; rfl
      | false =>
          have hhd2 : State.get (u.set SATStr.WHD (if false then [1] else [0])) SATStr.WHD ≠ [1] := by
            simp [State.get_set_eq]
          rw [Cmd.eval_ifBit_false _ _ _ _ hhd2, Cmd.eval_op]
          show State.get ((u.set SATStr.WHD [0]).set 0 (State.get (u.set SATStr.WHD [0]) OUT)) 0 = _
          rw [State.get_set_eq, State.get_set_ne _ SATStr.WHD _ OUT (by decide), hUO]
          have hwf : wfCnfB (strBits x) = true := by simp [wfCnfB, ha, hb]
          have hstrN : encodeCnf (SATStr.cnfOf x) = strBits x := encodeCnf_parseTotal _ (strBits_bit x) hwf
          rw [naeSatMap, if_pos hwf, strBits_boolsOf (encodeCnf_bit _), ← hstrN, naeRun_encodeCnf]

lemma naeSatCmd_chk : (naeSatCmd.chk (2 ^ 26 - 1)).1 = true := by decide

lemma naeSatCmd_usesBelow : Cmd.UsesBelow naeSatCmd 26 := by
  simp [naeSatCmd, buildZenc, naeBody, badBranch, Cmd.UsesBelow, Op.UsesBelow,
    SATStr.WCUR, SATStr.WIDX, SATStr.WHD, SATStr.WSA, SATStr.WSB, ZENC, OUT]

lemma naeSatCmd_cost :
    ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
      (∀ x : List Bool, naeSatCmd.cost (certState x) ≤ budget (encodable.size x)) ∧
      (∀ x : List Bool, encodable.size (naeSatMap x) ≤ budget (encodable.size x)) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk naeSatCmd (2 ^ 26 - 1) naeSatCmd_chk
  refine ⟨fun n => (K + 10) * (n + 1) ^ (D + 2) + 20, ?_, ?_, ?_, ?_⟩
  · refine inOPoly_add (inOPoly_mul (inOPoly_const (K + 10)) ⟨D + 2, 2 ^ (D + 2), 1, ?_⟩) (inOPoly_const 20)
    intro n hn
    calc (n + 1) ^ (D + 2) ≤ (2 * n) ^ (D + 2) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 2) * n ^ (D + 2) := by rw [Nat.mul_pow]
  · intro a b hab
    dsimp only
    have hpow := Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) (D + 2)
    have hmul := Nat.mul_le_mul_left (K + 10) hpow
    omega
  · intro x
    dsimp only
    have hsz : State.size (certState x) ≤ encodable.size x := by
      rw [State.size_certState]; exact length_le_size x
    have hcost := hb (certState x) (encodable.size x) hsz
    have hpow1 : (encodable.size x + 1) ^ (D + 1) ≤ (encodable.size x + 1) ^ (D + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hmul : K * (encodable.size x + 1) ^ (D + 1) ≤ (K + 10) * (encodable.size x + 1) ^ (D + 2) :=
      Nat.mul_le_mul (by omega) hpow1
    omega
  · intro x
    dsimp only
    have hlen : (naeSatMap x).length ≤ x.length + x.length * (x.length + 3) + 1 := by
      unfold naeSatMap
      split_ifs with hwf
      · simp only [boolsOf, List.length_map]
        have hstrN : encodeCnf (SATStr.cnfOf x) = strBits x := encodeCnf_parseTotal _ (strBits_bit x) hwf
        have h1 := encodeCnf_naeCnf_length x.length (SATStr.cnfOf x)
        have h2 := length_le_encodeCnf_length (SATStr.cnfOf x)
        rw [hstrN, strBits_length] at h1 h2
        have hmul := Nat.mul_le_mul_right (x.length + 3) h2
        omega
      · simp
    have hsz1 : encodable.size (naeSatMap x) ≤ 2 * (naeSatMap x).length := size_le_two_mul_length _
    have hsz2 : x.length ≤ encodable.size x := length_le_size x
    have hsq : (encodable.size x + 1) ^ 2 ≤ (encodable.size x + 1) ^ (D + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

noncomputable def naeSatPolyLang : PolyTimeComputableLang naeSatMap where
  c := naeSatCmd
  encodeIn := certState
  decodeOut := fun s => boolsOf (State.get s 0)
  cost_bound := naeSatCmd_cost.choose
  cost_bound_poly := naeSatCmd_cost.choose_spec.1
  cost_bound_mono := naeSatCmd_cost.choose_spec.2.1
  encBound := id
  encBound_poly := inOPoly_id
  encBound_mono := fun _ _ h => h
  encodeIn_size := fun x => by rw [State.size_certState]; exact length_le_size x
  computes := fun x => by
    rw [naeSatCmd_get0]
    exact boolsOf_strBits (naeSatMap x)
  cost_le := naeSatCmd_cost.choose_spec.2.2.1
  output_size_le := naeSatCmd_cost.choose_spec.2.2.2
  enc_bit := fun x => by
    intro reg hreg z hz
    simp only [certState, List.mem_singleton] at hreg
    subst hreg
    exact strBits_bit x z hz
  regBound := 26
  usesBelow := naeSatCmd_usesBelow
  width_le := fun x => by simp [certState]
  decode_agree := fun x m => by
    have hagr : AgreeBelow 26 (certState x ++ List.replicate m []) (certState x) := fun r _ =>
      State.get_append_replicate_nil (certState x) m r
    have hev := Cmd.eval_agree naeSatCmd 26 naeSatCmd_usesBelow hagr
    rw [hev 0 (by omega)]

end PvsNP.Units.m3_sat_to_naesat_aux

theorem PvsNP.Units.m3_sat_to_naesat :
    CookLevin.reducesPoly SATStr
      (fun x => ∃ a : assgn, ∀ C ∈ SATStr.cnfOf x,
        C.any (evalLiteral a) = true ∧ C.any (fun l => !evalLiteral a l) = true) := by
  obtain ⟨t, M, ht, hM, h1, hcomp⟩ :=
    PvsNP.Units.m3_sat_to_naesat_aux.naeSatPolyLang.toMachine
      (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨PvsNP.Units.m3_sat_to_naesat_aux.naeSatMap, t, M, ht, hM, h1, hcomp,
    PvsNP.Units.m3_sat_to_naesat_aux.naeSatMap_iff⟩
