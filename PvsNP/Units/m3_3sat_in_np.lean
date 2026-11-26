import Mathlib
import PvsNP.Defs
import CookLevin

/-!
# 3SAT is in NP (vendored model)

We reuse `SATStr.satStrBuild` to validate and normalize the input CNF into `CNF_STREAM`
(`encodeCnf (SATStr.cnfOf x)`) and `CLAUSE_TALLY`, then run a single linear pass `check3Sat`
over `CNF_STREAM` that checks whether every clause has at most 3 literals. If any clause has
4 or more literals, `badBranch` overwrites `CNF_STREAM` and `CLAUSE_TALLY` with the
unsatisfiable formula `botCnf = [[]]`. Composing with `EvalCnfSplit.certDecode` and
`EvalCnfTM.evalCnfDecidesLang` yields an `NPWitnessStr` for 3SAT, hence `CookLevin.inNP`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m3_3sat_in_np

open CookLevin.Lang EvalCnfCmd CnfWellFormed

/-- Literal-count registers for the 3-literal-per-clause check, above `SATStr`'s `0..24`. -/
def WL1 : Var := 25
def WL2 : Var := 26
def WL3 : Var := 27
def WOV : Var := 28

/-- Mathematical model of one step of the 3SAT clause-length scanner:
`(inLit, pending, clauseLen, overflow)`. -/
def scan3Step : Bool × Bool × Nat × Bool → Nat → Bool × Bool × Nat × Bool
  | (false, _, len, ov), cell =>
      if cell = 1 then
        (true, false, len + 1, ov || decide (3 ≤ len))
      else
        (false, false, 0, ov)
  | (true, false, len, ov), _ => (true, true, len, ov)
  | (true, true, len, ov), cell =>
      if cell = 1 then (true, true, len, ov) else (false, true, len, ov)

def scan3Run (l : List Nat) : Bool × Bool × Nat × Bool :=
  l.foldl scan3Step (false, false, 0, false)

def scan3Take (l : List Nat) (i : Nat) : Bool × Bool × Nat × Bool :=
  (l.take i).foldl scan3Step (false, false, 0, false)

theorem scan3Take_zero (l : List Nat) : scan3Take l 0 = (false, false, 0, false) := rfl

theorem scan3Take_length (l : List Nat) : scan3Take l l.length = scan3Run l := by
  rw [scan3Take, List.take_length]; rfl

theorem scan3Take_succ (l : List Nat) (i : Nat) (hi : i < l.length) :
    scan3Take l (i + 1) = scan3Step (scan3Take l i) l[i] := by
  rw [scan3Take, scan3Take, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem scan3_replicate_one (v len : Nat) (ov : Bool) :
    (List.replicate v 1).foldl scan3Step (true, true, len, ov) = (true, true, len, ov) := by
  induction v with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      show (List.replicate n 1).foldl scan3Step (scan3Step (true, true, len, ov) 1) = _
      rw [show scan3Step (true, true, len, ov) 1 = (true, true, len, ov) from rfl]
      exact ih

theorem scan3_encodeLit (l : literal) (p : Bool) (len : Nat) (ov : Bool) :
    (encodeLit l).foldl scan3Step (false, p, len, ov) =
      (false, true, len + 1, ov || decide (3 ≤ len)) := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).foldl scan3Step
      (false, p, len, ov) = (false, true, len + 1, ov || decide (3 ≤ len))
  rw [List.foldl_cons]
  rw [show scan3Step (false, p, len, ov) 1 =
      (true, false, len + 1, ov || decide (3 ≤ len)) from rfl]
  rw [List.foldl_cons]
  rw [show scan3Step (true, false, len + 1, ov || decide (3 ≤ len)) (if pol then 1 else 0) =
      (true, true, len + 1, ov || decide (3 ≤ len)) from rfl]
  rw [List.foldl_append, scan3_replicate_one]
  rfl

theorem scan3_clauseBody (C : clause) (p : Bool) (len : Nat) (ov : Bool) :
    (CnfSerialize.clauseBody C).foldl scan3Step (false, p, len, ov) =
      (false, p || !C.isEmpty, len + C.length, ov || (!C.isEmpty && decide (3 < len + C.length))) := by
  induction C generalizing p len ov with
  | nil =>
      simp [CnfSerialize.clauseBody]
  | cons l C ih =>
      rw [CnfSerialize.clauseBody_cons, List.foldl_append, scan3_encodeLit, ih]
      simp only [List.isEmpty_cons, Bool.not_false, Bool.or_true, Bool.true_or, Bool.true_and,
        List.length_cons]
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext (by ac_rfl) ?_))
      cases C with
      | nil =>
          simp only [List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.or_false, List.length_nil]
          by_cases h3 : 3 ≤ len
          · have h3' : 3 < len + (0 + 1) := by omega
            simp [h3, h3']
          · have h3' : ¬ (3 < len + (0 + 1)) := by omega
            simp [h3, h3']
      | cons l' C' =>
          simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.length_cons]
          by_cases h3 : 3 ≤ len
          · have h3' : 3 < len + (C'.length + 1 + 1) := by omega
            simp [h3, h3']
          · by_cases h4 : 3 < len + 1 + (C'.length + 1)
            · have h4' : 3 < len + (C'.length + 1 + 1) := by omega
              simp [h3, h4, h4']
            · have h4' : ¬ (3 < len + (C'.length + 1 + 1)) := by omega
              simp [h3, h4, h4']

theorem scan3_encodeClause (C : clause) (p : Bool) (ov : Bool) :
    (encodeClause C).foldl scan3Step (false, p, 0, ov) =
      (false, false, 0, ov || decide (3 < C.length)) := by
  rw [CnfSerialize.encodeClause_eq, List.foldl_append, scan3_clauseBody]
  simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil]
  cases C with
  | nil => rfl
  | cons l C' => rfl

theorem scan3_encodeCnf (N : cnf) (ov : Bool) :
    (encodeCnf N).foldl scan3Step (false, false, 0, ov) =
      (false, false, 0, ov || decide (∃ C ∈ N, 3 < C.length)) := by
  induction N generalizing ov with
  | nil => simp [encodeCnf]
  | cons C N ih =>
      show (encodeClause C ++ encodeCnf N).foldl scan3Step (false, false, 0, ov) = _
      rw [List.foldl_append, scan3_encodeClause, ih]
      simp only [List.mem_cons, exists_eq_or_imp, decide_eq_true_eq]
      by_cases hC : 3 < C.length <;> by_cases hN : ∃ C' ∈ N, 3 < C'.length <;>
        simp [hC, hN, Bool.or_assoc]

theorem scan3Run_encodeCnf_ov (N : cnf) :
    (scan3Run (encodeCnf N)).2.2.2 = false ↔ ∀ C ∈ N, C.length ≤ 3 := by
  unfold scan3Run
  rw [scan3_encodeCnf N false]
  simp only [Bool.false_or, decide_eq_false_iff_not, not_exists, not_and, Nat.not_lt]

/-- Increment the 3-literal counter `(WL1, WL2, WL3, WOV)`. -/
def incLitCmd : Cmd :=
  Cmd.ifBit WL1
    (Cmd.ifBit WL2
      (Cmd.ifBit WL3
        (Cmd.op (.clear WOV) ;; Cmd.op (.appendOne WOV))
        (Cmd.op (.appendOne WL3)))
      (Cmd.op (.appendOne WL2)))
    (Cmd.op (.appendOne WL1))

/-- One cell of the 3SAT clause-length scan. -/
def scan3Body : Cmd :=
  Cmd.op (.head SATStr.WHD SATStr.WCUR) ;;
  Cmd.op (.tail SATStr.WCUR SATStr.WCUR) ;;
  Cmd.ifBit SATStr.WSA
    (Cmd.ifBit SATStr.WSB
      (Cmd.ifBit SATStr.WHD
        (Cmd.op (.clear SATStr.WHD))
        (Cmd.op (.clear SATStr.WSA)))
      (Cmd.op (.clear SATStr.WSB) ;; Cmd.op (.appendOne SATStr.WSB)))
    (Cmd.ifBit SATStr.WHD
      (Cmd.op (.clear SATStr.WSA) ;; Cmd.op (.appendOne SATStr.WSA) ;; Cmd.op (.clear SATStr.WSB) ;;
        incLitCmd)
      (Cmd.op (.clear SATStr.WSB) ;;
        Cmd.op (.clear WL1) ;; Cmd.op (.clear WL2) ;; Cmd.op (.clear WL3)))

/-- Initialize the 3SAT scan from `CNF_STREAM`. -/
def check3Pre : Cmd :=
  Cmd.op (.copy SATStr.WCUR CNF_STREAM) ;;
  Cmd.op (.clear SATStr.WSA) ;;
  Cmd.op (.clear SATStr.WSB) ;;
  Cmd.op (.clear WL1) ;;
  Cmd.op (.clear WL2) ;;
  Cmd.op (.clear WL3) ;;
  Cmd.op (.clear WOV)

/-- Run the 3SAT scan over `CNF_STREAM`, and fall back to `badBranch` if any clause had > 3 literals. -/
def check3Sat : Cmd :=
  check3Pre ;;
  Cmd.forBnd SATStr.WIDX SATStr.WCUR scan3Body ;;
  Cmd.ifBit WOV SATStr.badBranch (Cmd.op (.clear SATStr.WHD))

def threeSatBuild : Cmd := SATStr.satStrBuild ;; check3Sat

def threeSatMfc : Cmd := threeSatBuild ;; EvalCnfSplit.certDecode

theorem incLitCmd_run (u : State) (len : Nat) (ov : Bool)
    (hu1 : State.get u WL1 = SATStr.flagOf (1 ≤ len))
    (hu2 : State.get u WL2 = SATStr.flagOf (2 ≤ len))
    (hu3 : State.get u WL3 = SATStr.flagOf (3 ≤ len))
    (huO : State.get u WOV = SATStr.flagOf ov) :
    State.get (incLitCmd.eval u) SATStr.WCUR = State.get u SATStr.WCUR
      ∧ State.get (incLitCmd.eval u) SATStr.WSA = State.get u SATStr.WSA
      ∧ State.get (incLitCmd.eval u) SATStr.WSB = State.get u SATStr.WSB
      ∧ State.get (incLitCmd.eval u) WL1 = SATStr.flagOf (1 ≤ len + 1)
      ∧ State.get (incLitCmd.eval u) WL2 = SATStr.flagOf (2 ≤ len + 1)
      ∧ State.get (incLitCmd.eval u) WL3 = SATStr.flagOf (3 ≤ len + 1)
      ∧ State.get (incLitCmd.eval u) WOV = SATStr.flagOf (ov || decide (3 ≤ len)) := by
  rcases len with _ | len
  · rw [incLitCmd, Cmd.eval_ifBit_false _ _ _ _ (by rw [hu1]; simp [SATStr.flagOf])]
    simp only [Cmd.eval_op, Op.eval]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ WL1 _ SATStr.WCUR (by decide)]
    · rw [State.get_set_ne _ WL1 _ SATStr.WSA (by decide)]
    · rw [State.get_set_ne _ WL1 _ SATStr.WSB (by decide)]
    · rw [State.get_set_eq, hu1]; rfl
    · rw [State.get_set_ne _ WL1 _ WL2 (by decide)]; exact hu2
    · rw [State.get_set_ne _ WL1 _ WL3 (by decide)]; exact hu3
    · rw [State.get_set_ne _ WL1 _ WOV (by decide), huO]; simp
  · rcases len with _ | len
    · rw [incLitCmd, Cmd.eval_ifBit_true _ _ _ _ (by rw [hu1]; rfl),
        Cmd.eval_ifBit_false _ _ _ _ (by rw [hu2]; simp [SATStr.flagOf])]
      simp only [Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ WL2 _ SATStr.WCUR (by decide)]
      · rw [State.get_set_ne _ WL2 _ SATStr.WSA (by decide)]
      · rw [State.get_set_ne _ WL2 _ SATStr.WSB (by decide)]
      · rw [State.get_set_ne _ WL2 _ WL1 (by decide)]; exact hu1
      · rw [State.get_set_eq, hu2]; rfl
      · rw [State.get_set_ne _ WL2 _ WL3 (by decide)]; exact hu3
      · rw [State.get_set_ne _ WL2 _ WOV (by decide), huO]; simp
    · rcases len with _ | len
      · rw [incLitCmd, Cmd.eval_ifBit_true _ _ _ _ (by rw [hu1]; rfl),
          Cmd.eval_ifBit_true _ _ _ _ (by rw [hu2]; rfl),
          Cmd.eval_ifBit_false _ _ _ _ (by rw [hu3]; simp [SATStr.flagOf])]
        simp only [Cmd.eval_op, Op.eval]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WL3 _ SATStr.WCUR (by decide)]
        · rw [State.get_set_ne _ WL3 _ SATStr.WSA (by decide)]
        · rw [State.get_set_ne _ WL3 _ SATStr.WSB (by decide)]
        · rw [State.get_set_ne _ WL3 _ WL1 (by decide)]; exact hu1
        · rw [State.get_set_ne _ WL3 _ WL2 (by decide)]; exact hu2
        · rw [State.get_set_eq, hu3]; rfl
        · rw [State.get_set_ne _ WL3 _ WOV (by decide), huO]; simp
      · rw [incLitCmd, Cmd.eval_ifBit_true _ _ _ _ (by rw [hu1]; rfl),
          Cmd.eval_ifBit_true _ _ _ _ (by rw [hu2]; rfl),
          Cmd.eval_ifBit_true _ _ _ _ (by rw [hu3]; rfl)]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
        have hge3 : 3 ≤ len + 3 := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WOV _ SATStr.WCUR (by decide),
            State.get_set_ne _ WOV _ SATStr.WCUR (by decide)]
        · rw [State.get_set_ne _ WOV _ SATStr.WSA (by decide),
            State.get_set_ne _ WOV _ SATStr.WSA (by decide)]
        · rw [State.get_set_ne _ WOV _ SATStr.WSB (by decide),
            State.get_set_ne _ WOV _ SATStr.WSB (by decide)]
        · rw [State.get_set_ne _ WOV _ WL1 (by decide),
            State.get_set_ne _ WOV _ WL1 (by decide), hu1]; simp [SATStr.flagOf]
        · rw [State.get_set_ne _ WOV _ WL2 (by decide),
            State.get_set_ne _ WOV _ WL2 (by decide), hu2]; simp [SATStr.flagOf]
        · rw [State.get_set_ne _ WOV _ WL3 (by decide),
            State.get_set_ne _ WOV _ WL3 (by decide), hu3]; simp [SATStr.flagOf]
        · rw [State.get_set_eq, State.get_set_eq]
          simp [SATStr.flagOf, hge3]

theorem scan3Body_run (l : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hC : State.get s SATStr.WCUR = l.drop i)
    (hA : State.get s SATStr.WSA = SATStr.flagOf (scan3Take l i).1)
    (hB : State.get s SATStr.WSB = SATStr.flagOf (scan3Take l i).2.1)
    (h1 : State.get s WL1 = SATStr.flagOf (1 ≤ (scan3Take l i).2.2.1))
    (h2 : State.get s WL2 = SATStr.flagOf (2 ≤ (scan3Take l i).2.2.1))
    (h3 : State.get s WL3 = SATStr.flagOf (3 ≤ (scan3Take l i).2.2.1))
    (hO : State.get s WOV = SATStr.flagOf (scan3Take l i).2.2.2) :
    State.get (scan3Body.eval s) SATStr.WCUR = l.drop (i + 1)
      ∧ State.get (scan3Body.eval s) SATStr.WSA = SATStr.flagOf (scan3Take l (i + 1)).1
      ∧ State.get (scan3Body.eval s) SATStr.WSB = SATStr.flagOf (scan3Take l (i + 1)).2.1
      ∧ State.get (scan3Body.eval s) WL1 = SATStr.flagOf (1 ≤ (scan3Take l (i + 1)).2.2.1)
      ∧ State.get (scan3Body.eval s) WL2 = SATStr.flagOf (2 ≤ (scan3Take l (i + 1)).2.2.1)
      ∧ State.get (scan3Body.eval s) WL3 = SATStr.flagOf (3 ≤ (scan3Take l (i + 1)).2.2.1)
      ∧ State.get (scan3Body.eval s) WOV = SATStr.flagOf (scan3Take l (i + 1)).2.2.2 := by
  have hcons : State.get s SATStr.WCUR = l[i] :: l.drop (i + 1) := by
    rw [hC, List.drop_eq_getElem_cons hi]
  have e1 : (Cmd.op (Op.head SATStr.WHD SATStr.WCUR)).eval s = s.set SATStr.WHD [l[i]] := by
    simp only [Cmd.eval_op, Op.eval, hcons]
  have hC1 : State.get (s.set SATStr.WHD [l[i]]) SATStr.WCUR = l[i] :: l.drop (i + 1) := by
    rw [State.get_set_ne s SATStr.WHD _ SATStr.WCUR (by decide)]; exact hcons
  have e2 : (Cmd.op (Op.tail SATStr.WCUR SATStr.WCUR)).eval (s.set SATStr.WHD [l[i]])
      = (s.set SATStr.WHD [l[i]]).set SATStr.WCUR (l.drop (i + 1)) := by
    simp only [Cmd.eval_op, Op.eval, hC1, List.tail_cons]
  rw [scan3Body, Cmd.eval_seq, e1, Cmd.eval_seq, e2]
  set t : State := (s.set SATStr.WHD [l[i]]).set SATStr.WCUR (l.drop (i + 1)) with ht
  have hT_C : State.get t SATStr.WCUR = l.drop (i + 1) := State.get_set_eq _ _ _
  have hT_HD : State.get t SATStr.WHD = [l[i]] := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WHD (by decide)]
    exact State.get_set_eq _ _ _
  have hT_A : State.get t SATStr.WSA = SATStr.flagOf (scan3Take l i).1 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WSA (by decide),
      State.get_set_ne _ SATStr.WHD _ SATStr.WSA (by decide)]
    exact hA
  have hT_B : State.get t SATStr.WSB = SATStr.flagOf (scan3Take l i).2.1 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ SATStr.WSB (by decide),
      State.get_set_ne _ SATStr.WHD _ SATStr.WSB (by decide)]
    exact hB
  have hT_1 : State.get t WL1 = SATStr.flagOf (1 ≤ (scan3Take l i).2.2.1) := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ WL1 (by decide),
      State.get_set_ne _ SATStr.WHD _ WL1 (by decide)]
    exact h1
  have hT_2 : State.get t WL2 = SATStr.flagOf (2 ≤ (scan3Take l i).2.2.1) := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ WL2 (by decide),
      State.get_set_ne _ SATStr.WHD _ WL2 (by decide)]
    exact h2
  have hT_3 : State.get t WL3 = SATStr.flagOf (3 ≤ (scan3Take l i).2.2.1) := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ WL3 (by decide),
      State.get_set_ne _ SATStr.WHD _ WL3 (by decide)]
    exact h3
  have hT_O : State.get t WOV = SATStr.flagOf (scan3Take l i).2.2.2 := by
    rw [ht, State.get_set_ne _ SATStr.WCUR _ WOV (by decide),
      State.get_set_ne _ SATStr.WHD _ WOV (by decide)]
    exact hO
  rw [scan3Take_succ l i hi]
  rcases hm : scan3Take l i with ⟨a, b, len, ov⟩
  rw [hm] at hT_A hT_B hT_1 hT_2 hT_3 hT_O
  by_cases hcell : l[i] = 1
  · have hHD : State.get t SATStr.WHD = [1] := by rw [hT_HD, hcell]
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl),
              Cmd.eval_ifBit_true _ _ _ _ hHD]
            simp only [Cmd.eval_op, Op.eval, scan3Step, hcell, if_pos]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ SATStr.WHD _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ SATStr.WHD _ SATStr.WSA (by decide)]; exact hT_A
            · rw [State.get_set_ne _ SATStr.WHD _ SATStr.WSB (by decide)]; exact hT_B
            · rw [State.get_set_ne _ SATStr.WHD _ WL1 (by decide)]; exact hT_1
            · rw [State.get_set_ne _ SATStr.WHD _ WL2 (by decide)]; exact hT_2
            · rw [State.get_set_ne _ SATStr.WHD _ WL3 (by decide)]; exact hT_3
            · rw [State.get_set_ne _ SATStr.WHD _ WOV (by decide)]; exact hT_O
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [SATStr.flagOf])]
            simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
              State.set_set, scan3Step]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]; exact hT_A
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [SATStr.flagOf]
            · rw [State.get_set_ne _ SATStr.WSB _ WL1 (by decide)]; exact hT_1
            · rw [State.get_set_ne _ SATStr.WSB _ WL2 (by decide)]; exact hT_2
            · rw [State.get_set_ne _ SATStr.WSB _ WL3 (by decide)]; exact hT_3
            · rw [State.get_set_ne _ SATStr.WSB _ WOV (by decide)]; exact hT_O
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [SATStr.flagOf]),
          Cmd.eval_ifBit_true _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
          State.set_set, scan3Step, hcell, if_pos]
        set u : State := (t.set SATStr.WSA ([] ++ [1])).set SATStr.WSB [] with hu
        have huC : State.get u SATStr.WCUR = l.drop (i + 1) := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide)]; exact hT_C
        have huA : State.get u SATStr.WSA = [1] := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide), State.get_set_eq]; rfl
        have huB : State.get u SATStr.WSB = [] := State.get_set_eq _ _ _
        have hu1 : State.get u WL1 = SATStr.flagOf (1 ≤ len) := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ WL1 (by decide),
            State.get_set_ne _ SATStr.WSA _ WL1 (by decide)]; exact hT_1
        have hu2 : State.get u WL2 = SATStr.flagOf (2 ≤ len) := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ WL2 (by decide),
            State.get_set_ne _ SATStr.WSA _ WL2 (by decide)]; exact hT_2
        have hu3 : State.get u WL3 = SATStr.flagOf (3 ≤ len) := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ WL3 (by decide),
            State.get_set_ne _ SATStr.WSA _ WL3 (by decide)]; exact hT_3
        have huO : State.get u WOV = SATStr.flagOf ov := by
          rw [hu, State.get_set_ne _ SATStr.WSB _ WOV (by decide),
            State.get_set_ne _ SATStr.WSA _ WOV (by decide)]; exact hT_O
        clear_value u
        obtain ⟨rC, rA, rB, r1, r2, r3, rO⟩ := incLitCmd_run u len ov hu1 hu2 hu3 huO
        exact ⟨rC.trans huC, rA.trans huA, rB.trans huB, r1, r2, r3, rO⟩
  · have hHD : State.get t SATStr.WHD ≠ [1] := by
      rw [hT_HD]; simpa using hcell
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl),
              Cmd.eval_ifBit_false _ _ _ _ hHD]
            simp only [Cmd.eval_op, Op.eval, scan3Step, if_neg hcell]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide)]; exact hT_C
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [SATStr.flagOf]
            · rw [State.get_set_ne _ SATStr.WSA _ SATStr.WSB (by decide)]; exact hT_B
            · rw [State.get_set_ne _ SATStr.WSA _ WL1 (by decide)]; exact hT_1
            · rw [State.get_set_ne _ SATStr.WSA _ WL2 (by decide)]; exact hT_2
            · rw [State.get_set_ne _ SATStr.WSA _ WL3 (by decide)]; exact hT_3
            · rw [State.get_set_ne _ SATStr.WSA _ WOV (by decide)]; exact hT_O
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [SATStr.flagOf])]
            simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
              State.set_set, scan3Step]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]; exact hT_A
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [SATStr.flagOf]
            · rw [State.get_set_ne _ SATStr.WSB _ WL1 (by decide)]; exact hT_1
            · rw [State.get_set_ne _ SATStr.WSB _ WL2 (by decide)]; exact hT_2
            · rw [State.get_set_ne _ SATStr.WSB _ WL3 (by decide)]; exact hT_3
            · rw [State.get_set_ne _ SATStr.WSB _ WOV (by decide)]; exact hT_O
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [SATStr.flagOf]),
          Cmd.eval_ifBit_false _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
          State.set_set, scan3Step, if_neg hcell]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WL3 _ SATStr.WCUR (by decide),
            State.get_set_ne _ WL2 _ SATStr.WCUR (by decide),
            State.get_set_ne _ WL1 _ SATStr.WCUR (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide)]
          exact hT_C
        · rw [State.get_set_ne _ WL3 _ SATStr.WSA (by decide),
            State.get_set_ne _ WL2 _ SATStr.WSA (by decide),
            State.get_set_ne _ WL1 _ SATStr.WSA (by decide),
            State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide)]
          exact hT_A
        · rw [State.get_set_ne _ WL3 _ SATStr.WSB (by decide),
            State.get_set_ne _ WL2 _ SATStr.WSB (by decide),
            State.get_set_ne _ WL1 _ SATStr.WSB (by decide),
            State.get_set_eq]; rfl
        · rw [State.get_set_ne _ WL3 _ WL1 (by decide),
            State.get_set_ne _ WL2 _ WL1 (by decide),
            State.get_set_eq]; rfl
        · rw [State.get_set_ne _ WL3 _ WL2 (by decide),
            State.get_set_eq]; rfl
        · rfl
        · rw [State.get_set_ne _ WL3 _ WOV (by decide),
            State.get_set_ne _ WL2 _ WOV (by decide),
            State.get_set_ne _ WL1 _ WOV (by decide),
            State.get_set_ne _ SATStr.WSB _ WOV (by decide)]
          exact hT_O

theorem scan3Loop_run (l : List Nat) (s : State)
    (hC : State.get s SATStr.WCUR = l)
    (hA : State.get s SATStr.WSA = [])
    (hB : State.get s SATStr.WSB = [])
    (h1 : State.get s WL1 = [])
    (h2 : State.get s WL2 = [])
    (h3 : State.get s WL3 = [])
    (hO : State.get s WOV = []) :
    State.get ((Cmd.forBnd SATStr.WIDX SATStr.WCUR scan3Body).eval s) WOV =
      SATStr.flagOf (scan3Run l).2.2.2 := by
  have hlen : (State.get s SATStr.WCUR).length = l.length := by rw [hC]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct scan3Body SATStr.WIDX l.length s
    (fun i st => State.get st SATStr.WCUR = l.drop i
      ∧ State.get st SATStr.WSA = SATStr.flagOf (scan3Take l i).1
      ∧ State.get st SATStr.WSB = SATStr.flagOf (scan3Take l i).2.1
      ∧ State.get st WL1 = SATStr.flagOf (1 ≤ (scan3Take l i).2.2.1)
      ∧ State.get st WL2 = SATStr.flagOf (2 ≤ (scan3Take l i).2.2.1)
      ∧ State.get st WL3 = SATStr.flagOf (3 ≤ (scan3Take l i).2.2.1)
      ∧ State.get st WOV = SATStr.flagOf (scan3Take l i).2.2.2)
    ⟨by simpa using hC, by rw [hA, scan3Take_zero]; rfl,
      by rw [hB, scan3Take_zero]; rfl, by rw [h1, scan3Take_zero]; rfl,
      by rw [h2, scan3Take_zero]; rfl, by rw [h3, scan3Take_zero]; rfl,
      by rw [hO, scan3Take_zero]; rfl⟩
    (by
      rintro i st hi ⟨gC, gA, gB, g1, g2, g3, gO⟩
      refine scan3Body_run l i hi _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WCUR (by decide)]; exact gC
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WSA (by decide)]; exact gA
      · rw [State.get_set_ne _ SATStr.WIDX _ SATStr.WSB (by decide)]; exact gB
      · rw [State.get_set_ne _ SATStr.WIDX _ WL1 (by decide)]; exact g1
      · rw [State.get_set_ne _ SATStr.WIDX _ WL2 (by decide)]; exact g2
      · rw [State.get_set_ne _ SATStr.WIDX _ WL3 (by decide)]; exact g3
      · rw [State.get_set_ne _ SATStr.WIDX _ WOV (by decide)]; exact gO)
  simp only [scan3Take_length] at key
  exact key.2.2.2.2.2.2

/-- The 3SAT CNF parsed from `x`: `cnfOf x` if every clause has `≤ 3` literals, else `botCnf`. -/
def cnf3Of (x : List Bool) : cnf :=
  if (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) then SATStr.cnfOf x else botCnf

theorem threeSatBuild_get (x c : List Bool) :
    State.get (threeSatBuild.eval (SATStr.strEIn (x, c))) OUTPUT = []
      ∧ State.get (threeSatBuild.eval (SATStr.strEIn (x, c))) CLAUSE_TALLY =
          List.replicate (cnf3Of x).length 1
      ∧ State.get (threeSatBuild.eval (SATStr.strEIn (x, c))) CNF_STREAM =
          encodeCnf (cnf3Of x)
      ∧ State.get (threeSatBuild.eval (SATStr.strEIn (x, c))) ASSGN = strBits c := by
  obtain ⟨h0, h1, h2, h3⟩ := SATStr.satStrBuild_get x c
  set s0 := SATStr.satStrBuild.eval (SATStr.strEIn (x, c)) with hs0
  rw [threeSatBuild, Cmd.eval_seq, ← hs0, check3Sat, Cmd.eval_seq, Cmd.eval_seq]
  -- evaluate check3Pre
  have hpre :
      State.get (check3Pre.eval s0) SATStr.WCUR = encodeCnf (SATStr.cnfOf x)
        ∧ State.get (check3Pre.eval s0) SATStr.WSA = []
        ∧ State.get (check3Pre.eval s0) SATStr.WSB = []
        ∧ State.get (check3Pre.eval s0) WL1 = []
        ∧ State.get (check3Pre.eval s0) WL2 = []
        ∧ State.get (check3Pre.eval s0) WL3 = []
        ∧ State.get (check3Pre.eval s0) WOV = []
        ∧ State.get (check3Pre.eval s0) OUTPUT = []
        ∧ State.get (check3Pre.eval s0) CLAUSE_TALLY = List.replicate (SATStr.cnfOf x).length 1
        ∧ State.get (check3Pre.eval s0) CNF_STREAM = encodeCnf (SATStr.cnfOf x)
        ∧ State.get (check3Pre.eval s0) ASSGN = strBits c := by
    rw [check3Pre]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ WOV _ SATStr.WCUR (by decide),
        State.get_set_ne _ WL3 _ SATStr.WCUR (by decide),
        State.get_set_ne _ WL2 _ SATStr.WCUR (by decide),
        State.get_set_ne _ WL1 _ SATStr.WCUR (by decide),
        State.get_set_ne _ SATStr.WSB _ SATStr.WCUR (by decide),
        State.get_set_ne _ SATStr.WSA _ SATStr.WCUR (by decide),
        State.get_set_eq]; exact h2
    · rw [State.get_set_ne _ WOV _ SATStr.WSA (by decide),
        State.get_set_ne _ WL3 _ SATStr.WSA (by decide),
        State.get_set_ne _ WL2 _ SATStr.WSA (by decide),
        State.get_set_ne _ WL1 _ SATStr.WSA (by decide),
        State.get_set_ne _ SATStr.WSB _ SATStr.WSA (by decide),
        State.get_set_eq]
    · rw [State.get_set_ne _ WOV _ SATStr.WSB (by decide),
        State.get_set_ne _ WL3 _ SATStr.WSB (by decide),
        State.get_set_ne _ WL2 _ SATStr.WSB (by decide),
        State.get_set_ne _ WL1 _ SATStr.WSB (by decide),
        State.get_set_eq]
    · rw [State.get_set_ne _ WOV _ WL1 (by decide),
        State.get_set_ne _ WL3 _ WL1 (by decide),
        State.get_set_ne _ WL2 _ WL1 (by decide),
        State.get_set_eq]
    · rw [State.get_set_ne _ WOV _ WL2 (by decide),
        State.get_set_ne _ WL3 _ WL2 (by decide),
        State.get_set_eq]
    · rw [State.get_set_ne _ WOV _ WL3 (by decide),
        State.get_set_eq]
    · rw [State.get_set_eq]
    · rw [State.get_set_ne _ WOV _ OUTPUT (by decide),
        State.get_set_ne _ WL3 _ OUTPUT (by decide),
        State.get_set_ne _ WL2 _ OUTPUT (by decide),
        State.get_set_ne _ WL1 _ OUTPUT (by decide),
        State.get_set_ne _ SATStr.WSB _ OUTPUT (by decide),
        State.get_set_ne _ SATStr.WSA _ OUTPUT (by decide),
        State.get_set_ne _ SATStr.WCUR _ OUTPUT (by decide)]; exact h0
    · rw [State.get_set_ne _ WOV _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ WL3 _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ WL2 _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ WL1 _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ SATStr.WSB _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ SATStr.WSA _ CLAUSE_TALLY (by decide),
        State.get_set_ne _ SATStr.WCUR _ CLAUSE_TALLY (by decide)]; exact h1
    · rw [State.get_set_ne _ WOV _ CNF_STREAM (by decide),
        State.get_set_ne _ WL3 _ CNF_STREAM (by decide),
        State.get_set_ne _ WL2 _ CNF_STREAM (by decide),
        State.get_set_ne _ WL1 _ CNF_STREAM (by decide),
        State.get_set_ne _ SATStr.WSB _ CNF_STREAM (by decide),
        State.get_set_ne _ SATStr.WSA _ CNF_STREAM (by decide),
        State.get_set_ne _ SATStr.WCUR _ CNF_STREAM (by decide)]; exact h2
    · rw [State.get_set_ne _ WOV _ ASSGN (by decide),
        State.get_set_ne _ WL3 _ ASSGN (by decide),
        State.get_set_ne _ WL2 _ ASSGN (by decide),
        State.get_set_ne _ WL1 _ ASSGN (by decide),
        State.get_set_ne _ SATStr.WSB _ ASSGN (by decide),
        State.get_set_ne _ SATStr.WSA _ ASSGN (by decide),
        State.get_set_ne _ SATStr.WCUR _ ASSGN (by decide)]; exact h3
  obtain ⟨pC, pA, pB, p1, p2, p3, pO, p0, pT, pS, pAS⟩ := hpre
  set s1 := (Cmd.forBnd SATStr.WIDX SATStr.WCUR scan3Body).eval (check3Pre.eval s0) with hs1
  have hs1_ov : State.get s1 WOV = SATStr.flagOf (scan3Run (encodeCnf (SATStr.cnfOf x))).2.2.2 :=
    scan3Loop_run (encodeCnf (SATStr.cnfOf x)) (check3Pre.eval s0) pC pA pB p1 p2 p3 pO
  have hframe : ∀ q : Var, q ∉ (Cmd.forBnd SATStr.WIDX SATStr.WCUR scan3Body).writes →
      State.get s1 q = State.get (check3Pre.eval s0) q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  have hs1_0 : State.get s1 OUTPUT = [] := by
    rw [hframe OUTPUT (by decide)]; exact p0
  have hs1_T : State.get s1 CLAUSE_TALLY = List.replicate (SATStr.cnfOf x).length 1 := by
    rw [hframe CLAUSE_TALLY (by decide)]; exact pT
  have hs1_S : State.get s1 CNF_STREAM = encodeCnf (SATStr.cnfOf x) := by
    rw [hframe CNF_STREAM (by decide)]; exact pS
  have hs1_AS : State.get s1 ASSGN = strBits c := by
    rw [hframe ASSGN (by decide)]; exact pAS
  have hbad : ∀ z : State, State.get (SATStr.badBranch.eval z) OUTPUT = State.get z OUTPUT
      ∧ State.get (SATStr.badBranch.eval z) CLAUSE_TALLY = [1]
      ∧ State.get (SATStr.badBranch.eval z) CNF_STREAM = [0]
      ∧ State.get (SATStr.badBranch.eval z) ASSGN = State.get z ASSGN := by
    intro z
    rw [SATStr.badBranch, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    simp only [Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
      State.get_set_ne _ CNF_STREAM _ CLAUSE_TALLY (by decide : CLAUSE_TALLY ≠ CNF_STREAM)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ CLAUSE_TALLY _ OUTPUT (by decide),
        State.get_set_ne _ CNF_STREAM _ OUTPUT (by decide)]
    · first | rfl | (rw [State.get_set_eq]; rfl)
    · rw [State.get_set_ne _ CLAUSE_TALLY _ CNF_STREAM (by decide), State.get_set_eq]; rfl
    · rw [State.get_set_ne _ CLAUSE_TALLY _ ASSGN (by decide),
        State.get_set_ne _ CNF_STREAM _ ASSGN (by decide)]
  by_cases h3sat : ∀ C ∈ SATStr.cnfOf x, C.length ≤ 3
  · have hov_f : (scan3Run (encodeCnf (SATStr.cnfOf x))).2.2.2 = false :=
      (scan3Run_encodeCnf_ov (SATStr.cnfOf x)).mpr h3sat
    have hs1_ov_f : State.get s1 WOV ≠ [1] := by
      rw [hs1_ov, hov_f]; simp [SATStr.flagOf]
    rw [Cmd.eval_ifBit_false _ _ _ _ hs1_ov_f, Cmd.eval_op, Op.eval]
    have hcnf3 : cnf3Of x = SATStr.cnfOf x := if_pos h3sat
    rw [hcnf3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ SATStr.WHD _ OUTPUT (by decide)]; exact hs1_0
    · rw [State.get_set_ne _ SATStr.WHD _ CLAUSE_TALLY (by decide)]; exact hs1_T
    · rw [State.get_set_ne _ SATStr.WHD _ CNF_STREAM (by decide)]; exact hs1_S
    · rw [State.get_set_ne _ SATStr.WHD _ ASSGN (by decide)]; exact hs1_AS
  · have hov_t : (scan3Run (encodeCnf (SATStr.cnfOf x))).2.2.2 = true := by
      cases h : (scan3Run (encodeCnf (SATStr.cnfOf x))).2.2.2
      · exact absurd ((scan3Run_encodeCnf_ov (SATStr.cnfOf x)).mp h) h3sat
      · rfl
    have hs1_ov_t : State.get s1 WOV = [1] := by
      rw [hs1_ov, hov_t]; rfl
    rw [Cmd.eval_ifBit_true _ _ _ _ hs1_ov_t]
    obtain ⟨b0, b1, b2, b3⟩ := hbad s1
    have hcnf3 : cnf3Of x = botCnf := if_neg h3sat
    rw [hcnf3]
    exact ⟨by rw [b0, hs1_0], by rw [b1]; rfl, by rw [b2]; rfl, by rw [b3, hs1_AS]⟩

theorem threeSatBuild_bridge (x c : List Bool) :
    AgreeBelow 19 (threeSatBuild.eval (SATStr.strEIn (x, c))) (EvalCnfSplit.satEIn (cnf3Of x, c)) := by
  obtain ⟨h0, h1, h2, h3⟩ := threeSatBuild_get x c
  have hframe : ∀ q : Var, q ∉ threeSatBuild.writes →
      State.get (threeSatBuild.eval (SATStr.strEIn (x, c))) q = State.get (SATStr.strEIn (x, c)) q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  intro r hr
  interval_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rw [hframe 4 (by decide)]; rfl
  · rw [hframe 5 (by decide)]; rfl
  · rw [hframe 6 (by decide)]; rfl
  · rw [hframe 7 (by decide)]; rfl
  · rw [hframe 8 (by decide)]; rfl
  · rw [hframe 9 (by decide)]; rfl
  · rw [hframe 10 (by decide)]; rfl
  · rw [hframe 11 (by decide)]; rfl
  · rw [hframe 12 (by decide)]; rfl
  · rw [hframe 13 (by decide)]; rfl
  · rw [hframe 14 (by decide)]; rfl
  · rw [hframe 15 (by decide)]; rfl
  · rw [hframe 16 (by decide)]; rfl
  · rw [hframe 17 (by decide)]; rfl
  · rw [hframe 18 (by decide)]; rfl

def g3Str (v : List Bool × List Bool) : cnf × assgn :=
  (cnf3Of v.1, EvalCnfSplit.decodeBits v.2)

theorem threeSatMfc_bridge (v : List Bool × List Bool) :
    AgreeBelow 16 (threeSatMfc.eval (SATStr.strEIn v)) (encodeState (g3Str v)) := by
  rcases v with ⟨x, c⟩
  have h1 : AgreeBelow 19 (EvalCnfSplit.certDecode.eval (threeSatBuild.eval (SATStr.strEIn (x, c))))
      (EvalCnfSplit.certDecode.eval (EvalCnfSplit.satEIn (cnf3Of x, c))) :=
    Cmd.eval_agree _ 19 EvalCnfSplit.certDecode_usesBelow (threeSatBuild_bridge x c)
  have h2 := EvalCnfSplit.certDecode_bridge (cnf3Of x, c)
  intro r hr
  rw [threeSatMfc, Cmd.eval_seq]
  exact (h1 r (by omega)).trans (h2 r hr)

theorem size_cnf3Of_le (x : List Bool) : encodable.size (cnf3Of x) ≤ encodable.size x + 1 := by
  by_cases h3 : ∀ C ∈ SATStr.cnfOf x, C.length ≤ 3
  · rw [cnf3Of, if_pos h3]
    exact SATStr.size_cnfOf_le x
  · rw [cnf3Of, if_neg h3, SATStr.size_botCnf]
    omega

theorem size_g3Str_le (v : List Bool × List Bool) :
    encodable.size (g3Str v) ≤ SATStr.gArg (encodable.size v) := by
  rcases v with ⟨x, c⟩
  have hx := size_cnf3Of_le x
  have hc := EvalCnfSplit.size_decodeBits_le c
  have hn : encodable.size ((x, c) : List Bool × List Bool)
      = encodable.size x + encodable.size c + 1 := rfl
  show encodable.size (cnf3Of x) + encodable.size (EvalCnfSplit.decodeBits c) + 1
      ≤ SATStr.gArg (encodable.size ((x, c) : List Bool × List Bool))
  rw [hn]
  show _ ≤ (encodable.size x + encodable.size c + 1) * (encodable.size x + encodable.size c + 1)
    + (encodable.size x + encodable.size c + 1) + 2
  nlinarith [Nat.zero_le (encodable.size x), Nat.zero_le (encodable.size c)]

def regs3 : Nat := 2 ^ 29 - 1

theorem threeSatMfc_chk : (threeSatMfc.chk regs3).1 = true := by decide

theorem threeSatMfc_usesBelow : Cmd.UsesBelow threeSatMfc 29 := by
  simp [threeSatMfc, threeSatBuild, SATStr.satStrBuild, SATStr.satStrPre, SATStr.satStrPostA,
    SATStr.satStrPostB, SATStr.badBranch, SATStr.scanBody, check3Sat, check3Pre, scan3Body,
    incLitCmd, EvalCnfSplit.certDecode, EvalCnfSplit.decodeBody, Cmd.UsesBelow, Op.UsesBelow,
    SATStr.WCUR, SATStr.WIDX, SATStr.WHD, SATStr.WSA, SATStr.WSB, SATStr.WTAL,
    WL1, WL2, WL3, WOV, EvalCnfSplit.DCUR, EvalCnfSplit.DIDX, EvalCnfSplit.DHD,
    OUTPUT, CLAUSE_TALLY, CNF_STREAM, ASSGN]

theorem threeSatMfc_cost : ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ v : List Bool × List Bool, threeSatMfc.cost (SATStr.strEIn v) ≤ budget (encodable.size v) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk threeSatMfc regs3 threeSatMfc_chk
  refine ⟨fun n => K * (n + 1) ^ (D + 1), ?_, ?_,
    fun v => hb (SATStr.strEIn v) _ (SATStr.strEIn_size_le v)⟩
  · refine inOPoly_mul (inOPoly_const K) ⟨D + 1, 2 ^ (D + 1), 1, ?_⟩
    intro n hn
    calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
  · exact fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

noncomputable def str3Bound : Nat → Nat :=
  fun n => threeSatMfc_cost.choose n + EvalCnfTM.timeBound (SATStr.gArg n) + 1

theorem str3Bound_poly : inOPoly str3Bound :=
  inOPoly_add (inOPoly_add threeSatMfc_cost.choose_spec.1
    (inOPoly_comp (f := SATStr.gArg) (g := EvalCnfTM.timeBound)
      SATStr.gArg_poly EvalCnfTM.timeBound_inOPoly)) (inOPoly_const 1)

theorem str3Bound_mono : monotonic str3Bound := by
  intro a b hab
  have h1 := threeSatMfc_cost.choose_spec.2.1 a b hab
  have h2 := EvalCnfTM.timeBound_monotonic _ _ (SATStr.gArg_mono a b hab)
  show _ + _ + 1 ≤ _ + _ + 1
  omega

theorem le_str3Bound (n : Nat) : n ≤ str3Bound n := by
  have h1 : n ≤ EvalCnfTM.timeBound (SATStr.gArg n) :=
    le_trans (SATStr.le_gArg n) (le_trans (SATStr.le_timeBound (SATStr.gArg n))
      (EvalCnfTM.timeBound_monotonic _ _ (Nat.le_refl _)))
  show n ≤ _ + _ + 1
  omega

noncomputable def str3PrecomposeData :
    EvalCnfTM.evalCnfDecidesLang.FreePrecomposeData g3Str where
  mfc := threeSatMfc
  eIn := SATStr.strEIn
  newBound := str3Bound
  newBound_poly := str3Bound_poly
  newBound_mono := str3Bound_mono
  bridge := threeSatMfc_bridge
  encodeIn_size := fun v => le_trans (SATStr.strEIn_size_le v) (le_str3Bound _)
  cost_bound := fun v => by
    have h1 : threeSatMfc.cost (SATStr.strEIn v) ≤ threeSatMfc_cost.choose (encodable.size v) :=
      threeSatMfc_cost.choose_spec.2.2 v
    have h2 : evalCnfCmd.cost (threeSatMfc.eval (SATStr.strEIn v))
        = evalCnfCmd.cost (encodeState (g3Str v)) :=
      Cmd.cost_agree _ 16 evalCnfCmd_usesBelow (threeSatMfc_bridge v)
    have h3 : evalCnfCmd.cost (encodeState (g3Str v))
        ≤ EvalCnfTM.timeBound (SATStr.gArg (encodable.size v)) :=
      le_trans (evalCnfCmd_cost_bound _)
        (EvalCnfTM.timeBound_monotonic _ _ (size_g3Str_le v))
    show (threeSatMfc ;; evalCnfCmd).cost (SATStr.strEIn v) ≤ str3Bound (encodable.size v)
    rw [Cmd.cost_seq, h2]
    show 1 + threeSatMfc.cost (SATStr.strEIn v) + _
        ≤ threeSatMfc_cost.choose _ + EvalCnfTM.timeBound (SATStr.gArg _) + 1
    omega
  enc_bit := SATStr.strEIn_bit
  regBound := 29
  usesBelow := ⟨threeSatMfc_usesBelow, Cmd.UsesBelow_mono (by omega) evalCnfCmd_usesBelow⟩
  width_le := fun v => by
    rcases v with ⟨x, c⟩
    show (SATStr.strEIn (x, c)).length ≤ 29
    rw [SATStr.strEIn_lit]
    simp

def threeSatRel (x c : List Bool) : Prop :=
  satisfiesCnf (EvalCnfSplit.decodeBits c) (cnf3Of x)

noncomputable def threeSatVerifier :
    DecidesLang (fun v : List Bool × List Bool => threeSatRel v.1 v.2) str3Bound :=
  EvalCnfTM.evalCnfDecidesLang.precomposeFree g3Str str3PrecomposeData

theorem threeSatRel_correct :
    polyCertRel (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) threeSatRel := by
  obtain ⟨R⟩ := EvalCnfSplit.satRel_correct
  refine ⟨⟨fun n => R.bound (n + 1), ?_, ?_, ?_, ?_⟩⟩
  · rintro x c h
    by_cases h3 : ∀ C ∈ SATStr.cnfOf x, C.length ≤ 3
    · rw [threeSatRel, cnf3Of, if_pos h3] at h
      exact ⟨h3, ⟨EvalCnfSplit.decodeBits c, h⟩⟩
    · have hbot : cnf3Of x = botCnf := if_neg h3
      have h' : satisfiesCnf (EvalCnfSplit.decodeBits c) botCnf := by
        rw [threeSatRel, hbot] at h; exact h
      exact absurd ⟨EvalCnfSplit.decodeBits c, h'⟩ not_sat_botCnf
  · rintro x ⟨h3, hx⟩
    obtain ⟨c, hrel, hsize⟩ := R.complete hx
    refine ⟨c, ?_, le_trans hsize (R.bound_mono _ _ (SATStr.size_cnfOf_le x))⟩
    rw [threeSatRel, cnf3Of, if_pos h3]
    exact hrel
  · exact inOPoly_comp (f := fun n => n + 1) (g := R.bound)
      (inOPoly_add inOPoly_id (inOPoly_const 1)) R.bound_poly
  · exact fun a b hab => R.bound_mono _ _ (by omega)

noncomputable def threeSatWitness :
    CookLevin.Lang.NPWitnessStr (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) where
  rel := threeSatRel
  dBound := str3Bound
  dBound_poly := str3Bound_poly
  dBound_mono := str3Bound_mono
  verifier := threeSatVerifier
  rel_correct := threeSatRel_correct
  encX := certState
  encodeIn_eq := fun _ _ => rfl
  xWidth := 1
  encX_width := fun _ => rfl
  encX_size := fun x => by
    have h : State.size (certState x) = x.length := CookLevin.Lang.State.size_certState x
    have h2 : x.length ≤ encodable.size x := CookLevin.length_le_size x
    have h3 := le_str3Bound (encodable.size x)
    omega
  sizeLB := fun n => 2 * n
  sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
  encX_sizeLB := fun x => by
    rw [CookLevin.Lang.State.size_certState]
    exact CookLevin.size_le_two_mul_length x
  encX_canonical := fun _ => rfl

end PvsNP.Units.m3_3sat_in_np

/-- 3SAT is in NP in the vendored Cook–Levin model. -/
theorem PvsNP.Units.m3_3sat_in_np :
    CookLevin.inNP (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) :=
  CookLevin.Lang.inNPCmd_inNP ⟨PvsNP.Units.m3_3sat_in_np.threeSatWitness⟩
