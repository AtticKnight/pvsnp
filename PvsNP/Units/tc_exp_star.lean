import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_padded_test_exp
import PvsNP.Units.tc_closure_star_p

namespace PvsNP.Units.tc_exp_star

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cptE {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Stretched chunk encoding and 7-state transducer -/

def chunk (T : ℕ) (b : Bool) : List Bool :=
  [false, false, true, b, true] ++ List.replicate T true

def stretch (T : ℕ) (w : List Bool) : List Bool :=
  w.flatMap (chunk T)

theorem stretch_nil (T : ℕ) : stretch T [] = [] := rfl

theorem stretch_cons (T : ℕ) (b : Bool) (w : List Bool) :
    stretch T (b :: w) = chunk T b ++ stretch T w := rfl

theorem stretch_append (T : ℕ) (w₁ w₂ : List Bool) :
    stretch T (w₁ ++ w₂) = stretch T w₁ ++ stretch T w₂ :=
  List.flatMap_append

theorem stretch_flatten (T : ℕ) (S : List (List Bool)) :
    stretch T S.flatten = (S.map (stretch T)).flatten := by
  induction S with
  | nil => rfl
  | cons w S ih =>
    simp only [List.flatten_cons, List.map_cons, stretch_append, ih]

theorem chunk_length (T : ℕ) (b : Bool) : (chunk T b).length = T + 5 := by
  simp [chunk]

theorem stretch_length (T : ℕ) (w : List Bool) :
    (stretch T w).length = w.length * (T + 5) := by
  induction w with
  | nil => simp [stretch]
  | cons b w ih =>
    rw [stretch_cons, List.length_append, chunk_length, ih, List.length_cons, Nat.succ_mul]
    omega

inductive Q : Type
  | qStart | qF1 | qF2 | qT1 | qB | qRun | qDead
  deriving DecidableEq

instance : Fintype Q :=
  Fintype.ofList [.qStart, .qF1, .qF2, .qT1, .qB, .qRun, .qDead]
    (fun q => by cases q <;> simp)

def stepQ : Q → Bool → Q
  | .qStart, false => .qF1
  | .qStart, true  => .qDead
  | .qF1,    false => .qF2
  | .qF1,    true  => .qDead
  | .qF2,    true  => .qT1
  | .qF2,    false => .qDead
  | .qT1,    _     => .qB
  | .qB,     true  => .qRun
  | .qB,     false => .qDead
  | .qRun,   true  => .qRun
  | .qRun,   false => .qF1
  | .qDead,  _     => .qDead

def emitQ : Q → Bool → Option Bool
  | .qT1, b => some b
  | _,    _ => none

def accQ : Q → Bool
  | .qStart => true
  | .qRun   => true
  | _       => false

def validD (q : Q) (b : Bool) : Q × Option Bool := (stepQ q b, none)
def validFin (q : Q) : Option Bool := some (accQ q)

def extractD (q : Q) (b : Bool) : Q × Option Bool := (stepQ q b, emitQ q b)
def extractFin (_ : Q) : Option Bool := none

def runState : Q → List Bool → Q
  | q, [] => q
  | q, b :: s => runState (stepQ q b) s

def valid (s : List Bool) : Bool := accQ (runState .qStart s)

def extract (s : List Bool) : List Bool := fstRun extractD extractFin .qStart s

theorem validD_run (q : Q) (s : List Bool) :
    fstRun validD validFin q s = [accQ (runState q s)] := by
  induction s generalizing q with
  | nil => rfl
  | cons b s ih =>
    simpa [fstRun, validD, runState] using ih (stepQ q b)

theorem cpt_valid :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer valid :=
  fst_polyTime (fun x : List Bool => x) Computability.encodeBool valid validD validFin .qStart
    (fun s => by simpa [valid, Computability.encodeBool] using (validD_run .qStart s).symm)

theorem cpt_extract :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) extract :=
  fst_polyTime _ _ _ extractD extractFin .qStart (fun _ => rfl)

theorem runState_append (q : Q) (s₁ s₂ : List Bool) :
    runState q (s₁ ++ s₂) = runState (runState q s₁) s₂ := by
  induction s₁ generalizing q with
  | nil => rfl
  | cons b s₁ ih => exact ih (stepQ q b)

theorem extract_append_aux (q : Q) (s₁ s₂ : List Bool) :
    fstRun extractD extractFin q (s₁ ++ s₂) =
      fstRun extractD extractFin q s₁ ++ fstRun extractD extractFin (runState q s₁) s₂ := by
  induction s₁ generalizing q with
  | nil => rfl
  | cons b s₁ ih =>
    simp only [List.cons_append, fstRun, extractD, runState, ih, List.append_assoc]

theorem runState_qDead (s : List Bool) : runState .qDead s = .qDead := by
  induction s with
  | nil => rfl
  | cons b s ih => exact ih

theorem runState_acc_eq {q : Q} (hq : accQ q = true) {s : List Bool} (hs : valid s = true) :
    accQ (runState q s) = true ∧ fstRun extractD extractFin q s = extract s := by
  cases q with
  | qStart => exact ⟨hs, rfl⟩
  | qRun =>
    cases s with
    | nil => exact ⟨rfl, rfl⟩
    | cons b r =>
      cases b with
      | false =>
        exact ⟨hs, rfl⟩
      | true =>
        have hfalse : valid (true :: r) = false := by
          simp [valid, runState, stepQ, runState_qDead, accQ]
        rw [hfalse] at hs
        cases hs
  | qF1 => simp [accQ] at hq
  | qF2 => simp [accQ] at hq
  | qT1 => simp [accQ] at hq
  | qB => simp [accQ] at hq
  | qDead => simp [accQ] at hq

theorem extract_flatten (S : List (List Bool)) (hS : ∀ s ∈ S, valid s = true) :
    valid S.flatten = true ∧ extract S.flatten = (S.map extract).flatten := by
  induction S with
  | nil => exact ⟨rfl, rfl⟩
  | cons s S ih =>
    have hs : valid s = true := hS s (by simp)
    have hrest := ih (fun t ht => hS t (by simp [ht]))
    have h1 := runState_acc_eq hs hrest.1
    refine ⟨?_, ?_⟩
    · simp only [List.flatten_cons, valid, runState_append]
      exact h1.1
    · simp only [List.flatten_cons, List.map_cons, extract, extract_append_aux]
      rw [h1.2, ← hrest.2]

theorem runState_rep_true (T : ℕ) : runState .qRun (List.replicate T true) = .qRun := by
  induction T with
  | zero => rfl
  | succ T ih => exact ih

theorem extract_rep_true (T : ℕ) :
    fstRun extractD extractFin .qRun (List.replicate T true) = [] := by
  induction T with
  | zero => rfl
  | succ T ih => exact ih

theorem chunk_action {q : Q} (hq : accQ q = true) (T : ℕ) (b : Bool) :
    runState q (chunk T b) = .qRun ∧ fstRun extractD extractFin q (chunk T b) = [b] := by
  cases q with
  | qStart =>
    simp [chunk, runState, fstRun, extractD, stepQ, emitQ, runState_rep_true, extract_rep_true]
  | qRun =>
    simp [chunk, runState, fstRun, extractD, stepQ, emitQ, runState_rep_true, extract_rep_true]
  | qF1 => simp [accQ] at hq
  | qF2 => simp [accQ] at hq
  | qT1 => simp [accQ] at hq
  | qB => simp [accQ] at hq
  | qDead => simp [accQ] at hq

theorem stretch_action {q : Q} (hq : accQ q = true) (T : ℕ) (w : List Bool) :
    accQ (runState q (stretch T w)) = true ∧ fstRun extractD extractFin q (stretch T w) = w := by
  induction w generalizing q with
  | nil => exact ⟨hq, rfl⟩
  | cons b w ih =>
    rw [stretch_cons, runState_append, extract_append_aux]
    obtain ⟨h1, h2⟩ := chunk_action hq T b
    rw [h1, h2]
    obtain ⟨h3, h4⟩ := ih (q := .qRun) rfl
    exact ⟨h3, by simp [h4]⟩

theorem valid_stretch (T : ℕ) (w : List Bool) : valid (stretch T w) = true :=
  (stretch_action (q := .qStart) rfl T w).1

theorem extract_stretch (T : ℕ) (w : List Bool) : extract (stretch T w) = w :=
  (stretch_action (q := .qStart) rfl T w).2

/-! ### Polynomial-time computation of `stretch T x` from `1^T 0 x` -/

def headBitD : Bool → Bool → Bool × Option Bool
  | false, true  => (true, some true)
  | false, false => (true, none)
  | true,  _     => (true, none)

def headBitFlag (l : List Bool) : List Bool :=
  fstRun headBitD (fun _ => none) false l

theorem headBitD_true (l : List Bool) : fstRun headBitD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

theorem headBitFlag_cons (b : Bool) (l : List Bool) :
    headBitFlag (b :: l) = if b then [true] else [] := by
  cases b <;> simp [headBitFlag, fstRun, headBitD, headBitD_true]

theorem cpt_headBitFlag :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headBitFlag :=
  fst_polyTime _ _ _ headBitD (fun _ => none) false (fun _ => rfl)

def chunkHead (l : List Bool) : List Bool :=
  ([false, false, true] ++ sel (headBitFlag l) [false] [true]) ++ [true]

theorem chunkHead_cons (b : Bool) (l : List Bool) :
    chunkHead (b :: l) = [false, false, true, b, true] := by
  cases b <;> simp [chunkHead, headBitFlag_cons, sel]

theorem chunkHead_length (l : List Bool) : (chunkHead l).length = 5 := by
  unfold chunkHead
  cases headBitFlag l <;> simp [sel]

theorem cpt_chunkHead :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) chunkHead :=
  cpt_app2 (cpt_app2 (cpt_const [false, false, true])
    (cpt_sel cpt_headBitFlag (cpt_const [false]) (cpt_const [true]))) (cpt_const [true])

def stStep (s : List Bool) : List Bool :=
  sel (unpairB (unpairB s).2).1
    s
    (pairB (unpairB s).1
      (pairB (unpairB (unpairB s).2).1.tail
        (((unpairB (unpairB s).2).2 ++ chunkHead (unpairB (unpairB s).2).1) ++ (unpairB s).1)))

theorem cpt_stStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stStep := by
  have hpad := cpt_unpairB1
  have hrest := cpt_unpairB2
  have hremX := cpt_unpairB1_1 hrest
  have hout := cpt_unpairB2_1 hrest
  have hch := cpt_comp hremX cpt_chunkHead
  have hnext := cpt_pairB2 hpad
    (cpt_pairB2 (cpt_tail1 hremX) (cpt_app2 (cpt_app2 hout hch) hpad))
  exact cpt_sel hremX cpt_id hnext

theorem unpairB_dropWhile_nil (s : List Bool) (h : s.dropWhile id = []) :
    (unpairB s).1 = [] ∧ (unpairB s).2 = [] := by
  simp [unpairB, h]

theorem unpairB_len_strict (s : List Bool) (h : s.dropWhile id ≠ []) :
    2 * (unpairB s).1.length + (unpairB s).2.length + 1 ≤ s.length := by
  have hlen : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have htail : (s.dropWhile id).tail.length + 1 = (s.dropWhile id).length := by
    cases hd : s.dropWhile id with
    | nil => exact absurd hd h
    | cons a l => simp
  have h1 : (unpairB s).1.length = min (s.takeWhile id).length (s.dropWhile id).tail.length := by
    simp [unpairB, List.length_take]
  have h2 : (unpairB s).2.length = (s.dropWhile id).tail.length - (s.takeWhile id).length := by
    simp only [unpairB, List.length_drop]
  omega

theorem unpairB_fst_le (s : List Bool) : (unpairB s).1.length ≤ s.length := by
  have hlen : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have h1 : (unpairB s).1.length ≤ (s.takeWhile id).length := by
    simp [unpairB, List.length_take]
  omega

def stMeasure (s : List Bool) : ℕ := (unpairB s).1.length + 5

theorem stMeasure_step (y : List Bool) : stMeasure (stStep y) ≤ stMeasure y := by
  unfold stStep
  by_cases hrem : (unpairB (unpairB y).2).1 = []
  · simp [sel, hrem]
  · simp only [sel, hrem, ite_false, stMeasure, unpairB_pairB]
    exact le_rfl

theorem stStep_length (y : List Bool) : (stStep y).length ≤ y.length + stMeasure y := by
  unfold stStep
  by_cases hrem : (unpairB (unpairB y).2).1 = []
  · simp only [sel, hrem, ite_true]
    omega
  · simp only [sel, hrem, ite_false]
    have hrest_dw : (unpairB y).2.dropWhile id ≠ [] := by
      intro h0
      exact hrem (unpairB_dropWhile_nil _ h0).1
    have hrest_ne : (unpairB y).2 ≠ [] := by
      intro h0
      rw [h0] at hrest_dw
      exact hrest_dw rfl
    have hy_dw : y.dropWhile id ≠ [] := by
      intro h0
      exact hrest_ne (unpairB_dropWhile_nil _ h0).2
    have h1 := unpairB_len_strict y hy_dw
    have h2 := unpairB_len_strict (unpairB y).2 hrest_dw
    have htail : (unpairB (unpairB y).2).1.tail.length + 1 = (unpairB (unpairB y).2).1.length := by
      cases hq : (unpairB (unpairB y).2).1 with
      | nil => exact absurd hq hrem
      | cons a l => simp
    have hch := chunkHead_length (unpairB (unpairB y).2).1
    rw [pairB_length, pairB_length, List.length_append, List.length_append, hch]
    unfold stMeasure
    omega

theorem stMeasure_bound (y : List Bool) : stMeasure y ≤ 5 * y.length + 5 := by
  have := unpairB_fst_le y
  unfold stMeasure
  omega

theorem stStep_cons (T : ℕ) (b : Bool) (w out : List Bool) :
    stStep (pairB (List.replicate T true) (pairB (b :: w) out)) =
      pairB (List.replicate T true) (pairB w (out ++ chunk T b)) := by
  simp only [stStep, unpairB_pairB, sel, List.cons_ne_nil, ite_false, List.tail_cons,
    chunkHead_cons, chunk, List.append_assoc]

theorem stStep_iter (T : ℕ) (w out : List Bool) :
    stStep^[w.length] (pairB (List.replicate T true) (pairB w out)) =
      pairB (List.replicate T true) (pairB [] (out ++ stretch T w)) := by
  induction w generalizing out with
  | nil => simp [stretch]
  | cons b w ih =>
    simp only [List.length_cons, Function.iterate_succ_apply]
    rw [stStep_cons, ih (out ++ chunk T b), stretch_cons, List.append_assoc]

def stretchPad (p : List Bool) : List Bool :=
  (unpairB (unpairB (stStep^[(dropN p).length] (pairB (hd p) (pairB (dropN p) [])))).2).2

theorem cpt_stretchPad :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stretchPad := by
  have hIter := cpt_iterB stStep cpt_stStep stMeasure 5 stMeasure_step stStep_length stMeasure_bound
  have hArg := cpt_pairB2 (cpt_pairB2 cpt_hd (cpt_pairB2 cpt_dropN (cpt_const []))) cpt_dropN
  exact cptE (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_comp hArg hIter))) (fun p => by
    simp [stretchPad, unpairB_pairB])

theorem stretchPad_spec (T : ℕ) (x : List Bool) :
    stretchPad (List.replicate T true ++ false :: x) = stretch T x := by
  have h1 : hd (List.replicate T true ++ false :: x) = List.replicate T true := hd_un T x
  have h2 : dropN (List.replicate T true ++ false :: x) = x := dropN_un T x
  simp only [stretchPad, h1, h2, stStep_iter, unpairB_pairB, List.nil_append]

/-! ### Simulator language in P and equivalence under Kleene star -/

def simPred (c : Code) (d : ℕ) (s : List Bool) : Bool :=
  valid s && V (pairB (encCode c) (pairB (extract s) (un (d * s.length + d))), [])

theorem cpt_simPred (c : Code) (d : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (simPred c d) := by
  have hclk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => un (d * s.length + d)) := by
    have h1 := L055 (Polynomial.C d * Polynomial.X + Polynomial.C d)
    exact cptE h1 (fun s => by simp [un])
  have hV : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool =>
        V (pairB (encCode c) (pairB (extract s) (un (d * s.length + d))), [])) :=
    cpt_comp (cpt_pair (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 cpt_extract hclk))
      (cpt_const [])) (cpt_V cpt_sstep)
  exact PvsNP.Units.m2_bool_combine_polytime.ptc_and cpt_valid hV

theorem lift_exp_bound (k n : ℕ) : 2 ^ (n ^ k) + k ≤ 2 ^ (n ^ (k + 1)) + (k + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases k with
    | zero => norm_num
    | succ k => simp
  · have h1 : n ^ k ≤ n ^ (k + 1) := Nat.pow_le_pow_right hn (Nat.le_succ k)
    have h2 : 2 ^ (n ^ k) ≤ 2 ^ (n ^ (k + 1)) := Nat.pow_le_pow_right (by norm_num) h1
    omega

theorem length_le_flatten {w : List Bool} {S : List (List Bool)} (hw : w ∈ S) :
    w.length ≤ S.flatten.length := by
  induction S with
  | nil => cases hw
  | cons a S ih =>
    simp only [List.mem_cons] at hw
    simp only [List.flatten_cons, List.length_append]
    rcases hw with rfl | hw
    · omega
    · have := ih hw
      omega

theorem main :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ KStar.kstar L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k₀, f, M, hf, htime₀⟩
  let K : ℕ := k₀ + 1
  have htime : ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ K) + K :=
    fun n => (htime₀ n).trans (lift_exp_bound k₀ n)
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  let Lsim : Language Bool := {s : List Bool | simPred c d s = true}
  have hLsimP : Lsim ∈ PvsNP.P := ⟨simPred c d, cpt_simPred c d, fun _ => Iff.rfl⟩
  obtain ⟨hStar, hhStar, hStarMem⟩ := PvsNP.Units.tc_closure_star_p Lsim hLsimP
  have hSound : ∀ s : List Bool, s ∈ Lsim → valid s = true ∧ extract s ∈ L := by
    intro s hs
    have hsp : simPred c d s = true := hs
    simp only [simPred, Bool.and_eq_true] at hsp
    obtain ⟨hval, hV⟩ := hsp
    refine ⟨hval, ?_⟩
    rw [V_spec] at hV
    have hcw1 : c.outputsWithin ((extract s).map (fun b => cond b 1 0)) (d * s.length + d) [1] := by
      simpa using hV.2
    have hev : (flip bind (Turing.TM2.step M.tm.m))^[((M.outputsFun (extract s)).steps)]
        (some (Turing.initList M.tm ((extract s).map M.inputAlphabet.invFun))) =
        some (Turing.haltList M.tm [M.outputAlphabet.invFun (f (extract s))]) :=
      (M.outputsFun (extract s)).evals_in_steps
    have hcw2 := hc (extract s) (f (extract s)) (M.outputsFun (extract s)).steps hev
    have h1 := Code.outputsWithin_mono c _
      (le_max_left (d * s.length + d) (d * (M.outputsFun (extract s)).steps + d)) _ hcw1
    have h2 := Code.outputsWithin_mono c _
      (le_max_right (d * s.length + d) (d * (M.outputsFun (extract s)).steps + d)) _ hcw2
    have heq : [1] = [bitCode (f (extract s))] := h1.2.symm.trans h2.2
    cases hfx : f (extract s) with
    | false =>
      rw [hfx] at heq
      simp [bitCode] at heq
    | true =>
      exact (hf (extract s)).mpr hfx
  have hComp : ∀ (T : ℕ) (w : List Bool), w ∈ L → w ≠ [] → 2 ^ (w.length ^ K) + K ≤ T →
      stretch T w ∈ Lsim := by
    intro T w hwL hwne hT
    have hfx : f w = true := (hf w).mp hwL
    have hwpos : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hwne
      | cons _ _ => simp
    have hlen : T ≤ (stretch T w).length := by
      rw [stretch_length]
      have : 1 * (T + 5) ≤ w.length * (T + 5) := Nat.mul_le_mul_right (T + 5) hwpos
      omega
    have hsteps : (M.outputsFun w).steps ≤ (stretch T w).length := by
      have h1 : (M.outputsFun w).steps ≤ M.time w.length := (M.outputsFun w).steps_le_m
      exact h1.trans ((htime w.length).trans (hT.trans hlen))
    have hle_steps : d * (M.outputsFun w).steps + d ≤ d * (stretch T w).length + d := by
      have := Nat.mul_le_mul_left d hsteps
      omega
    have hev : (flip bind (Turing.TM2.step M.tm.m))^[((M.outputsFun w).steps)]
        (some (Turing.initList M.tm (w.map M.inputAlphabet.invFun))) =
        some (Turing.haltList M.tm [M.outputAlphabet.invFun (f w)]) :=
      (M.outputsFun w).evals_in_steps
    have hcw := Code.outputsWithin_mono c _ hle_steps _ (hc w (f w) (M.outputsFun w).steps hev)
    rw [hfx] at hcw
    have hcw1 : c.outputsWithin (w.map (fun b => cond b 1 0)) (d * (stretch T w).length + d) [1] := by
      simpa [bitCode] using hcw
    have hV : V (pairB (encCode c) (pairB w (un (d * (stretch T w).length + d))), []) = true := by
      rw [V_spec]
      refine ⟨by simp, ?_⟩
      simpa using hcw1
    show simPred c d (stretch T w) = true
    simp only [simPred, valid_stretch, extract_stretch, hV, Bool.and_self]
  have hEquiv : ∀ x : List Bool,
      x ∈ KStar.kstar L ↔ stretch (2 ^ (x.length ^ K) + K) x ∈ KStar.kstar Lsim := by
    intro x
    set T := 2 ^ (x.length ^ K) + K
    constructor
    · intro hx
      obtain ⟨S, hxS, hS⟩ := Language.mem_kstar_iff_exists_nonempty.1 hx
      refine Language.mem_kstar.2 ⟨S.map (stretch T), ?_, ?_⟩
      · rw [← stretch_flatten, ← hxS]
      · intro s hs
        rw [List.mem_map] at hs
        obtain ⟨w, hwS, rfl⟩ := hs
        obtain ⟨hwL, hwne⟩ := hS w hwS
        have hwle : w.length ≤ x.length := by
          rw [hxS]
          exact length_le_flatten hwS
        have hT : 2 ^ (w.length ^ K) + K ≤ T := by
          have h1 : w.length ^ K ≤ x.length ^ K := Nat.pow_le_pow_left hwle K
          have h2 : 2 ^ (w.length ^ K) ≤ 2 ^ (x.length ^ K) :=
            Nat.pow_le_pow_right (by norm_num) h1
          omega
        exact hComp T w hwL hwne hT
    · intro hs
      obtain ⟨S, hS_eq, hS⟩ := Language.mem_kstar.1 hs
      have hval : ∀ s ∈ S, valid s = true := fun s hs' => (hSound s (hS s hs')).1
      have hfl := (extract_flatten S hval).2
      refine Language.mem_kstar.2 ⟨S.map extract, ?_, ?_⟩
      · rw [← hfl, ← hS_eq, extract_stretch]
      · intro w hw
        rw [List.mem_map] at hw
        obtain ⟨s, hsS, rfl⟩ := hw
        exact (hSound s (hS s hsS)).2
  let hPair : List Bool × List Bool → Bool := fun p => hStar (stretchPad p.1)
  have hhPair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer hPair :=
    cpt_comp (cpt_comp cpt_fst cpt_stretchPad) hhStar
  obtain ⟨j, M', hM'⟩ := PvsNP.Units.m2_padded_test_exp K
    (fun x : List Bool => x) (fun _ : List Bool => ([] : List Bool)) hPair
    cpt_id (cpt_const []) hhPair
  refine ⟨j, _, M', fun x => ?_, hM'⟩
  rw [hEquiv x, hStarMem]
  show hStar (stretch (2 ^ (x.length ^ K) + K) x) = true ↔
    hPair (List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x, []) = true
  simp only [hPair, stretchPad_spec]

end PvsNP.Units.tc_exp_star

theorem PvsNP.Units.tc_exp_star :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ KStar.kstar L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_star.main
