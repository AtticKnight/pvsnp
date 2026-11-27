import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_binary_shift_right_low

namespace PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tf_fun_pair_mul

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem unpairB_len_le (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  unfold unpairB
  dsimp only
  cases hd0 : s.dropWhile id with
  | nil => simp
  | cons b t =>
    rw [hd0] at hsplit
    have htake : (t.take (s.takeWhile id).length).length ≤ (s.takeWhile id).length :=
      List.length_take_le _ _
    have htd : (t.take (s.takeWhile id).length).length +
        (t.drop (s.takeWhile id).length).length = t.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.tail_cons, List.length_cons] at hsplit ⊢
    omega

def eqStep (s : List Bool) : List Bool :=
  let a := (unpairB s).1
  let s2 := (unpairB s).2
  let b := (unpairB s2).1
  let acc := (unpairB s2).2
  let neA := sel a [] [true]
  let neB := sel b [] [true]
  let sameNE := sel neA (sel neB [true] []) (sel neB [] [true])
  let hbA := headBit a
  let hbB := headBit b
  let sameHB := sel hbA (sel hbB [true] []) (sel hbB [] [true])
  let acc' := sel acc [] (sel sameNE [] (sel sameHB [] [true]))
  pairB a.tail (pairB b.tail acc')

private theorem sel_len_le_one (c x y : List Bool) (hx : x.length ≤ 1) (hy : y.length ≤ 1) :
    (sel c x y).length ≤ 1 := by
  by_cases h : c = [] <;> simp [sel, h, hx, hy]

theorem eqStep_length (s : List Bool) : (eqStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_len_le s
  have h2 := unpairB_len_le (unpairB s).2
  unfold eqStep
  dsimp only
  have hacc' : (sel (unpairB (unpairB s).2).2 []
      (sel (sel (sel (unpairB s).1 [] [true]) (sel (sel (unpairB (unpairB s).2).1 [] [true]) [true] [])
        (sel (sel (unpairB (unpairB s).2).1 [] [true]) [] [true])) []
      (sel (sel (headBit (unpairB s).1) (sel (headBit (unpairB (unpairB s).2).1) [true] [])
        (sel (headBit (unpairB (unpairB s).2).1) [] [true])) [] [true]))).length ≤ 1 :=
    sel_len_le_one _ _ _ (by simp) (sel_len_le_one _ _ _ (by simp) (sel_len_le_one _ _ _ (by simp) (by simp)))
  have ht1 : (unpairB s).1.tail.length ≤ (unpairB s).1.length := by simp
  have ht2 : (unpairB (unpairB s).2).1.tail.length ≤ (unpairB (unpairB s).2).1.length := by simp
  simp only [pairB_length]
  omega

theorem cpt_eqStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) eqStep := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hs2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hs2
  have hacc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hs2
  have hneA := cpt_sel ha (cpt_const []) (cpt_const [true])
  have hneB := cpt_sel hb (cpt_const []) (cpt_const [true])
  have hsameNE := cpt_sel hneA (cpt_sel hneB (cpt_const [true]) (cpt_const [])) (cpt_sel hneB (cpt_const []) (cpt_const [true]))
  have hhbA := cpt_comp ha cpt_headBit
  have hhbB := cpt_comp hb cpt_headBit
  have hsameHB := cpt_sel hhbA (cpt_sel hhbB (cpt_const [true]) (cpt_const [])) (cpt_sel hhbB (cpt_const []) (cpt_const [true]))
  have hacc' := cpt_sel hacc (cpt_const []) (cpt_sel hsameNE (cpt_const []) (cpt_sel hsameHB (cpt_const []) (cpt_const [true])))
  exact cpt_pairB2 (cpt_tail1 ha) (cpt_pairB2 (cpt_tail1 hb) hacc')

theorem eqStep_one (a b acc : List Bool) (hacc : acc = [true] ∨ acc = []) :
    eqStep (pairB a (pairB b acc)) =
      pairB a.tail (pairB b.tail (if acc = [true] ∧ a.take 1 = b.take 1 then [true] else [])) := by
  have hsameNE : sel (sel a [] [true]) (sel (sel b [] [true]) [true] [])
      (sel (sel b [] [true]) [] [true]) =
      if (a = [] ↔ b = []) then [true] else [] := by
    cases a <;> cases b <;> simp [sel]
  have hsameHB : sel (headBit a) (sel (headBit b) [true] []) (sel (headBit b) [] [true]) =
      if (headBit a = headBit b) then [true] else [] := by
    rw [headBit_eq a, headBit_eq b]
    cases a with
    | nil => cases b with | nil => simp [sel] | cons b0 _ => cases b0 <;> simp [sel]
    | cons a0 _ => cases a0 <;> cases b with | nil => simp [sel] | cons b0 _ => cases b0 <;> simp [sel]
  have hboth : sel (if (a = [] ↔ b = []) then [true] else []) []
      (sel (if headBit a = headBit b then [true] else []) [] [true]) =
      if a.take 1 = b.take 1 then [true] else [] := by
    rw [headBit_eq a, headBit_eq b]
    cases a with
    | nil => cases b with | nil => simp [sel] | cons b0 _ => cases b0 <;> simp [sel]
    | cons a0 _ => cases a0 <;> cases b with | nil => simp [sel] | cons b0 _ => cases b0 <;> simp [sel]
  unfold eqStep
  simp only [unpairB_pairB]
  rw [hsameNE, hsameHB, hboth]
  rcases hacc with rfl | rfl
  · by_cases h : a.take 1 = b.take 1 <;> simp [sel, h]
  · simp [sel]

theorem eqStep_iter : ∀ (k : ℕ) (a b acc : List Bool), (acc = [true] ∨ acc = []) →
    eqStep^[k] (pairB a (pairB b acc)) =
      pairB (a.drop k) (pairB (b.drop k) (if acc = [true] ∧ a.take k = b.take k then [true] else []))
  | 0, a, b, acc, hacc => by
    rcases hacc with rfl | rfl <;> simp
  | k + 1, a, b, acc, hacc => by
    rw [Function.iterate_succ_apply, eqStep_one a b acc hacc]
    have hacc' : (if acc = [true] ∧ a.take 1 = b.take 1 then [true] else []) = [true] ∨
        (if acc = [true] ∧ a.take 1 = b.take 1 then [true] else []) = [] := by
      split_ifs <;> simp
    rw [eqStep_iter k a.tail b.tail _ hacc']
    have ha_drop : a.tail.drop k = a.drop (k + 1) := by cases a <;> simp
    have hb_drop : b.tail.drop k = b.drop (k + 1) := by cases b <;> simp
    have htake : (a.take 1 = b.take 1 ∧ a.tail.take k = b.tail.take k) ↔ a.take (k + 1) = b.take (k + 1) := by
      cases a with
      | nil => cases b with | nil => simp | cons _ _ => simp
      | cons a0 t1 =>
        cases b with
        | nil => simp
        | cons b0 t2 =>
          simp only [List.take_succ_cons, List.tail_cons, List.cons.injEq]
          tauto
    rw [ha_drop, hb_drop]
    by_cases h1 : acc = [true] ∧ a.take 1 = b.take 1
    · rcases h1 with ⟨rfl, h12⟩
      have heq : (a.tail.take k = b.tail.take k) ↔ a.take (k + 1) = b.take (k + 1) := by
        rw [← htake]; exact ⟨fun h => ⟨h12, h⟩, fun h => h.2⟩
      simp [h12, heq]
    · have hne : ¬ (acc = [true] ∧ a.take (k + 1) = b.take (k + 1)) := by
        intro ⟨ha, ht⟩
        exact h1 ⟨ha, (htake.mpr ht).1⟩
      simp [h1, hne]

def eqFlag (a b : List Bool) : List Bool :=
  let init := pairB a (pairB b [true])
  (unpairB (unpairB (eqStep^[init.length] init)).2).2

theorem eqFlag_eq (a b : List Bool) : eqFlag a b = if a = b then [true] else [] := by
  unfold eqFlag
  dsimp only
  set init := pairB a (pairB b [true])
  rw [eqStep_iter init.length a b [true] (Or.inl rfl), unpairB_pairB, unpairB_pairB]
  have ha : a.length ≤ init.length := by simp [init, pairB_length]; omega
  have hb : b.length ≤ init.length := by simp [init, pairB_length]; omega
  rw [List.take_of_length_le ha, List.take_of_length_le hb]
  simp

theorem cpt_eqFlag {f g : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => eqFlag (f s) (g s)) := by
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (f s) (pairB (g s) [true])) :=
    cpt_pairB2 hf (cpt_pairB2 hg (cpt_const [true]))
  have hIter := cpt_iterGrow cpt_eqStep 3 eqStep_length hInit hInit
  exact cpt_unpairB2_1 (cpt_unpairB2_1 hIter)

def mulBits (a b : List Bool) : List Bool :=
  Nat.bits (val a * val b)

theorem cpt_mulBits {f g : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulBits (f s) (g s)) := by
  have hm : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) := by
    have h := PvsNP.Units.tf_fun_pair_mul
    change PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString _ at h
    unfold PvsNP.PolyTimeComputable PvsNP.encodeString at h
    rwa [← encodePair_eq]
  exact cptE' (cpt_comp (cpt_pair hf hg) hm) (fun _ => rfl)

def verList (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let w := (unpairB s).2
  let a := (unpairB w).1
  let b := (unpairB w).2
  let lhs := stripLSB (addB (mulBits a a) (false :: mulBits b b))
  let rhs := stripLSB x
  sel (eqFlag lhs rhs) [false] [true]

theorem cpt_verList :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) verList := by
  have hx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have ha := cpt_unpairB1_1 hw
  have hb := cpt_unpairB2_1 hw
  have ha2 := cpt_mulBits ha ha
  have hb2 := cpt_mulBits hb hb
  have h2b2 := cpt_cons1 false hb2
  have hsum := cpt_comp (cpt_pair ha2 h2b2) cpt_addB
  have hlhs := cpt_comp hsum cpt_stripLSB
  have hrhs := cpt_comp hx cpt_stripLSB
  exact cpt_sel (cpt_eqFlag hlhs hrhs) (cpt_const [false]) (cpt_const [true])

def verFun (p : List Bool × List Bool) : Bool :=
  (verList (pairB p.1 p.2) ++ []).all id

private theorem cpt_listToBool {g : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => (g (pairB p.1 p.2) ++ []).all id) := by
  have h1 : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s => (g s, ([] : List Bool))) :=
    cpt_pair hg (cpt_const [])
  have h2 : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (g (pairB p.1 p.2), ([] : List Bool))) :=
    cpt_comp cpt_pairB h1
  exact cpt_comp h2 allTrue_polyTime

theorem cpt_verFun :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer verFun :=
  cpt_listToBool cpt_verList

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  unfold val
  induction n using Nat.binaryRec with
  | zero => simp
  | bit b n ih =>
    cases b
    · by_cases hn : n = 0
      · subst hn; simp
      · rw [Nat.bits_append_bit _ _ (fun h => absurd h hn)]
        simp [Nat.ofDigits_cons, Nat.bit_val] at ih ⊢
        omega
    · rw [Nat.bits_append_bit _ _ (fun _ => by simp)]
      simp [Nat.ofDigits_cons, Nat.bit_val] at ih ⊢
      omega

theorem val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val_nil]
  | cons b t ih =>
    rw [val_cons, List.length_cons, Nat.pow_succ']
    cases b <;> simp <;> omega

theorem verFun_iff (x w : List Bool) :
    verFun (x, w) = true ↔
      (val (unpairB w).1) ^ 2 + 2 * (val (unpairB w).2) ^ 2 = val x := by
  unfold verFun verList
  dsimp only
  rw [unpairB_pairB, eqFlag_eq]
  have hlhs : val (stripLSB (addB (mulBits (unpairB w).1 (unpairB w).1)
      (false :: mulBits (unpairB w).2 (unpairB w).2))) =
      (val (unpairB w).1) ^ 2 + 2 * (val (unpairB w).2) ^ 2 := by
    rw [val_stripLSB, val_addB, val_cons, Bool.toNat_false, zero_add]
    simp only [mulBits, val_bits]
    ring
  have heq : stripLSB (addB (mulBits (unpairB w).1 (unpairB w).1)
      (false :: mulBits (unpairB w).2 (unpairB w).2)) = stripLSB x ↔
      (val (unpairB w).1) ^ 2 + 2 * (val (unpairB w).2) ^ 2 = val x := by
    constructor
    · intro h
      have hv := congrArg val h
      rw [hlhs, val_stripLSB] at hv
      exact hv
    · intro h
      rw [stripLSB_eq_bits, stripLSB_eq_bits, ← val_stripLSB (addB _ _), hlhs, h]
  by_cases h : stripLSB (addB (mulBits (unpairB w).1 (unpairB w).1)
      (false :: mulBits (unpairB w).2 (unpairB w).2)) = stripLSB x
  · simp [sel, h]
    exact heq.mp h
  · simp [sel, h]
    exact fun h' => h (heq.mpr h')

end PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux

theorem PvsNP.Units.tl_lang_sq_plus_two_sq_np : ({x : List Bool | ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  refine ⟨PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.verFun, 3 * Polynomial.X + 1,
    PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.cpt_verFun, fun x => ?_⟩
  have hpeval : (3 * Polynomial.X + 1).eval x.length = 3 * x.length + 1 := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hpeval]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB (Nat.bits a) (Nat.bits b), ?_, ?_⟩
    · have hlt := PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.val_lt_two_pow x
      have ha_lt : a < 2 ^ x.length := by
        have ha2 : a ≤ a ^ 2 := Nat.le_self_pow (by decide) a
        change a ^ 2 + 2 * b ^ 2 = PvsNP.Units.tf_fun_pair_mul.val x at hab
        omega
      have hb_lt : b < 2 ^ x.length := by
        have hb2 : b ≤ b ^ 2 := Nat.le_self_pow (by decide) b
        change a ^ 2 + 2 * b ^ 2 = PvsNP.Units.tf_fun_pair_mul.val x at hab
        omega
      have hla := PvsNP.Units.tf_fun_pair_mul.bits_length_le_of_lt x.length a ha_lt
      have hlb := PvsNP.Units.tf_fun_pair_mul.bits_length_le_of_lt x.length b hb_lt
      rw [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB_length]
      omega
    · rw [PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.verFun_iff,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
        PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.val_bits,
        PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.val_bits]
      exact hab
  · rintro ⟨w, _, hw⟩
    rw [PvsNP.Units.tl_lang_sq_plus_two_sq_np_aux.verFun_iff] at hw
    exact ⟨_, _, hw⟩
