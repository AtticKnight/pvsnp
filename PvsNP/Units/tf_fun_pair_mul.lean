import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime

namespace PvsNP.Units.tf_fun_pair_mul

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

def headBitD : Bool → Bool → Bool × Option Bool
  | false, true => (true, some true)
  | false, false => (true, none)
  | true, _ => (true, none)

def headBit (l : List Bool) : List Bool :=
  fstRun headBitD (fun _ => none) false l

theorem headBit_eq (l : List Bool) :
    headBit l = match l with | true :: _ => [true] | _ => [] := by
  have htrue : ∀ t : List Bool, fstRun headBitD (fun _ => none) true t = [] := by
    intro t; induction t with | nil => rfl | cons _ _ ih => simp [fstRun, headBitD, ih]
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [headBit, fstRun, headBitD, htrue]

theorem cpt_headBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headBit :=
  fst_polyTime _ _ _ headBitD (fun _ => none) false (fun _ => rfl)

def oddBitD : Bool → Bool → Bool × Option Bool
  | q, _ => (!q, none)

def oddBit (l : List Bool) : List Bool :=
  fstRun oddBitD (fun q => if q then some true else some false) false l

theorem oddBit_eq (l : List Bool) :
    oddBit l = if l.length % 2 = 1 then [true] else [false] := by
  have hgen : ∀ (q : Bool) (t : List Bool),
      fstRun oddBitD (fun q => if q then some true else some false) q t =
        if (t.length + (if q then 1 else 0)) % 2 = 1 then [true] else [false] := by
    intro q t
    induction t generalizing q with
    | nil => cases q <;> rfl
    | cons _ ts ih =>
      simp only [fstRun, oddBitD, ih, List.length_cons, Option.toList_none, List.nil_append]
      cases q
      · simp
      · have : ts.length % 2 = 1 ↔ (ts.length + 1 + 1) % 2 = 1 := by omega
        simp [this]
  exact hgen false l

theorem cpt_oddBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) oddBit :=
  fst_polyTime _ _ _ oddBitD (fun q => if q then some true else some false) false (fun _ => rfl)

def dropFalseD : Bool → Bool → Bool × Option Bool
  | false, false => (false, none)
  | false, true => (true, some true)
  | true, b => (true, some b)

def dropLeadingFalse (l : List Bool) : List Bool :=
  fstRun dropFalseD (fun _ => none) false l

theorem dropLeadingFalse_eq (l : List Bool) :
    dropLeadingFalse l = l.dropWhile (fun b => !b) := by
  have htrue : ∀ t : List Bool, fstRun dropFalseD (fun _ => none) true t = t := by
    intro t; induction t with | nil => rfl | cons b ts ih => simp [fstRun, dropFalseD, ih]
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simpa [dropLeadingFalse, fstRun, dropFalseD] using ih
    · simp [dropLeadingFalse, fstRun, dropFalseD, htrue]

theorem cpt_dropLeadingFalse :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropLeadingFalse :=
  fst_polyTime _ _ _ dropFalseD (fun _ => none) false (fun _ => rfl)

def stripLSB (l : List Bool) : List Bool :=
  (dropLeadingFalse l.reverse).reverse

theorem cptE {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_stripLSB :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stripLSB := by
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  exact cptE (cpt_comp (cpt_comp hRev cpt_dropLeadingFalse) hRev) (fun _ => rfl)

-- Binary addition step: state = pairB a (pairB b (pairB c acc))
def addStep (s : List Bool) : List Bool :=
  let a := (unpairB s).1
  let s2 := (unpairB s).2
  let b := (unpairB s2).1
  let s3 := (unpairB s2).2
  let c := (unpairB s3).1
  let acc := (unpairB s3).2
  let tot := headBit a ++ headBit b ++ c
  let c' := sel (leFlag [true, true] tot) [] [true]
  let outBit := oddBit tot
  pairB a.tail (pairB b.tail (pairB c' (outBit ++ acc)))

theorem cpt_addStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) addStep := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hs2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hs2
  have hs3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hs2
  have hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 hs3
  have hacc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 hs3
  have htot : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => headBit (unpairB s).1 ++ headBit (unpairB (unpairB s).2).1 ++
        (unpairB (unpairB (unpairB s).2).2).1) :=
    cpt_app2 (cpt_app2 (cpt_comp ha cpt_headBit) (cpt_comp hb cpt_headBit)) hc
  have hc' := cpt_sel (cpt_leFlag (cpt_const [true, true]) htot) (cpt_const []) (cpt_const [true])
  have hout := cpt_comp htot cpt_oddBit
  exact cpt_pairB2 (cpt_tail1 ha) (cpt_pairB2 (cpt_tail1 hb) (cpt_pairB2 hc' (cpt_app2 hout hacc)))

theorem addStep_length (s : List Bool) : (addStep s).length ≤ s.length + 12 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hc' : (sel (leFlag [true, true] (headBit (unpairB s).1 ++ headBit (unpairB (unpairB s).2).1 ++
      (unpairB (unpairB (unpairB s).2).2).1)) [] [true]).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  have hout : (oddBit (headBit (unpairB s).1 ++ headBit (unpairB (unpairB s).2).1 ++
      (unpairB (unpairB (unpairB s).2).2).1)).length = 1 := by
    rw [oddBit_eq]; split_ifs <;> rfl
  simp only [addStep, pairB_length, List.length_append, List.length_tail, hout]
  omega

def addB_raw (a b : List Bool) : List Bool :=
  (unpairB (unpairB (unpairB (addStep^[(a ++ b ++ [true]).length]
    (pairB a (pairB b (pairB [] []))))).2).2).2.reverse

def addB (a b : List Bool) : List Bool :=
  stripLSB (addB_raw a b)

theorem cpt_addB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => addB p.1 p.2) := by
  have ha : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.1) := cpt_fst
  have hb : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.2) := cpt_snd
  have hnil : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun _ : List Bool × List Bool => ([] : List Bool)) :=
    cpt_comp ha (cpt_const [])
  have hInit : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 (pairB p.2 (pairB [] []))) :=
    cpt_comp (cpt_pairG ha
      (cpt_comp (cpt_pairG hb (cpt_comp (cpt_pairG hnil hnil) cpt_pairB)) cpt_pairB)) cpt_pairB
  have hCnt : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.1 ++ p.2 ++ [true]) :=
    cpt_comp (cpt_pairG (cpt_comp (cpt_pairG ha hb) cpt_append)
      (cpt_comp ha (cpt_const [true]))) cpt_append
  obtain ⟨cAdd⟩ := cpt_addStep
  have hIter := Iter.iter_polyTime addStep cAdd 12 addStep_length
  have hRun := cpt_comp (cpt_pairG hInit hCnt) hIter
  have hAcc := cpt_comp hRun
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  exact cptE (cpt_comp (cpt_comp hAcc hRev) cpt_stripLSB) (fun _ => rfl)

-- Value semantics
def val (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits]

theorem val_append_false (l : List Bool) : val (l ++ [false]) = val l := by
  induction l with
  | nil => rfl
  | cons b t ih => simp [val_cons, ih]

theorem val_stripLSB (l : List Bool) : val (stripLSB l) = val l := by
  have hrev : ∀ r : List Bool, val (dropLeadingFalse r).reverse = val r.reverse := by
    intro r
    rw [dropLeadingFalse_eq]
    induction r with
    | nil => rfl
    | cons b t ih =>
      cases b
      · simp only [List.dropWhile_cons, Bool.not_false, ↓reduceIte, List.reverse_cons]
        rw [ih, val_append_false]
      · simp [List.dropWhile_cons]
  simpa [stripLSB] using hrev l.reverse

theorem val_reverse_acc (a b c : List Bool) (hc : c = [] ∨ c = [true])
    (acc : List Bool) (n : ℕ) (hn : n ≥ a.length + b.length + c.length) :
    let fin := addStep^[n] (pairB a (pairB b (pairB c acc)))
    val ((unpairB (unpairB (unpairB fin).2).2).2.reverse) =
      val acc.reverse + 2 ^ acc.length * (val a + val b + c.length) := by
  induction n generalizing a b c acc with
  | zero =>
    have ha : a = [] := by cases a <;> simp_all
    have hb : b = [] := by cases b <;> simp_all
    have hc0 : c = [] := by cases c <;> simp_all
    subst ha hb hc0
    simp [unpairB_pairB, val_nil]
  | succ k ih =>
    intro fin
    dsimp [fin]
    have hstep : addStep (pairB a (pairB b (pairB c acc))) =
        pairB a.tail (pairB b.tail (pairB
          (sel (leFlag [true, true] (headBit a ++ headBit b ++ c)) [] [true])
          (oddBit (headBit a ++ headBit b ++ c) ++ acc))) := by
      simp [addStep, unpairB_pairB]
    rw [hstep]
    by_cases hbase : a = [] ∧ b = [] ∧ c = []
    · obtain ⟨rfl, rfl, rfl⟩ := hbase
      simp only [List.tail_nil, headBit_eq, List.nil_append, oddBit_eq, List.length_nil,
        Nat.zero_mod, zero_ne_one, ↓reduceIte]
      have hc' : sel (leFlag [true, true] []) [] [true] = [] := by
        unfold sel leFlag; simp
      rw [hc']
      have hk : k ≥ ([] : List Bool).length + ([] : List Bool).length + ([] : List Bool).length := by simp
      have hrec := ih ([] : List Bool) ([] : List Bool) ([] : List Bool) (Or.inl rfl) ([false] ++ acc) hk
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        val_append_false, val_nil, List.length_nil, add_zero, mul_zero] at hrec ⊢
      exact hrec
    · let tot := headBit a ++ headBit b ++ c
      let c' := sel (leFlag [true, true] tot) [] [true]
      let outBit := oddBit tot
      have hc'_or : c' = [] ∨ c' = [true] := by
        dsimp [c']; unfold sel leFlag; split_ifs <;> simp
      have hba : (headBit a).length = (a.headD false).toNat := by
        rw [headBit_eq]; cases a with | nil => rfl | cons b _ => cases b <;> rfl
      have hbb : (headBit b).length = (b.headD false).toNat := by
        rw [headBit_eq]; cases b with | nil => rfl | cons b _ => cases b <;> rfl
      have htot_len : tot.length = (a.headD false).toNat + (b.headD false).toNat + c.length := by
        simp [tot, List.length_append, hba, hbb, Nat.add_assoc]
      have hc'_len : c'.length = tot.length / 2 := by
        dsimp [c']; unfold sel leFlag
        have hcle : c.length ≤ 1 := by rcases hc with rfl | rfl <;> simp
        have h1 : (a.headD false).toNat ≤ 1 := by cases a.headD false <;> simp
        have h2 : (b.headD false).toNat ≤ 1 := by cases b.headD false <;> simp
        by_cases h : [true, true].length ≤ tot.length
        · rw [if_pos h, if_neg (by simp)]; simp only [List.length_cons, List.length_nil] at h ⊢; omega
        · rw [if_neg h, if_pos rfl]; simp only [List.length_cons, List.length_nil] at h ⊢; omega
      have hk : k ≥ a.tail.length + b.tail.length + c'.length := by
        rw [hc'_len, htot_len]
        rcases a with _ | ⟨⟨⟩, ta⟩ <;> rcases b with _ | ⟨⟨⟩, tb⟩ <;>
          rcases hc with rfl | rfl <;> simp at hn hbase ⊢ <;> omega
      have hrec := ih a.tail b.tail c' hc'_or (outBit ++ acc) hk
      dsimp only at hrec
      rw [hrec]
      have hout_val : val outBit = tot.length % 2 := by
        simp only [outBit, oddBit_eq]
        split_ifs with h <;> simp [val_cons, val_nil] <;> omega
      have hout_len : outBit.length = 1 := by
        simp [outBit, oddBit_eq]; split_ifs <;> rfl
      have hrev_app : (outBit ++ acc).reverse = acc.reverse ++ outBit.reverse :=
        List.reverse_append
      have hout_rev : outBit.reverse = outBit := by
        simp [outBit, oddBit_eq]; split_ifs <;> rfl
      have hval_app : ∀ (x : List Bool) (d : Bool), val (x ++ [d]) = val x + 2 ^ x.length * d.toNat := by
        intro x d; induction x with
        | nil => simp [val_cons, val_nil]
        | cons u us ihu => simp [val_cons, ihu, pow_succ]; ring
      have hout_sing : ∃ d : Bool, outBit = [d] ∧ d.toNat = tot.length % 2 := by
        simp only [outBit, oddBit_eq]
        split_ifs with h
        · exact ⟨true, rfl, h.symm⟩
        · exact ⟨false, rfl, by change 0 = tot.length % 2; omega⟩
      obtain ⟨d, hd, hdn⟩ := hout_sing
      have hlen_d : ([d] ++ acc).length = acc.length + 1 := by simp
      rw [hrev_app, hout_rev, hd, hval_app, List.length_reverse, hdn, hlen_d, hc'_len]
      have hva : val a = (a.headD false).toNat + 2 * val a.tail := by
        cases a with | nil => rfl | cons u us => simp [val_cons]
      have hvb : val b = (b.headD false).toNat + 2 * val b.tail := by
        cases b with | nil => rfl | cons u us => simp [val_cons]
      rw [hva, hvb, htot_len]
      have hdiv : (a.headD false).toNat + (b.headD false).toNat + c.length =
          ((a.headD false).toNat + (b.headD false).toNat + c.length) % 2 +
          2 * (((a.headD false).toNat + (b.headD false).toNat + c.length) / 2) := by omega
      rw [pow_add, pow_one]
      have hlin : (a.headD false).toNat + 2 * val a.tail + ((b.headD false).toNat + 2 * val b.tail) + c.length =
          ((a.headD false).toNat + (b.headD false).toNat + c.length) % 2 +
          2 * (((a.headD false).toNat + (b.headD false).toNat + c.length) / 2) +
          2 * (val a.tail + val b.tail) := by omega
      rw [hlin]
      ring

theorem val_addB (a b : List Bool) : val (addB a b) = val a + val b := by
  dsimp [addB, addB_raw]
  rw [val_stripLSB]
  have h := val_reverse_acc a b [] (Or.inl rfl) [] (a ++ b ++ [true]).length
    (by simp [List.length_append])
  simpa [val_nil] using h

theorem dropWhile_append_nil {α : Type} (p : α → Bool) (r : List α) (x : α)
    (hr : r.dropWhile p = []) (hx : p x = true) : (r ++ [x]).dropWhile p = [] := by
  induction r with
  | nil => simp [hx]
  | cons u us ih =>
    by_cases h : p u = true
    · simp only [List.dropWhile_cons, h, ↓reduceIte] at hr
      simp only [List.cons_append, List.dropWhile_cons, h, ↓reduceIte]
      exact ih hr
    · simp [List.dropWhile_cons, h] at hr

theorem dropWhile_append_cons {α : Type} (p : α → Bool) (r : List α) (x : α)
    (hr : r.dropWhile p = [] → p x = false) :
    (r ++ [x]).dropWhile p = r.dropWhile p ++ [x] := by
  induction r with
  | nil => simp [hr rfl]
  | cons u us ih =>
    by_cases h : p u = true
    · simp only [List.cons_append, List.dropWhile_cons, h, ↓reduceIte]
      refine ih (fun h' => hr ?_)
      simp [List.dropWhile_cons, h, h']
    · simp [List.cons_append, List.dropWhile_cons, h]

theorem stripLSB_eq_bits (l : List Bool) : stripLSB l = Nat.bits (val l) := by
  have ht_false : ∀ m : List Bool, val m = 0 → m.reverse.dropWhile (fun x => !x) = [] := by
    intro m hm; induction m with
    | nil => rfl
    | cons u us ihu =>
      cases u
      · have hus : val us = 0 := by simp [val_cons] at hm; exact hm
        simp only [List.reverse_cons]
        exact dropWhile_append_nil _ _ _ (ihu hus) rfl
      · simp [val_cons] at hm
  have hgen : ∀ (n : ℕ) (l : List Bool), val l = n → stripLSB l = Nat.bits n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro l hl
      cases l with
      | nil =>
        simp [val_nil] at hl
        subst hl; rfl
      | cons b t =>
        by_cases h0 : val (b :: t) = 0
        · have hb : b = false := by
            cases b
            · rfl
            · simp [val_cons] at h0
          have ht : val t = 0 := by simp [val_cons, hb] at h0; exact h0
          have htf2 := dropWhile_append_nil (fun x => !x) t.reverse false (ht_false t ht) rfl
          simp only [stripLSB, dropLeadingFalse_eq, List.reverse_cons, hb, htf2, List.reverse_nil]
          rw [← hl, h0]; rfl
        · have hlt : val t < n := by
            rw [val_cons] at h0
            rw [← hl, val_cons]
            cases b <;> simp at h0 ⊢ <;> omega
          have hst := ih (val t) hlt t rfl
          have hbit : n = Nat.bit b (val t) := by
            rw [← hl, val_cons, Nat.bit_val]
            cases b <;> simp <;> omega
          rw [hbit, Nat.bits_append_bit (val t) b (fun hvt => by
            cases b
            · exfalso; simp [hvt, val_cons] at hl h0
            · rfl)]
          rw [← hst]
          simp only [stripLSB, dropLeadingFalse_eq, List.reverse_cons]
          have happ : (t.reverse ++ [b]).dropWhile (fun x => !x) =
              t.reverse.dropWhile (fun x => !x) ++ [b] := by
            refine dropWhile_append_cons (fun x => !x) t.reverse b (fun he => ?_)
            cases b
            · exfalso
              have ht0 : val t = 0 := by
                have hst' : stripLSB t = [] := by simp [stripLSB, dropLeadingFalse_eq, he]
                rw [← val_stripLSB t, hst']; rfl
              simp [val_cons, ht0] at h0
            · rfl
          simp [happ]
  exact hgen (val l) l rfl

theorem bits_length_le_of_lt (k n : ℕ) (hn : n < 2 ^ k) : (Nat.bits n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by omega
    simp [this]
  | succ k ih =>
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hdiv : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
      have hlen : (Nat.bits n).length = (Nat.bits (n / 2)).length + 1 := by
        conv_lhs => rw [← Nat.div_add_mod n 2]
        by_cases hmod : n % 2 = 0
        · have hn2 : n / 2 ≠ 0 := by omega
          rw [hmod, add_zero, Nat.bit0_bits _ hn2, List.length_cons]
        · have hmod1 : n % 2 = 1 := by omega
          rw [hmod1, Nat.bit1_bits, List.length_cons]
      rw [hlen]
      exact Nat.succ_le_succ (ih (n / 2) hdiv)

theorem addB_length (a b : List Bool) : (addB a b).length ≤ max a.length b.length + 1 := by
  have hv : val (addB a b) = val a + val b := val_addB a b
  have hbits : addB a b = Nat.bits (val (addB a b)) := by
    change stripLSB (addB_raw a b) = Nat.bits (val (stripLSB (addB_raw a b)))
    rw [val_stripLSB]
    exact stripLSB_eq_bits (addB_raw a b)
  rw [hv] at hbits
  have hbound : ∀ x : List Bool, val x < 2 ^ x.length := by
    intro x; induction x with
    | nil => simp [val_nil]
    | cons d ds ih =>
      rw [val_cons, List.length_cons, pow_succ]
      cases d <;> simp <;> omega
  have h1 := hbound a
  have h2 := hbound b
  have hlt : val a + val b < 2 ^ (max a.length b.length + 1) := by
    have ha : 2 ^ a.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hb : 2 ^ b.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    rw [pow_succ]
    omega
  rw [hbits]
  exact bits_length_le_of_lt _ _ hlt

-- Multiplication step: state = pairB rem_x (pairB shifted_y acc)
def mulStep (s : List Bool) : List Bool :=
  let rx := (unpairB s).1
  let s2 := (unpairB s).2
  let sy := (unpairB s2).1
  let acc := (unpairB s2).2
  let addend := sel (headBit rx) [] sy
  let acc' := addB acc addend
  let sy' := sel rx sy (false :: sy)
  pairB rx.tail (pairB sy' acc')

theorem cpt_mulStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mulStep := by
  have hrx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hs2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hsy : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hs2
  have hacc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hs2
  have haddend := cpt_sel (cpt_comp hrx cpt_headBit) (cpt_const []) hsy
  have hacc' := cpt_comp (cpt_pairG hacc haddend) cpt_addB
  have hsy' := cpt_sel hrx hsy (cpt_cons1 false hsy)
  exact cpt_pairB2 (cpt_tail1 hrx) (cpt_pairB2 hsy' hacc')

def mulM (s : List Bool) : ℕ :=
  6 * (2 * (unpairB s).1.length + (unpairB (unpairB s).2).1.length) + 12

theorem mulM_step (s : List Bool) : mulM (mulStep s) ≤ mulM s := by
  simp only [mulM, mulStep, unpairB_pairB]
  cases hrx : (unpairB s).1 with
  | nil =>
    have hsel : sel [] (unpairB (unpairB s).2).1 (false :: (unpairB (unpairB s).2).1) =
        (unpairB (unpairB s).2).1 := rfl
    simp [hsel]
  | cons b t =>
    have hsel : sel (b :: t) (unpairB (unpairB s).2).1 (false :: (unpairB (unpairB s).2).1) =
        false :: (unpairB (unpairB s).2).1 := by
      unfold sel; simp
    simp only [hsel, List.length_tail, List.length_cons]
    omega

theorem mulStep_length (s : List Bool) : (mulStep s).length ≤ s.length + mulM s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have hadd : (addB (unpairB (unpairB s).2).2
      (sel (headBit (unpairB s).1) [] (unpairB (unpairB s).2).1)).length ≤
      max (unpairB (unpairB s).2).2.length (unpairB (unpairB s).2).1.length + 1 := by
    have := addB_length (unpairB (unpairB s).2).2
      (sel (headBit (unpairB s).1) [] (unpairB (unpairB s).2).1)
    have hsel : (sel (headBit (unpairB s).1) [] (unpairB (unpairB s).2).1).length ≤
        (unpairB (unpairB s).2).1.length := by
      unfold sel; split_ifs <;> simp
    omega
  have hsy' : (sel (unpairB s).1 (unpairB (unpairB s).2).1
      (false :: (unpairB (unpairB s).2).1)).length ≤ (unpairB (unpairB s).2).1.length + 1 := by
    unfold sel; split_ifs <;> simp
  simp only [mulStep, pairB_length, List.length_tail, mulM]
  omega

theorem mulM_le (s : List Bool) : mulM s ≤ 18 * s.length + 18 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  simp only [mulM]
  omega

theorem val_mulStep_iter (rx sy acc : List Bool) :
    val (unpairB (unpairB (mulStep^[rx.length] (pairB rx (pairB sy acc)))).2).2 =
      val acc + val rx * val sy := by
  induction rx generalizing sy acc with
  | nil =>
    simp [unpairB_pairB, val_nil]
  | cons b t ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : mulStep (pairB (b :: t) (pairB sy acc)) =
        pairB t (pairB (false :: sy) (addB acc (if b then sy else []))) := by
      have h1 : sel (headBit (b :: t)) [] sy = if b then sy else [] := by
        rw [headBit_eq]; cases b <;> simp [sel]
      have h2 : sel (b :: t) sy (false :: sy) = false :: sy := by
        unfold sel; simp
      simp [mulStep, unpairB_pairB, h1, h2]
    rw [hstep, ih (false :: sy) (addB acc (if b then sy else [])), val_addB]
    have hsy : val (false :: sy) = 2 * val sy := by simp [val_cons]
    rw [hsy, val_cons]
    cases b <;> simp [val_nil] <;> ring

theorem encodePair_eq : PvsNP.encodePair = encodePair := by funext p; rfl

end PvsNP.Units.tf_fun_pair_mul

theorem PvsNP.Units.tf_fun_pair_mul :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  rw [PvsNP.Units.tf_fun_pair_mul.encodePair_eq]
  have hx : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.1) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_fst
  have hy : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.2) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_snd
  have hnil : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun _ : List Bool × List Bool => ([] : List Bool)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hx
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
  have hInit := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairG hx
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairG hy hnil)
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB))
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB
  have hIter := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_iterB
    PvsNP.Units.tf_fun_pair_mul.mulStep
    PvsNP.Units.tf_fun_pair_mul.cpt_mulStep
    PvsNP.Units.tf_fun_pair_mul.mulM 18
    PvsNP.Units.tf_fun_pair_mul.mulM_step
    PvsNP.Units.tf_fun_pair_mul.mulStep_length
    PvsNP.Units.tf_fun_pair_mul.mulM_le
  have hRun := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairG hInit hx)
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB)
    hIter
  have hAcc := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hRun
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2_1
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2)
  have hStrip := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hAcc
    PvsNP.Units.tf_fun_pair_mul.cpt_stripLSB
  refine PvsNP.Units.tf_fun_pair_mul.cptE hStrip ?_
  rintro ⟨x, y⟩
  simp only [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
  rw [PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits,
    PvsNP.Units.tf_fun_pair_mul.val_mulStep_iter x y [],
    PvsNP.Units.tf_fun_pair_mul.val_nil, zero_add]
  rfl
