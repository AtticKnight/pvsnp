import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_binary_le_polytime

set_option autoImplicit false

namespace PvsNP.Units.tr_rel_val_power_of

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem encodePair_eq : PvsNP.encodePair = encodePair := by
  funext ⟨a, b⟩
  simp only [PvsNP.encodePair, encodePair, Computability.encodingProd,
    Computability.encodingList, id_eq]

def headBitD : Bool → Bool → Bool × Option Bool
  | false, true => (true, some true)
  | false, false => (true, none)
  | true, _ => (true, none)

def headBit (l : List Bool) : List Bool :=
  fstRun headBitD (fun _ => none) false l

theorem headBit_true_run (t : List Bool) : fstRun headBitD (fun _ => none) true t = [] := by
  induction t with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem headBit_eq (l : List Bool) :
    headBit l = match l with | true :: _ => [true] | _ => [] := by
  cases l with
  | nil => rfl
  | cons b t =>
    cases b with
    | false => exact headBit_true_run t
    | true =>
      change true :: fstRun headBitD (fun _ => none) true t = [true]
      rw [headBit_true_run]

theorem headBit_length (l : List Bool) : (headBit l).length = (l.headD false).toNat := by
  rw [headBit_eq]
  cases l with
  | nil => rfl
  | cons b _ => cases b <;> rfl

theorem cpt_headBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headBit :=
  fst_polyTime _ _ _ headBitD (fun _ => none) false (fun _ => rfl)

def oddBitD : Bool → Bool → Bool × Option Bool
  | q, _ => (!q, none)

def oddBit (l : List Bool) : List Bool :=
  fstRun oddBitD (fun q => if q then some true else some false) false l

theorem oddBit_gen (q : Bool) (t : List Bool) :
    fstRun oddBitD (fun q => if q then some true else some false) q t =
      [decide ((t.length + q.toNat) % 2 = 1)] := by
  induction t generalizing q with
  | nil => cases q <;> rfl
  | cons _ ts ih =>
    change fstRun oddBitD (fun q => if q then some true else some false) (!q) ts = _
    rw [ih (!q)]
    congr 1
    cases q with
    | false =>
      simp only [Bool.not_false, Bool.toNat_true, Bool.toNat_false, List.length_cons, Nat.add_zero]
    | true =>
      simp only [Bool.not_true, Bool.toNat_false, Bool.toNat_true, List.length_cons, Nat.add_zero]
      have hmod : ts.length % 2 = (ts.length + 1 + 1) % 2 := by omega
      rw [hmod]

theorem oddBit_eq (l : List Bool) : oddBit l = [decide (l.length % 2 = 1)] := by
  simpa only [oddBit, Bool.toNat_false, Nat.add_zero] using oddBit_gen false l

theorem cpt_oddBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) oddBit :=
  fst_polyTime _ _ _ oddBitD (fun q => if q then some true else some false) false (fun _ => rfl)

def dropFalseD : Bool → Bool → Bool × Option Bool
  | false, false => (false, none)
  | false, true => (true, some true)
  | true, b => (true, some b)

def dropLeadingFalse (l : List Bool) : List Bool :=
  fstRun dropFalseD (fun _ => none) false l

theorem dropLeadingFalse_true_run (t : List Bool) :
    fstRun dropFalseD (fun _ => none) true t = t := by
  induction t with
  | nil => rfl
  | cons b ts ih =>
    change b :: fstRun dropFalseD (fun _ => none) true ts = b :: ts
    rw [ih]

theorem dropLeadingFalse_nil : dropLeadingFalse [] = [] := rfl

theorem dropLeadingFalse_cons_false (t : List Bool) :
    dropLeadingFalse (false :: t) = dropLeadingFalse t := rfl

theorem dropLeadingFalse_cons_true (t : List Bool) :
    dropLeadingFalse (true :: t) = true :: t := by
  change true :: fstRun dropFalseD (fun _ => none) true t = true :: t
  rw [dropLeadingFalse_true_run]

theorem dropLeadingFalse_length (l : List Bool) : (dropLeadingFalse l).length ≤ l.length := by
  induction l with
  | nil => exact le_rfl
  | cons b t ih =>
    cases b with
    | false =>
      rw [dropLeadingFalse_cons_false, List.length_cons]
      omega
    | true =>
      rw [dropLeadingFalse_cons_true]

theorem cpt_dropLeadingFalse :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropLeadingFalse :=
  fst_polyTime _ _ _ dropFalseD (fun _ => none) false (fun _ => rfl)

def stripLSB (l : List Bool) : List Bool :=
  (dropLeadingFalse l.reverse).reverse

theorem stripLSB_length (l : List Bool) : (stripLSB l).length ≤ l.length := by
  rw [stripLSB, List.length_reverse]
  exact (dropLeadingFalse_length l.reverse).trans (by rw [List.length_reverse])

theorem cpt_stripLSB :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stripLSB := by
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have h1 := cpt_comp hRev cpt_dropLeadingFalse
  have h2 := cpt_comp h1 hRev
  exact cpt_congr h2 (fun _ => rfl)

def val (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := by
  simp only [val, List.map_cons, Nat.ofDigits, Nat.cast_id]

theorem val_head_tail (l : List Bool) : val l = (l.headD false).toNat + 2 * val l.tail := by
  cases l with
  | nil => rfl
  | cons b t => exact val_cons b t

theorem ofDigits_append_singleton (xs : List ℕ) (d : ℕ) :
    Nat.ofDigits (2 : ℕ) (xs ++ [d]) = Nat.ofDigits (2 : ℕ) xs + 2 ^ xs.length * d := by
  induction xs with
  | nil =>
    simp only [List.nil_append, List.length_nil, pow_zero, Nat.one_mul, Nat.ofDigits,
      Nat.cast_id, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  | cons a rest ih =>
    simp only [List.cons_append, Nat.ofDigits, Nat.cast_id, List.length_cons, ih, pow_succ]
    ring

theorem val_append_singleton (xs : List Bool) (d : Bool) :
    val (xs ++ [d]) = val xs + 2 ^ xs.length * d.toNat := by
  rw [val, List.map_append, List.map_singleton, ofDigits_append_singleton, List.length_map]
  rfl

theorem bits_val_append_true (xs : List Bool) :
    Nat.bits (val (xs ++ [true])) = xs ++ [true] := by
  induction xs with
  | nil => decide
  | cons b rest ih =>
    have hpos : 0 < val (rest ++ [true]) := by
      rw [val_append_singleton]
      have h1 : 1 ≤ 2 ^ rest.length := Nat.one_le_two_pow
      simp only [Bool.toNat_true, Nat.mul_one]
      omega
    have hne : val (rest ++ [true]) ≠ 0 := by omega
    have hcons : val ((b :: rest) ++ [true]) = Nat.bit b (val (rest ++ [true])) := by
      rw [List.cons_append, val_cons, Nat.bit_val]
      cases b with
      | false => simp only [Bool.toNat_false]; omega
      | true => simp only [Bool.toNat_true]; omega
    rw [hcons, Nat.bits_append_bit _ _ (fun h => absurd h hne), ih, List.cons_append]

theorem dropLeadingFalse_reverse_eq_bits (r : List Bool) :
    (dropLeadingFalse r).reverse = Nat.bits (val r.reverse) := by
  induction r with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | false =>
      rw [dropLeadingFalse_cons_false, ih, List.reverse_cons, val_append_singleton]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    | true =>
      rw [dropLeadingFalse_cons_true, List.reverse_cons, bits_val_append_true]

theorem stripLSB_eq_bits (l : List Bool) : stripLSB l = Nat.bits (val l) := by
  rw [stripLSB, dropLeadingFalse_reverse_eq_bits, List.reverse_reverse]

theorem val_dropLeadingFalse_reverse (r : List Bool) :
    val (dropLeadingFalse r).reverse = val r.reverse := by
  induction r with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | false =>
      rw [dropLeadingFalse_cons_false, ih, List.reverse_cons, val_append_singleton]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    | true =>
      rw [dropLeadingFalse_cons_true]

theorem val_stripLSB (l : List Bool) : val (stripLSB l) = val l := by
  rw [stripLSB, val_dropLeadingFalse_reverse, List.reverse_reverse]

theorem stripLSB_eq_nil_iff (l : List Bool) : stripLSB l = [] ↔ val l = 0 := by
  constructor
  · intro h
    rw [← val_stripLSB l, h]
    rfl
  · intro h
    rw [stripLSB_eq_bits, h]
    rfl

-- Binary subtraction step: state = pairB a (pairB b (pairB bor acc))
def subStep (s : List Bool) : List Bool :=
  let a := (unpairB s).1
  let s2 := (unpairB s).2
  let b := (unpairB s2).1
  let s3 := (unpairB s2).2
  let bor := (unpairB s3).1
  let acc := (unpairB s3).2
  let aBit := headBit a
  let bBit := headBit b
  let bor' := leFlag (aBit ++ [true]) (bBit ++ bor)
  let outBit := oddBit (aBit ++ bBit ++ bor)
  pairB a.tail (pairB b.tail (pairB bor' (outBit ++ acc)))

theorem cpt_subStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) subStep := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hs2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hs2
  have hs3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hs2
  have hbor : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 hs3
  have hacc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 hs3
  have haBit := cpt_comp ha cpt_headBit
  have hbBit := cpt_comp hb cpt_headBit
  have hbor' := cpt_leFlag (cpt_app2 haBit (cpt_const [true])) (cpt_app2 hbBit hbor)
  have htot := cpt_app2 (cpt_app2 haBit hbBit) hbor
  have hout := cpt_comp htot cpt_oddBit
  exact cpt_congr
    (cpt_pairB2 (cpt_tail1 ha) (cpt_pairB2 (cpt_tail1 hb) (cpt_pairB2 hbor' (cpt_app2 hout hacc))))
    (fun _ => rfl)

theorem subStep_length (s : List Bool) : (subStep s).length ≤ s.length + 6 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hbor' : (leFlag (headBit (unpairB s).1 ++ [true])
      (headBit (unpairB (unpairB s).2).1 ++ (unpairB (unpairB (unpairB s).2).2).1)).length ≤ 1 := by
    unfold leFlag
    split_ifs <;> decide
  have hout : (oddBit (headBit (unpairB s).1 ++ headBit (unpairB (unpairB s).2).1 ++
      (unpairB (unpairB (unpairB s).2).2).1)).length = 1 := by
    rw [oddBit_eq]
    rfl
  simp only [subStep, pairB_length, List.length_append, List.length_tail, hout]
  omega

theorem subStep_pair (a b bor acc : List Bool) :
    subStep (pairB a (pairB b (pairB bor acc))) =
      pairB a.tail (pairB b.tail
        (pairB (leFlag (headBit a ++ [true]) (headBit b ++ bor))
          (oddBit (headBit a ++ headBit b ++ bor) ++ acc))) := by
  simp only [subStep, unpairB_pairB]

theorem subStep_iter_acc_len (n : ℕ) (a b bor acc : List Bool) :
    (unpairB (unpairB (unpairB (subStep^[n] (pairB a (pairB b (pairB bor acc))))).2).2).2.length =
      acc.length + n := by
  induction n generalizing a b bor acc with
  | zero =>
    simp only [Function.iterate_zero, id_eq, unpairB_pairB, Nat.add_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, subStep_pair, ih]
    rw [List.length_append, oddBit_eq, List.length_singleton]
    omega

theorem sub_bit_spec (u v : Bool) (bor : List Bool) (hbor : bor = [] ∨ bor = [true]) :
    let bor' := leFlag (headBit [u] ++ [true]) (headBit [v] ++ bor)
    let d := decide ((headBit [u] ++ headBit [v] ++ bor).length % 2 = 1)
    (bor' = [] ∨ bor' = [true]) ∧
      u.toNat + 2 * bor'.length = d.toNat + v.toNat + bor.length := by
  rcases hbor with rfl | rfl <;> cases u <;> cases v <;> decide

theorem subStep_iter_val (a b bor acc : List Bool)
    (hbor : bor = [] ∨ bor = [true]) (hle : val b + bor.length ≤ val a) :
    val (unpairB (unpairB (unpairB (subStep^[a.length] (pairB a (pairB b (pairB bor acc))))).2).2).2.reverse =
      val acc.reverse + 2 ^ acc.length * (val a - val b - bor.length) := by
  induction a generalizing b bor acc with
  | nil =>
    simp only [List.length_nil, Function.iterate_zero, id_eq, unpairB_pairB, val_nil] at hle ⊢
    have hzero : 0 - val b - bor.length = 0 := by omega
    rw [hzero, Nat.mul_zero, Nat.add_zero]
  | cons u as ih =>
    rw [List.length_cons, Function.iterate_succ_apply, subStep_pair]
    simp only [List.tail_cons]
    have haBit : headBit (u :: as) = headBit [u] := by
      rw [headBit_eq, headBit_eq]
      cases u <;> rfl
    have hbBit : headBit b = headBit [b.headD false] := by
      rw [headBit_eq, headBit_eq]
      cases b with
      | nil => rfl
      | cons v _ => cases v <;> rfl
    rw [haBit, hbBit]
    set bor' := leFlag (headBit [u] ++ [true]) (headBit [b.headD false] ++ bor)
    set d := decide ((headBit [u] ++ headBit [b.headD false] ++ bor).length % 2 = 1)
    have hspec := sub_bit_spec u (b.headD false) bor hbor
    have hbor' : bor' = [] ∨ bor' = [true] := hspec.1
    have hid : u.toNat + 2 * bor'.length = d.toNat + (b.headD false).toNat + bor.length := hspec.2
    have hodd : oddBit (headBit [u] ++ headBit [b.headD false] ++ bor) = [d] := oddBit_eq _
    rw [hodd]
    have hva : val (u :: as) = u.toNat + 2 * val as := val_cons u as
    have hvb : val b = (b.headD false).toNat + 2 * val b.tail := val_head_tail b
    have hd_le : d.toNat ≤ 1 := by cases d <;> decide
    have hle' : val b.tail + bor'.length ≤ val as := by omega
    have hrec := ih b.tail bor' ([d] ++ acc) hbor' hle'
    rw [hrec]
    have hrev : ([d] ++ acc).reverse = acc.reverse ++ [d] := by
      rw [List.singleton_append, List.reverse_cons]
    have hlen : ([d] ++ acc).length = acc.length + 1 := by
      rw [List.singleton_append, List.length_cons]
    rw [hrev, hlen, val_append_singleton, List.length_reverse, pow_succ]
    have hnum : d.toNat + 2 * (val as - val b.tail - bor'.length) =
        val (u :: as) - val b - bor.length := by omega
    rw [← hnum]
    ring

def subB_raw (a b : List Bool) : List Bool :=
  (unpairB (unpairB (unpairB (subStep^[a.length] (pairB a (pairB b (pairB [] []))))).2).2).2.reverse

def subB (a b : List Bool) : List Bool :=
  stripLSB (subB_raw a b)

theorem subB_length (a b : List Bool) : (subB a b).length ≤ a.length := by
  have h1 : (subB a b).length ≤ (subB_raw a b).length := stripLSB_length _
  have h2 : (subB_raw a b).length = a.length := by
    rw [subB_raw, List.length_reverse, subStep_iter_acc_len, List.length_nil, Nat.zero_add]
  omega

theorem val_subB (a b : List Bool) (hle : val b ≤ val a) : val (subB a b) = val a - val b := by
  rw [subB, val_stripLSB, subB_raw]
  have h := subStep_iter_val a b [] [] (Or.inl rfl) (by simp only [List.length_nil, Nat.add_zero]; exact hle)
  simpa only [List.reverse_nil, val_nil, List.length_nil, pow_zero, Nat.zero_add, Nat.one_mul,
    Nat.sub_zero] using h

def subBPacked (z : List Bool) : List Bool :=
  subB (unpairB z).1 (unpairB z).2

theorem cpt_subBPacked :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) subBPacked := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).1) := cpt_unpairB1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).2) := cpt_unpairB2
  have hInit := cpt_pairB2 ha (cpt_pairB2 hb (cpt_pairB2 (cpt_const []) (cpt_const [])))
  have hIter := cpt_iterGrow cpt_subStep 6 subStep_length ha hInit
  have hAcc := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hIter))
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have h1 := cpt_comp hAcc hRev
  have h2 := cpt_comp h1 cpt_stripLSB
  exact cpt_congr h2 (fun _ => rfl)

theorem cpt_subB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => subB (u s) (v s)) := by
  have h := cpt_comp (cpt_pairB2 hu hv) cpt_subBPacked
  exact cpt_congr h (fun s => by simp only [subBPacked, unpairB_pairB])

-- Binary long division step: state = pairB remA (pairB b (pairB rem q))
def divStep (s : List Bool) : List Bool :=
  let remA := (unpairB s).1
  let s2 := (unpairB s).2
  let b := (unpairB s2).1
  let s3 := (unpairB s2).2
  let rem := (unpairB s3).1
  let q := (unpairB s3).2
  let rem1 := sel (headBit remA) (false :: rem) (true :: rem)
  let cmp := bflag (decide (val b ≤ val rem1))
  let rem' := sel cmp rem1 (subB rem1 b)
  let q' := sel cmp (false :: q) (true :: q)
  pairB remA.tail (pairB b (pairB rem' q'))

theorem cpt_divStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) divStep := by
  have hremA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hs2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hs2
  have hs3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hs2
  have hrem : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 hs3
  have hq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 hs3
  have hrem1 := cpt_sel (cpt_comp hremA cpt_headBit) (cpt_cons1 false hrem) (cpt_cons1 true hrem)
  have hBinLe : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) := by
    have h := PvsNP.Units.m2_binary_le_polytime
    rw [encodePair_eq] at h
    exact h
  have hcmpBool := cpt_comp (cpt_pair hb hrem1) hBinLe
  have hcmp := cpt_congr (cpt_bitFlag hcmpBool) (fun _ => rfl)
  have hrem' := cpt_sel hcmp hrem1 (cpt_subB2 hrem1 hb)
  have hq' := cpt_sel hcmp (cpt_cons1 false hq) (cpt_cons1 true hq)
  exact cpt_congr (cpt_pairB2 (cpt_tail1 hremA) (cpt_pairB2 hb (cpt_pairB2 hrem' hq')))
    (fun _ => rfl)

theorem divStep_length (s : List Bool) : (divStep s).length ≤ s.length + 6 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  set remA := (unpairB s).1
  set b := (unpairB (unpairB s).2).1
  set rem := (unpairB (unpairB (unpairB s).2).2).1
  set q := (unpairB (unpairB (unpairB s).2).2).2
  set rem1 := sel (headBit remA) (false :: rem) (true :: rem)
  have hrem1_len : rem1.length = rem.length + 1 := by
    dsimp only [rem1]
    unfold sel
    split_ifs <;> exact List.length_cons
  have hrem'_len : (sel (bflag (decide (val b ≤ val rem1))) rem1 (subB rem1 b)).length ≤
      rem.length + 1 := by
    unfold sel
    split_ifs
    · omega
    · exact (subB_length rem1 b).trans (by omega)
  have hq'_len : (sel (bflag (decide (val b ≤ val rem1))) (false :: q) (true :: q)).length =
      q.length + 1 := by
    unfold sel
    split_ifs <;> exact List.length_cons
  simp only [divStep, pairB_length]
  change 2 * remA.tail.length +
      (2 * b.length +
        (2 * (sel (bflag (decide (val b ≤ val rem1))) rem1 (subB rem1 b)).length +
          (sel (bflag (decide (val b ≤ val rem1))) (false :: q) (true :: q)).length + 1) + 1) + 1 ≤
      s.length + 6
  have htail : remA.tail.length ≤ remA.length := by rw [List.length_tail]; omega
  omega

theorem divStep_pair (bit : Bool) (rest b rem q : List Bool) :
    divStep (pairB (bit :: rest) (pairB b (pairB rem q))) =
      pairB rest (pairB b (pairB
        (if val b ≤ val (bit :: rem) then subB (bit :: rem) b else bit :: rem)
        (if val b ≤ val (bit :: rem) then true :: q else false :: q))) := by
  have hrem1 : sel (headBit (bit :: rest)) (false :: rem) (true :: rem) = bit :: rem := by
    rw [headBit_eq]
    cases bit <;> rfl
  simp only [divStep, unpairB_pairB, List.tail_cons, hrem1]
  by_cases h : val b ≤ val (bit :: rem)
  · simp only [h, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
  · simp only [h, decide_false, bflag, sel, Bool.false_eq_true, ↓reduceIte]

theorem divStep_iter (remA b rem q : List Bool) (_hb : 0 < val b) (hrem : val rem < val b) :
    let fin := divStep^[remA.length] (pairB remA (pairB b (pairB rem q)))
    val (unpairB (unpairB (unpairB fin).2).2).1 < val b ∧
      val (unpairB (unpairB (unpairB fin).2).2).2 * val b +
        val (unpairB (unpairB (unpairB fin).2).2).1 =
        val remA.reverse + 2 ^ remA.length * (val q * val b + val rem) := by
  induction remA generalizing rem q with
  | nil =>
    simp only [List.length_nil, Function.iterate_zero, id_eq, unpairB_pairB, List.reverse_nil,
      val_nil, pow_zero, Nat.one_mul, Nat.zero_add]
    exact ⟨hrem, trivial⟩
  | cons bit rest ih =>
    dsimp only
    rw [List.length_cons, Function.iterate_succ_apply, divStep_pair]
    set rem' := if val b ≤ val (bit :: rem) then subB (bit :: rem) b else bit :: rem
    set q' := if val b ≤ val (bit :: rem) then true :: q else false :: q
    have hrem1_val : val (bit :: rem) = bit.toNat + 2 * val rem := val_cons bit rem
    have hbit_le : bit.toNat ≤ 1 := by cases bit <;> decide
    have hstep : val rem' < val b ∧ val q' * val b + val rem' = bit.toNat + 2 * (val q * val b + val rem) := by
      by_cases h : val b ≤ val (bit :: rem)
      · have hrem'_eq : rem' = subB (bit :: rem) b := by simp only [rem', h, ↓reduceIte]
        have hq'_eq : q' = true :: q := by simp only [q', h, ↓reduceIte]
        rw [hrem'_eq, hq'_eq, val_subB (bit :: rem) b h, val_cons true q, Bool.toNat_true]
        have hmul : (1 + 2 * val q) * val b = val b + 2 * (val q * val b) := by ring
        rw [hmul]
        omega
      · have hrem'_eq : rem' = bit :: rem := by simp only [rem', h, ↓reduceIte]
        have hq'_eq : q' = false :: q := by simp only [q', h, ↓reduceIte]
        rw [hrem'_eq, hq'_eq, val_cons false q, Bool.toNat_false, Nat.zero_add]
        have hmul : 2 * val q * val b = 2 * (val q * val b) := by ring
        rw [hmul]
        omega
    obtain ⟨hremF, hinv⟩ := ih rem' q' hstep.1
    refine ⟨hremF, ?_⟩
    rw [hinv, hstep.2, List.reverse_cons, val_append_singleton, List.length_reverse, pow_succ]
    ring

def divFinal (a b : List Bool) : List Bool :=
  divStep^[a.length] (pairB a.reverse (pairB b (pairB [] [])))

def modB (a b : List Bool) : List Bool :=
  sel (stripLSB b) (stripLSB a) (stripLSB (unpairB (unpairB (unpairB (divFinal a b)).2).2).1)

def modBPacked (z : List Bool) : List Bool :=
  modB (unpairB z).1 (unpairB z).2

theorem cpt_modBPacked :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) modBPacked := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).1) := cpt_unpairB1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).2) := cpt_unpairB2
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have hInit := cpt_pairB2 (cpt_comp ha hRev) (cpt_pairB2 hb (cpt_pairB2 (cpt_const []) (cpt_const [])))
  have hIter := cpt_iterGrow cpt_divStep 6 divStep_length ha hInit
  have hrem := cpt_comp (cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hIter))) cpt_stripLSB
  have hSel := cpt_sel (cpt_comp hb cpt_stripLSB) (cpt_comp ha cpt_stripLSB) hrem
  exact cpt_congr hSel (fun _ => rfl)

theorem modB_eq (a b : List Bool) : modB a b = Nat.bits (val a % val b) := by
  rcases Nat.eq_zero_or_pos (val b) with hb0 | hbpos
  · have hsb : stripLSB b = [] := (stripLSB_eq_nil_iff b).mpr hb0
    rw [modB, hsb, hb0, Nat.mod_zero]
    exact stripLSB_eq_bits a
  · have hsb : stripLSB b ≠ [] := by
      intro h
      exact Nat.ne_of_gt hbpos ((stripLSB_eq_nil_iff b).mp h)
    have hsel : modB a b = stripLSB (unpairB (unpairB (unpairB (divFinal a b)).2).2).1 := by
      simp only [modB, sel, hsb, ↓reduceIte]
    rw [hsel, stripLSB_eq_bits]
    have hiter := divStep_iter a.reverse b [] [] hbpos (by rw [val_nil]; exact hbpos)
    have hlen : a.reverse.length = a.length := List.length_reverse
    rw [hlen, List.reverse_reverse, val_nil, Nat.zero_mul, Nat.add_zero, Nat.mul_zero,
      Nat.add_zero] at hiter
    obtain ⟨hremF, hinv⟩ := hiter
    change val (unpairB (unpairB (unpairB (divFinal a b)).2).2).1 < val b at hremF
    have ha_eq : val a = val (unpairB (unpairB (unpairB (divFinal a b)).2).2).1 +
        val b * val (unpairB (unpairB (unpairB (divFinal a b)).2).2).2 := by
      dsimp only [divFinal]
      rw [← hinv]
      ring
    rw [ha_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hremF]

def divB (a b : List Bool) : List Bool :=
  sel (stripLSB b) [] (stripLSB (unpairB (unpairB (unpairB (divFinal a b)).2).2).2)

def divBPacked (z : List Bool) : List Bool :=
  divB (unpairB z).1 (unpairB z).2

theorem cpt_divBPacked :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) divBPacked := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).1) := cpt_unpairB1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).2) := cpt_unpairB2
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have hInit := cpt_pairB2 (cpt_comp ha hRev) (cpt_pairB2 hb (cpt_pairB2 (cpt_const []) (cpt_const [])))
  have hIter := cpt_iterGrow cpt_divStep 6 divStep_length ha hInit
  have hq := cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hIter))) cpt_stripLSB
  have hSel := cpt_sel (cpt_comp hb cpt_stripLSB) (cpt_const []) hq
  exact cpt_congr hSel (fun _ => rfl)

theorem divB_eq (a b : List Bool) : divB a b = Nat.bits (val a / val b) := by
  rcases Nat.eq_zero_or_pos (val b) with hb0 | hbpos
  · have hsb : stripLSB b = [] := (stripLSB_eq_nil_iff b).mpr hb0
    rw [divB, hsb, hb0, Nat.div_zero]
    rfl
  · have hsb : stripLSB b ≠ [] := by
      intro h
      exact Nat.ne_of_gt hbpos ((stripLSB_eq_nil_iff b).mp h)
    have hsel : divB a b = stripLSB (unpairB (unpairB (unpairB (divFinal a b)).2).2).2 := by
      simp only [divB, sel, hsb, ↓reduceIte]
    rw [hsel, stripLSB_eq_bits]
    have hiter := divStep_iter a.reverse b [] [] hbpos (by rw [val_nil]; exact hbpos)
    have hlen : a.reverse.length = a.length := List.length_reverse
    rw [hlen, List.reverse_reverse, val_nil, Nat.zero_mul, Nat.add_zero, Nat.mul_zero,
      Nat.add_zero] at hiter
    obtain ⟨hremF, hinv⟩ := hiter
    change val (unpairB (unpairB (unpairB (divFinal a b)).2).2).1 < val b at hremF
    have ha_eq : val a = val (unpairB (unpairB (unpairB (divFinal a b)).2).2).1 +
        val b * val (unpairB (unpairB (unpairB (divFinal a b)).2).2).2 := by
      dsimp only [divFinal]
      rw [← hinv]
      ring
    rw [ha_eq, Nat.add_mul_div_left _ _ hbpos, Nat.div_eq_of_lt hremF, Nat.zero_add]

theorem cpt_divB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => divB (u s) (v s)) := by
  have h := cpt_comp (cpt_pairB2 hu hv) cpt_divBPacked
  exact cpt_congr h (fun s => by simp only [divBPacked, unpairB_pairB])

theorem cpt_modB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => modB (u s) (v s)) := by
  have h := cpt_comp (cpt_pairB2 hu hv) cpt_modBPacked
  exact cpt_congr h (fun s => by simp only [modBPacked, unpairB_pairB])

theorem bits_pos {n : ℕ} (hpos : 0 < n) :
    Nat.bits n = decide (n % 2 = 1) :: Nat.bits (n / 2) := by
  have hbit : n = Nat.bit (decide (n % 2 = 1)) (n / 2) := by
    rw [Nat.bit_val]
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm
    · rw [hm]; simp only [Nat.zero_ne_one, decide_false, Bool.toNat_false]; omega
    · rw [hm]; simp only [decide_true, Bool.toNat_true]; omega
  conv_lhs => rw [hbit]
  exact Nat.bits_append_bit (n / 2) (decide (n % 2 = 1)) (fun h0 => by
    rw [h0] at hbit
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm
    · rw [hm] at hbit
      simp only [Nat.zero_ne_one, decide_false, Nat.bit_false, Nat.mul_zero] at hbit
      omega
    · rw [hm]; decide)

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rfl
    · have hdiv : n / 2 < n := Nat.div_lt_self hpos (by decide)
      rw [bits_pos hpos, val_cons, ih (n / 2) hdiv]
      rcases Nat.mod_two_eq_zero_or_one n with hm | hm
      · rw [hm]; simp only [Nat.zero_ne_one, decide_false, Bool.toNat_false]; omega
      · rw [hm]; simp only [decide_true, Bool.toNat_true]; omega

theorem bits_length_le_of_lt (k n : ℕ) (hn : n < 2 ^ k) : (Nat.bits n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    rw [hn0]; rfl
  | succ k ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact Nat.zero_le _
    · have hdiv : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
      rw [bits_pos hpos, List.length_cons]
      exact Nat.succ_le_succ (ih (n / 2) hdiv)

theorem val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => decide
  | cons b t ih =>
    rw [val_cons, List.length_cons, pow_succ]
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    omega

theorem divB_length (a b : List Bool) : (divB a b).length ≤ a.length := by
  rw [divB_eq]
  have hlt : val a / val b < 2 ^ a.length :=
    lt_of_le_of_lt (Nat.div_le_self (val a) (val b)) (val_lt_two_pow a)
  exact bits_length_le_of_lt a.length (val a / val b) hlt

theorem bits_len_ge_two_iff (n : ℕ) : 2 ≤ (Nat.bits n).length ↔ 2 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl <;> exact absurd h (by decide)
  · intro h
    have hpos : 0 < n := by omega
    have hdiv_pos : 0 < n / 2 := by omega
    rw [bits_pos hpos, List.length_cons, bits_pos hdiv_pos, List.length_cons]
    omega

theorem bits_len_le_one_iff (n : ℕ) : (Nat.bits n).length ≤ 1 ↔ n ≤ 1 := by
  have h := bits_len_ge_two_iff n
  omega

theorem bits_eq_nil_iff (n : ℕ) : Nat.bits n = [] ↔ n = 0 := by
  constructor
  · intro h
    rw [← val_bits n, h]
    rfl
  · intro h
    rw [h]
    rfl

theorem bits_eq_one_iff (n : ℕ) : Nat.bits n = [true] ↔ n = 1 := by
  constructor
  · intro h
    rw [← val_bits n, h]
    rfl
  · intro h
    rw [h]
    rfl

def isOneFlag (l : List Bool) : List Bool :=
  sel l [] (leFlag l [true])

theorem isOneFlag_bits_iff (n : ℕ) : isOneFlag (Nat.bits n) ≠ [] ↔ n = 1 := by
  unfold isOneFlag
  by_cases h0 : Nat.bits n = []
  · have hn0 : n = 0 := (bits_eq_nil_iff n).mp h0
    simp only [h0, sel, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
    omega
  · have hn0 : n ≠ 0 := fun h => h0 ((bits_eq_nil_iff n).mpr h)
    simp only [sel, h0, ↓reduceIte, leFlag, List.length_singleton]
    by_cases h1 : (Nat.bits n).length ≤ 1
    · have hn1 : n ≤ 1 := (bits_len_le_one_iff n).mp h1
      simp only [h1, ↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true, true_iff]
      omega
    · have hn2 : 2 ≤ n := (bits_len_ge_two_iff n).mp (by omega)
      simp only [h1, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
      omega

theorem cpt_isOneFlag {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => isOneFlag (f s)) :=
  cpt_congr (cpt_sel hf (cpt_const []) (cpt_leFlag hf (cpt_const [true]))) (fun _ => rfl)

def powStep (s : List Bool) : List Bool :=
  let sa := (unpairB s).1
  let cur := (unpairB s).2
  let nextCur :=
    sel (leFlag [true, true] cur) cur
      (sel (modB cur sa) (divB cur sa) cur)
  pairB sa nextCur

theorem cpt_powStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) powStep := by
  have hsa : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hcur : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hge2 := cpt_leFlag (cpt_const [true, true]) hcur
  have hmod := cpt_modB2 hcur hsa
  have hdiv := cpt_divB2 hcur hsa
  have hinner := cpt_sel hmod hdiv hcur
  have hnext := cpt_sel hge2 hcur hinner
  exact cpt_congr (cpt_pairB2 hsa hnext) (fun _ => rfl)

theorem powStep_length (s : List Bool) : (powStep s).length ≤ s.length + 1 := by
  have hunp := unpairB_length s
  set sa := (unpairB s).1
  set cur := (unpairB s).2
  have hnext_le : (sel (leFlag [true, true] cur) cur (sel (modB cur sa) (divB cur sa) cur)).length ≤
      cur.length := by
    unfold sel
    split_ifs
    · exact le_rfl
    · exact divB_length cur sa
    · exact le_rfl
  simp only [powStep, pairB_length]
  change 2 * sa.length +
      (sel (leFlag [true, true] cur) cur (sel (modB cur sa) (divB cur sa) cur)).length + 1 ≤
      s.length + 1
  omega

theorem powStep_pair (sa cur : List Bool) :
    powStep (pairB sa cur) =
      pairB sa (sel (leFlag [true, true] cur) cur (sel (modB cur sa) (divB cur sa) cur)) := by
  simp only [powStep, unpairB_pairB]

theorem powStep_one (sa : List Bool) : powStep (pairB sa [true]) = pairB sa [true] := by
  rw [powStep_pair]
  have hle : ¬ ([true, true] : List Bool).length ≤ ([true] : List Bool).length := by decide
  simp only [leFlag, hle, ↓reduceIte, sel]

theorem powStep_one_iter (sa : List Bool) (n : ℕ) :
    powStep^[n] (pairB sa [true]) = pairB sa [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, powStep_one, ih]

theorem powStep_preserves (sa cur : List Bool) (ha : 2 ≤ val sa) (hcur : cur = Nat.bits (val cur)) :
    let cur' := (unpairB (powStep (pairB sa cur))).2
    cur' = Nat.bits (val cur') ∧
      ((∃ k : ℕ, val cur = val sa ^ k) ↔ (∃ k : ℕ, val cur' = val sa ^ k)) := by
  dsimp only
  rw [powStep_pair, unpairB_pairB]
  by_cases hge : 2 ≤ cur.length
  · have hflag : leFlag [true, true] cur = [true] := by
      simp only [leFlag, List.length_cons, List.length_nil, hge, ↓reduceIte]
    rw [hflag]
    simp only [sel, List.cons_ne_nil, ↓reduceIte]
    by_cases hmod : modB cur sa = []
    · simp only [hmod, ↓reduceIte]
      have hdiv_eq : divB cur sa = Nat.bits (val cur / val sa) := divB_eq cur sa
      have hdiv_val : val (divB cur sa) = val cur / val sa := by rw [hdiv_eq, val_bits]
      have hmod0 : val cur % val sa = 0 := by
        rw [modB_eq] at hmod
        exact (bits_eq_nil_iff _).mp hmod
      have hcur_ge2 : 2 ≤ val cur := by
        rw [hcur] at hge
        exact (bits_len_ge_two_iff (val cur)).mp hge
      have hmul : val cur = val sa * (val cur / val sa) := by
        have hdm := Nat.div_add_mod (val cur) (val sa)
        omega
      refine ⟨by rw [hdiv_val, hdiv_eq], ?_⟩
      rw [hdiv_val]
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero =>
          rw [pow_zero] at hk
          omega
        | succ k' =>
          refine ⟨k', ?_⟩
          rw [pow_succ', hmul] at hk
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < val sa) hk
      · rintro ⟨k', hk'⟩
        refine ⟨k' + 1, ?_⟩
        rw [pow_succ', hmul, hk']
    · simp only [hmod, ↓reduceIte]
      exact ⟨hcur, trivial⟩
  · have hflag : leFlag [true, true] cur = [] := by
      simp only [leFlag, List.length_cons, List.length_nil, hge, ↓reduceIte]
    rw [hflag]
    simp only [sel, ↓reduceIte]
    exact ⟨hcur, trivial⟩

theorem powStep_iter_preserves (sa : List Bool) (ha : 2 ≤ val sa) (n : ℕ) :
    ∀ cur : List Bool, cur = Nat.bits (val cur) →
      let cur' := (unpairB (powStep^[n] (pairB sa cur))).2
      cur' = Nat.bits (val cur') ∧
        ((∃ k : ℕ, val cur = val sa ^ k) ↔ (∃ k : ℕ, val cur' = val sa ^ k)) := by
  induction n with
  | zero =>
    intro cur hcur
    simp only [Function.iterate_zero, id_eq, unpairB_pairB]
    exact ⟨hcur, trivial⟩
  | succ n ih =>
    intro cur hcur
    dsimp only
    rw [Function.iterate_succ_apply]
    have hp := powStep_preserves sa cur ha hcur
    set cur1 := (unpairB (powStep (pairB sa cur))).2
    have hpair : powStep (pairB sa cur) = pairB sa cur1 := by
      rw [powStep_pair]
      simp only [cur1, powStep_pair, unpairB_pairB]
    rw [hpair]
    have hrec := ih cur1 hp.1
    exact ⟨hrec.1, hp.2.trans hrec.2⟩

theorem powStep_iter_reach_one (sa : List Bool) (ha : 2 ≤ val sa) :
    ∀ (n : ℕ) (cur : List Bool),
      cur = Nat.bits (val cur) →
      (∃ k : ℕ, val cur = val sa ^ k) →
      val cur < 2 ^ n →
      (unpairB (powStep^[n] (pairB sa cur))).2 = [true] := by
  intro n
  induction n with
  | zero =>
    intro cur _ hpow hlt
    obtain ⟨k, hk⟩ := hpow
    have hge1 : 1 ≤ val sa ^ k := Nat.one_le_pow k (val sa) (by omega)
    rw [pow_zero] at hlt
    omega
  | succ n ih =>
    intro cur hcur hpow hlt
    obtain ⟨k, hk⟩ := hpow
    cases k with
    | zero =>
      rw [pow_zero] at hk
      have hcur1 : cur = [true] := by rw [hcur, hk]; rfl
      rw [hcur1, powStep_one_iter, unpairB_pairB]
    | succ k' =>
      rw [Function.iterate_succ_apply, powStep_pair]
      have hge1 : 1 ≤ val sa ^ k' := Nat.one_le_pow k' (val sa) (by omega)
      have hcur_eq : val cur = val sa * val sa ^ k' := by rw [hk, pow_succ']
      have hcur_ge2 : 2 ≤ val cur := by
        have hm : 2 * 1 ≤ val sa * val sa ^ k' := Nat.mul_le_mul ha hge1
        omega
      have hcur_len : 2 ≤ cur.length := by
        rw [hcur]
        exact (bits_len_ge_two_iff (val cur)).mpr hcur_ge2
      have hflag : leFlag [true, true] cur = [true] := by
        simp only [leFlag, List.length_cons, List.length_nil, hcur_len, ↓reduceIte]
      have hmod0 : val cur % val sa = 0 := by
        rw [hcur_eq, Nat.mul_mod_right]
      have hmod : modB cur sa = [] := by
        rw [modB_eq, hmod0]
        rfl
      rw [hflag]
      simp only [sel, List.cons_ne_nil, hmod, ↓reduceIte]
      set cur1 := divB cur sa
      have hcur1_eq : cur1 = Nat.bits (val cur / val sa) := divB_eq cur sa
      have hcur1_val : val cur1 = val sa ^ k' := by
        rw [hcur1_eq, val_bits, hcur_eq, Nat.mul_div_cancel_left _ (by omega : 0 < val sa)]
      have hcur1_bits : cur1 = Nat.bits (val cur1) := by
        rw [hcur1_val, ← Nat.mul_div_cancel_left (val sa ^ k') (by omega : 0 < val sa), ← hcur_eq]
        exact hcur1_eq
      have hcur1_lt : val cur1 < 2 ^ n := by
        have hm : 2 * val cur1 ≤ val sa * val cur1 := Nat.mul_le_mul_right _ ha
        rw [hcur1_val] at hm
        rw [pow_succ] at hlt
        omega
      exact ih cur1 hcur1_bits ⟨k', hcur1_val⟩ hcur1_lt

theorem neBool_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem cpt_neBool :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons _ l => exact (neBool_true l).symm)

def powFlag (a b : List Bool) : List Bool :=
  let sa := stripLSB a
  let sb := stripLSB b
  let finCur := (unpairB (powStep^[b.length] (pairB sa sb))).2
  sel sa (leFlag sb [true])
    (sel (leFlag [true, true] sa) (isOneFlag sb) (isOneFlag finCur))

def powFlagPacked (z : List Bool) : List Bool :=
  powFlag (unpairB z).1 (unpairB z).2

def powDec (p : List Bool × List Bool) : Bool :=
  !(powFlag p.1 p.2).isEmpty

theorem cpt_powFlagPacked :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) powFlagPacked := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).1) := cpt_unpairB1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => (unpairB z).2) := cpt_unpairB2
  have hsa := cpt_comp ha cpt_stripLSB
  have hsb := cpt_comp hb cpt_stripLSB
  have hInit := cpt_pairB2 hsa hsb
  have hIter := cpt_iterGrow cpt_powStep 1 powStep_length hb hInit
  have hFin := cpt_unpairB2_1 hIter
  have hCase0 := cpt_leFlag hsb (cpt_const [true])
  have hCase1 := cpt_isOneFlag hsb
  have hCase2 := cpt_isOneFlag hFin
  have hGe2 := cpt_leFlag (cpt_const [true, true]) hsa
  have hNonZero := cpt_sel hGe2 hCase1 hCase2
  exact cpt_congr (cpt_sel hsa hCase0 hNonZero) (fun _ => rfl)

theorem cpt_powDec :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer powDec := by
  rw [encodePair_eq]
  have h0 := cpt_comp cpt_pairB cpt_powFlagPacked
  have h1 := cpt_comp h0 cpt_neBool
  exact cpt_congr h1 (fun ⟨a, b⟩ => by simp only [powDec, powFlagPacked, unpairB_pairB])

theorem powDec_iff (a b : List Bool) :
    (∃ k : ℕ, val b = val a ^ k) ↔ powDec (a, b) = true := by
  have hne : ∀ l : List Bool, (!l.isEmpty) = true ↔ l ≠ [] := by
    intro l
    cases l with
    | nil => exact ⟨Bool.noConfusion, fun h => absurd rfl h⟩
    | cons _ _ => exact ⟨fun _ => List.cons_ne_nil _ _, fun _ => rfl⟩
  rw [powDec, hne]
  set sa := stripLSB a
  set sb := stripLSB b
  have hsa_eq : sa = Nat.bits (val a) := stripLSB_eq_bits a
  have hsb_eq : sb = Nat.bits (val b) := stripLSB_eq_bits b
  have hsa_val : val sa = val a := val_stripLSB a
  have hsb_val : val sb = val b := val_stripLSB b
  rcases Nat.eq_zero_or_pos (val a) with ha0 | hapos
  · have hsa0 : sa = [] := by rw [hsa_eq, ha0]; rfl
    have hpf : powFlag a b = leFlag sb [true] := by
      simp only [powFlag, sa, sb, hsa0, sel, ↓reduceIte]
    rw [hpf, ha0]
    simp only [leFlag, List.length_singleton]
    by_cases h1 : sb.length ≤ 1
    · have hb1 : val b ≤ 1 := by
        rw [hsb_eq] at h1
        exact (bits_len_le_one_iff (val b)).mp h1
      simp only [h1, ↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true, iff_true]
      rcases Nat.eq_zero_or_pos (val b) with hb0 | hbpos
      · exact ⟨1, by rw [hb0]; decide⟩
      · have hbe1 : val b = 1 := by omega
        exact ⟨0, by rw [hbe1, pow_zero]⟩
    · have hb2 : 2 ≤ val b := by
        rw [hsb_eq] at h1
        exact (bits_len_ge_two_iff (val b)).mp (by omega)
      simp only [h1, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
      rintro ⟨k, hk⟩
      cases k with
      | zero => rw [pow_zero] at hk; omega
      | succ k' => rw [Nat.zero_pow (Nat.succ_pos k')] at hk; omega
  · have hsa_ne : sa ≠ [] := by
      intro h
      exact Nat.ne_of_gt hapos ((bits_eq_nil_iff (val a)).mp (hsa_eq.symm.trans h))
    by_cases ha1 : val a = 1
    · have hsa_len : ¬ 2 ≤ sa.length := by
        rw [hsa_eq, ha1]
        decide
      have hpf : powFlag a b = isOneFlag sb := by
        simp only [powFlag, sa, sb, hsa_ne, sel, leFlag, List.length_cons, List.length_nil,
          hsa_len, ↓reduceIte]
      rw [hpf, hsb_eq, isOneFlag_bits_iff (val b), ha1]
      constructor
      · rintro ⟨k, hk⟩; rw [one_pow] at hk; exact hk
      · intro hb1; exact ⟨0, by rw [hb1, pow_zero]⟩
    · have ha2 : 2 ≤ val a := by omega
      have hsa_len : 2 ≤ sa.length := by
        rw [hsa_eq]
        exact (bits_len_ge_two_iff (val a)).mpr ha2
      have hpf : powFlag a b = isOneFlag (unpairB (powStep^[b.length] (pairB sa sb))).2 := by
        simp only [powFlag, sa, sb, hsa_ne, sel, leFlag, List.length_cons, List.length_nil,
          hsa_len, List.cons_ne_nil, ↓reduceIte]
      rw [hpf]
      have hsb_bits : sb = Nat.bits (val sb) := by rw [hsb_val]; exact hsb_eq
      have hpres := powStep_iter_preserves sa (by rw [hsa_val]; exact ha2) b.length sb hsb_bits
      set finCur := (unpairB (powStep^[b.length] (pairB sa sb))).2
      have hfin_bits : finCur = Nat.bits (val finCur) := hpres.1
      have hfin_iff : (∃ k : ℕ, val sb = val sa ^ k) ↔ (∃ k : ℕ, val finCur = val sa ^ k) := hpres.2
      rw [hsa_val, hsb_val] at hfin_iff
      constructor
      · intro hpow
        have hreach : finCur = [true] :=
          powStep_iter_reach_one sa (by rw [hsa_val]; exact ha2) b.length sb hsb_bits
            (by rw [hsb_val, hsa_val]; exact hpow) (by rw [hsb_val]; exact val_lt_two_pow b)
        rw [hreach]
        decide
      · intro hflag
        rw [hfin_bits] at hflag
        have hfin1 : val finCur = 1 := (isOneFlag_bits_iff (val finCur)).mp hflag
        exact hfin_iff.mpr ⟨0, by rw [hfin1, pow_zero]⟩

theorem main :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ^ k) ↔ f p = true :=
  ⟨powDec, cpt_powDec, fun ⟨a, b⟩ => powDec_iff a b⟩

end PvsNP.Units.tr_rel_val_power_of

theorem PvsNP.Units.tr_rel_val_power_of :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ^ k) ↔ f p = true :=
  PvsNP.Units.tr_rel_val_power_of.main
