import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tl_lang_len_prime_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-! ### isEmpty FST helper -/

def isEmptyδ : Bool → Bool → Bool × Option Bool
  | _, _ => (true, none)

def isEmptyFin : Bool → Option Bool
  | false => some true
  | true => some false

theorem isEmpty_run (x : List Bool) (q : Bool) :
    fstRun isEmptyδ isEmptyFin q x =
      Computability.encodeBool (if q then false else decide (x = [])) := by
  induction x generalizing q with
  | nil => cases q <;> rfl
  | cons _ t ih =>
      simp only [fstRun, isEmptyδ, Option.toList_none, List.nil_append]
      rw [ih true]
      cases q <;> rfl

theorem cpt_isEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => decide (x = [])) := by
  refine fst_polyTime (fun x : List Bool => x) Computability.encodeBool
    (fun x : List Bool => decide (x = [])) isEmptyδ isEmptyFin false ?_
  intro x
  simpa using (isEmpty_run x false).symm

/-! ### Unary divisibility counter (constant growth) -/

def modStep (s : List Bool) : List Bool :=
  let left := (unpairB s).1
  let used := (unpairB (unpairB s).2).1
  pairB (sel left used.tail left.tail) (pairB (sel left [true] (true :: used)) [])

theorem modStep_length (s : List Bool) : (modStep s).length ≤ s.length + 4 := by
  dsimp only [modStep]
  simp only [pairB_length, List.length_nil]
  have h0 := unpairB_length s
  have h1 := unpairB_length (unpairB s).2
  by_cases hl : (unpairB s).1 = []
  · simp only [sel, hl, ↓reduceIte, List.length_cons, List.length_nil, List.length_tail]
    omega
  · have hpos : 0 < (unpairB s).1.length := List.length_pos_iff.mpr hl
    simp only [sel, hl, ↓reduceIte, List.length_cons, List.length_tail]
    omega

theorem cpt_modStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) modStep := by
  have hleft := cpt_unpairB1
  have hused := cpt_unpairB1_1 cpt_unpairB2
  have hleft' := cpt_sel hleft (cpt_tail1 hused) (cpt_tail1 hleft)
  have hused' := cpt_sel hleft (cpt_const [true]) (cpt_cons1 true hused)
  exact cpt_pairB2 hleft' (cpt_pairB2 hused' (cpt_const []))

theorem modStep_iter (d : ℕ) (hd : 1 ≤ d) :
    ∀ (k : ℕ) (left used : List Bool),
      left.length + used.length = d → left.length < d →
      ∃ left' used',
        modStep^[k] (pairB left (pairB used [])) = pairB left' (pairB used' []) ∧
        left'.length + used'.length = d ∧ left'.length < d ∧
        (left'.length + k) % d = left.length % d := by
  intro k
  induction k with
  | zero =>
      intro left used hsum hlt
      exact ⟨left, used, rfl, hsum, hlt, by simp⟩
  | succ k ih =>
      intro left used hsum hlt
      rw [Function.iterate_succ_apply]
      cases left with
      | nil =>
          have hst : modStep (pairB [] (pairB used [])) = pairB used.tail (pairB [true] []) := by
            simp only [modStep, unpairB_pairB, sel, ↓reduceIte]
          rw [hst]
          have hused_len : used.length = d := by simp only [List.length_nil, Nat.zero_add] at hsum; exact hsum
          have htail_len : used.tail.length = d - 1 := by
            rw [List.length_tail, hused_len]
          have hsum1 : used.tail.length + ([true] : List Bool).length = d := by
            simp only [List.length_cons, List.length_nil]
            omega
          have hlt1 : used.tail.length < d := by omega
          obtain ⟨left', used', heq, hsum', hlt', hmod'⟩ := ih used.tail [true] hsum1 hlt1
          refine ⟨left', used', heq, hsum', hlt', ?_⟩
          have h2 : used.tail.length + 1 = d := by omega
          calc (left'.length + (k + 1)) % d
              = ((left'.length + k) + 1) % d := by rw [← Nat.add_assoc]
            _ = ((left'.length + k) % d + 1 % d) % d := Nat.add_mod _ 1 d
            _ = (used.tail.length % d + 1 % d) % d := by rw [hmod']
            _ = (used.tail.length + 1) % d := (Nat.add_mod _ 1 d).symm
            _ = d % d := by rw [h2]
            _ = 0 := Nat.mod_self d
            _ = ([] : List Bool).length % d := by simp
      | cons b t =>
          have hne : (b :: t) ≠ [] := List.cons_ne_nil b t
          have hst : modStep (pairB (b :: t) (pairB used [])) =
              pairB t (pairB (true :: used) []) := by
            simp only [modStep, unpairB_pairB, sel, hne, ↓reduceIte, List.tail_cons]
          rw [hst]
          have hsum1 : t.length + (true :: used).length = d := by
            simp only [List.length_cons] at hsum ⊢
            omega
          have hlt1 : t.length < d := by
            simp only [List.length_cons] at hlt
            omega
          obtain ⟨left', used', heq, hsum', hlt', hmod'⟩ := ih t (true :: used) hsum1 hlt1
          refine ⟨left', used', heq, hsum', hlt', ?_⟩
          calc (left'.length + (k + 1)) % d
              = ((left'.length + k) + 1) % d := by rw [← Nat.add_assoc]
            _ = ((left'.length + k) % d + 1 % d) % d := Nat.add_mod _ 1 d
            _ = (t.length % d + 1 % d) % d := by rw [hmod']
            _ = (t.length + 1) % d := (Nat.add_mod _ 1 d).symm

/-! ### Trial division loop over divisors d = 2, ..., n - 1 -/

def runMod (s : List Bool) : List Bool :=
  let r1 := (unpairB s).2
  let d := (unpairB r1).1
  let x := (unpairB r1).2
  modStep^[x.length] (pairB [] (pairB d []))

theorem cpt_runMod :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) runMod := by
  have hr1 := cpt_unpairB2
  have hd := cpt_unpairB1_1 hr1
  have hx := cpt_unpairB2_1 hr1
  have harg := cpt_pairB2 (cpt_const []) (cpt_pairB2 hd (cpt_const []))
  exact cpt_iterGrow cpt_modStep 4 modStep_length hx harg

def divStep (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let d := (unpairB r1).1
  let x := (unpairB r1).2
  let rem := (unpairB (runMod s)).1
  let hit := sel rem [true] []
  let flag' := sel flag hit [true]
  pairB flag' (pairB (true :: d) x)

theorem divStep_length (s : List Bool) : (divStep s).length ≤ s.length + 6 := by
  dsimp only [divStep]
  simp only [pairB_length, List.length_cons]
  have h0 := unpairB_length s
  have h1 := unpairB_length (unpairB s).2
  have hhit : (sel (unpairB (runMod s)).1 [true] []).length ≤ 1 :=
    sel_length _ [true] [] 1 (by decide) (by decide)
  have hfl : (sel (unpairB s).1 (sel (unpairB (runMod s)).1 [true] []) [true]).length ≤ 1 :=
    sel_length _ _ [true] 1 hhit (by decide)
  omega

theorem cpt_divStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) divStep := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hd := cpt_unpairB1_1 hr1
  have hx := cpt_unpairB2_1 hr1
  have hrem := cpt_unpairB1_1 cpt_runMod
  have hhit := cpt_sel hrem (cpt_const [true]) (cpt_const [])
  have hflag' := cpt_sel hflag hhit (cpt_const [true])
  exact cpt_pairB2 hflag' (cpt_pairB2 (cpt_cons1 true hd) hx)

theorem divStep_iter :
    ∀ (m : ℕ) (flag d x : List Bool), 1 ≤ d.length →
      ∃ flag' d',
        divStep^[m] (pairB flag (pairB d x)) = pairB flag' (pairB d' x) ∧
        (flag' = [] ↔ flag = [] ∧ ∀ k : ℕ, k < m → ¬ (d.length + k) ∣ x.length) := by
  intro m
  induction m with
  | zero =>
      intro flag d x _
      exact ⟨flag, d, rfl, ⟨fun h => ⟨h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩, fun h => h.1⟩⟩
  | succ m ih =>
      intro flag d x hd
      rw [Function.iterate_succ_apply]
      obtain ⟨left', used', hmodEq, _, hlt', hmod⟩ :=
        modStep_iter d.length hd x.length [] d (by simp) (by simp; omega)
      have hrm : runMod (pairB flag (pairB d x)) = pairB left' (pairB used' []) := by
        simpa only [runMod, unpairB_pairB] using hmodEq
      have hdvd_iff : left' = [] ↔ d.length ∣ x.length := by
        constructor
        · intro hnil
          rw [hnil] at hmod
          simp only [List.length_nil, Nat.zero_add, Nat.zero_mod] at hmod
          exact Nat.dvd_of_mod_eq_zero hmod
        · intro hdvd
          have hxm : x.length % d.length = 0 := Nat.mod_eq_zero_of_dvd hdvd
          have hlmod : left'.length % d.length = 0 := by
            have h1 : (left'.length + x.length) % d.length =
                (left'.length % d.length + x.length % d.length) % d.length := Nat.add_mod ..
            rw [hxm, Nat.add_zero, Nat.mod_mod] at h1
            rw [← h1, hmod]
            simp
          rw [Nat.mod_eq_of_lt hlt'] at hlmod
          exact List.eq_nil_of_length_eq_zero hlmod
      let flag1 := sel flag (sel left' [true] []) [true]
      have hst : divStep (pairB flag (pairB d x)) = pairB flag1 (pairB (true :: d) x) := by
        simp only [divStep, unpairB_pairB, hrm, flag1]
      rw [hst]
      have hd1 : 1 ≤ (true :: d).length := by simp
      obtain ⟨flag', d', heq, hinv⟩ := ih flag1 (true :: d) x hd1
      refine ⟨flag', d', heq, ?_⟩
      rw [hinv]
      have hfl1_iff : flag1 = [] ↔ flag = [] ∧ ¬ d.length ∣ x.length := by
        dsimp only [flag1]
        by_cases hf0 : flag = []
        · by_cases hl0 : left' = []
          · simp only [sel, hf0, hl0, ↓reduceIte, List.cons_ne_nil, false_iff, not_and, not_not]
            intro _
            exact hdvd_iff.1 hl0
          · simp only [sel, hf0, hl0, ↓reduceIte, true_iff, true_and]
            intro hdvd
            exact hl0 (hdvd_iff.2 hdvd)
        · show (if flag = [] then sel left' [true] [] else [true]) = [] ↔ flag = [] ∧ ¬ d.length ∣ x.length
          rw [if_neg hf0]
          exact ⟨fun h => absurd h (List.cons_ne_nil true []), fun h => absurd h.1 hf0⟩
      rw [hfl1_iff]
      constructor
      · rintro ⟨⟨hfl0, hnd0⟩, hrest⟩
        refine ⟨hfl0, fun k hk => ?_⟩
        cases k with
        | zero => simpa using hnd0
        | succ k' =>
            have h := hrest k' (by omega)
            have e : (true :: d).length + k' = d.length + (k' + 1) := by
              simp only [List.length_cons]; omega
            rw [← e]
            exact h
      · rintro ⟨hfl0, hall⟩
        refine ⟨⟨hfl0, by simpa using hall 0 (Nat.zero_lt_succ m)⟩, fun k' hk' => ?_⟩
        have h := hall (k' + 1) (by omega)
        have e : (true :: d).length + k' = d.length + (k' + 1) := by
          simp only [List.length_cons]; omega
        rw [e]
        exact h

/-! ### Top-level decider and main theorem -/

def runPrime (x : List Bool) : List Bool :=
  divStep^[x.tail.tail.length] (pairB (sel x.tail [true] []) (pairB [true, true] x))

def isPrimeF (x : List Bool) : Bool :=
  decide ((unpairB (runPrime x)).1 = [])

theorem cpt_isPrimeF :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer isPrimeF := by
  have hcnt := cpt_tail1 (cpt_tail1 cpt_id)
  have hinitFlag := cpt_sel (cpt_tail1 cpt_id) (cpt_const [true]) (cpt_const [])
  have harg := cpt_pairB2 hinitFlag (cpt_pairB2 (cpt_const [true, true]) cpt_id)
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) runPrime :=
    cpt_iterGrow cpt_divStep 6 divStep_length hcnt harg
  have hflag := cpt_unpairB1_1 hrun
  have hdec : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x => decide ((unpairB (runPrime x)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  exact hdec

theorem prime_iff_no_div (n : ℕ) :
    Nat.Prime n ↔ 2 ≤ n ∧ ∀ d : ℕ, 2 ≤ d → d < n → ¬ d ∣ n :=
  Nat.prime_def_lt'

theorem isPrimeF_spec (x : List Bool) : Nat.Prime x.length ↔ isPrimeF x = true := by
  obtain ⟨flag', d', hrunEq, hinv⟩ :=
    divStep_iter x.tail.tail.length (sel x.tail [true] []) [true, true] x (by decide)
  have hrp : runPrime x = pairB flag' (pairB d' x) := hrunEq
  have hdec : isPrimeF x = true ↔ flag' = [] := by
    simp only [isPrimeF, hrp, unpairB_pairB, decide_eq_true_eq]
  rw [hdec, hinv, prime_iff_no_div]
  have htail_iff : sel x.tail [true] [] = [] ↔ 2 ≤ x.length := by
    cases x with
    | nil => simp [sel]
    | cons _ t =>
        cases t with
        | nil => simp [sel]
        | cons _ _ => simp [sel]
  rw [htail_iff]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun k hk => ?_⟩
    have hlt : x.tail.tail.length = x.length - 2 := by
      simp only [List.length_tail]; omega
    exact hall (2 + k) (by omega) (by omega)
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d hd2 hdn => ?_⟩
    have hlt : x.tail.tail.length = x.length - 2 := by
      simp only [List.length_tail]; omega
    have h := hall (d - 2) (by omega)
    have e : ([true, true] : List Bool).length + (d - 2) = d := by
      simp only [List.length_cons, List.length_nil]; omega
    rw [e] at h
    exact h

end PvsNP.Units.tl_lang_len_prime_p

/-- The strings whose length is a prime number are in P (TM2). -/
theorem PvsNP.Units.tl_lang_len_prime_p :
    ({x : List Bool | Nat.Prime x.length} : Language Bool) ∈ PvsNP.P :=
  ⟨PvsNP.Units.tl_lang_len_prime_p.isPrimeF,
   PvsNP.Units.tl_lang_len_prime_p.cpt_isPrimeF,
   PvsNP.Units.tl_lang_len_prime_p.isPrimeF_spec⟩
