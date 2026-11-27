import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-!
`coNP` is closed under prefix-reversal (`∃ i, (x.take i).reverse ++ x.drop i ∈ L`):
equivalently, the complement `{x | ∀ i ≤ x.length, (x.take i).reverse ++ x.drop i ∈ Lᶜ}` is in
`NP`, because a single polynomial-length certificate can bundle the `x.length + 1` NP witnesses
for `Lᶜ` at `i = 0, …, x.length`, and a polynomial-time verifier iterates `x.length + 1` steps,
maintaining `((x.take i).reverse, x.drop i)` via `head1` and `tail`.
-/

namespace PvsNP.Units.tc_closure_flip_prefix_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def boolToFlag (b : Bool) : List Bool :=
  if b = true then [] else [true]

theorem cpt_boolToFlag :
    ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x) boolToFlag := by
  refine filterMap_polyTime Computability.encodeBool (fun x : List Bool => x) boolToFlag
    (fun b : Bool => if b then none else some true) ?_
  intro b
  cases b <;> rfl

def isEmptyδ : Bool → Bool → Bool × Option Bool
  | _, _ => (true, none)

def isEmptyFin : Bool → Option Bool
  | false => some true
  | true => some false

theorem isEmpty_run (x : List Bool) (q : Bool) :
    fstRun isEmptyδ isEmptyFin q x =
      Computability.encodeBool (if q then false else decide (x = [])) := by
  induction x generalizing q with
  | nil =>
    cases q <;> rfl
  | cons b t ih =>
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

def head1 : List Bool → List Bool
  | [] => []
  | b :: _ => [b]

def head1δ : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

def head1Fin : Bool → Option Bool := fun _ => none

theorem head1_run_true (x : List Bool) : fstRun head1δ head1Fin true x = [] := by
  induction x with
  | nil => rfl
  | cons _ t ih => simp [fstRun, head1δ, ih]

theorem head1_run_false (x : List Bool) : fstRun head1δ head1Fin false x = head1 x := by
  cases x with
  | nil => rfl
  | cons b t => simp [fstRun, head1δ, head1_run_true, head1]

theorem cpt_head1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) head1 :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) head1 head1δ head1Fin false
    (fun x => (head1_run_false x).symm)

theorem head1_length_le (x : List Bool) : (head1 x).length ≤ 1 := by
  cases x <;> simp [head1]

def adv (st : List Bool × List Bool) : List Bool × List Bool :=
  (head1 st.2 ++ st.1, st.2.tail)

theorem adv_iter (x : List Bool) :
    ∀ j : ℕ, adv^[j] ([], x) = ((x.take j).reverse, x.drop j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    dsimp only [adv]
    by_cases hj : j < x.length
    · have hdrop : x.drop j = x[j] :: x.drop (j + 1) := List.drop_eq_getElem_cons hj
      have htake : x.take (j + 1) = x.take j ++ [x[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      rw [hdrop, head1, List.tail_cons, htake, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
    · have hge : x.length ≤ j := Nat.le_of_not_lt hj
      have hd1 : x.drop j = [] := List.drop_eq_nil_of_le hge
      have hd2 : x.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have ht1 : x.take j = x := List.take_of_length_le hge
      have ht2 : x.take (j + 1) = x := List.take_of_length_le (by omega)
      rw [hd1, hd2, ht1, ht2]
      simp [head1]

def rstep (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let st := (unpairB r1).1
  let revPref := (unpairB st).1
  let suf := (unpairB st).2
  let rem := (unpairB r1).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let cur := revPref ++ suf
  let okFlag := boolToFlag (f (cur, w))
  let flag' := sel flag okFlag [true]
  pairB flag' (pairB (pairB (head1 suf ++ revPref) suf.tail) rem')

theorem rstep_length (f : List Bool × List Bool → Bool) (s : List Bool) :
    (rstep f s).length ≤ s.length + 10 := by
  dsimp only [rstep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).1
  have h4 := unpairB_length (unpairB (unpairB s).2).2
  have hh := head1_length_le (unpairB (unpairB (unpairB s).2).1).2
  have hfl : (sel (unpairB s).1
      (boolToFlag (f ((unpairB (unpairB (unpairB s).2).1).1 ++
        (unpairB (unpairB (unpairB s).2).1).2,
        (unpairB (unpairB (unpairB s).2).2).1)))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs
    · cases f ((unpairB (unpairB (unpairB s).2).1).1 ++
        (unpairB (unpairB (unpairB s).2).1).2,
        (unpairB (unpairB (unpairB s).2).2).1) <;> simp [boolToFlag]
    · simp
  omega

theorem cpt_rstep (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (rstep f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hst := cpt_unpairB1_1 hr1
  have hrev := cpt_unpairB1_1 hst
  have hsuf := cpt_unpairB2_1 hst
  have hrem := cpt_unpairB2_1 hr1
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hcur := cpt_app2 hrev hsuf
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f ((unpairB (unpairB (unpairB s).2).1).1 ++
        (unpairB (unpairB (unpairB s).2).1).2,
        (unpairB (unpairB (unpairB s).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair hcur hw) hf) cpt_boolToFlag
  have hflag' := cpt_sel hflag hok (cpt_const [true])
  have hrev' := cpt_app2 (cpt_comp hsuf cpt_head1) hrev
  have hsuf' := cpt_tail1 hsuf
  exact cpt_pairB2 hflag' (cpt_pairB2 (cpt_pairB2 hrev' hsuf') hrem')

def encWitnesses : List (List Bool) → List Bool
  | [] => []
  | w :: rest => pairB w (encWitnesses rest)

theorem encWitnesses_length_le (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ w ∈ ws, w.length ≤ B) :
    (encWitnesses ws).length ≤ ws.length * (2 * B + 1) := by
  induction ws with
  | nil => simp [encWitnesses]
  | cons w rest ih =>
    have hw : w.length ≤ B := hB w (by simp)
    have hrest := ih (fun q hq => hB q (by simp [hq]))
    simp only [encWitnesses, pairB_length, List.length_cons]
    have hmul : (rest.length + 1) * (2 * B + 1) = rest.length * (2 * B + 1) + (2 * B + 1) := by
      ring
    omega

theorem rstep_complete (f : List Bool × List Bool → Bool) :
    ∀ (m : ℕ) (st : List Bool × List Bool) (ws : List (List Bool)) (hlen : ws.length = m),
      (∀ (j : ℕ) (hj : j < m),
        f ((adv^[j] st).1 ++ (adv^[j] st).2, ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ st' rem',
        (rstep f)^[m] (pairB [] (pairB (pairB st.1 st.2) (encWitnesses ws))) =
          pairB [] (pairB st' rem') := by
  intro m
  induction m with
  | zero =>
    intro st ws _ _
    exact ⟨pairB st.1 st.2, encWitnesses ws, rfl⟩
  | succ m ih =>
    intro st ws hlen hok
    cases ws with
    | nil => simp at hlen
    | cons w rest =>
      have h0 := hok 0 (Nat.zero_lt_succ m)
      simp only [List.getElem_cons_zero, Function.iterate_zero, id_eq] at h0
      have hst : rstep f (pairB [] (pairB (pairB st.1 st.2) (encWitnesses (w :: rest)))) =
          pairB [] (pairB (pairB (adv st).1 (adv st).2) (encWitnesses rest)) := by
        simp only [rstep, encWitnesses, unpairB_pairB, h0, boolToFlag, sel, ↓reduceIte, adv]
      rw [Function.iterate_succ_apply, hst]
      apply ih (adv st) rest (by simp at hlen; omega)
      intro j hj
      have hj' := hok (j + 1) (by omega)
      simp only [List.getElem_cons_succ] at hj'
      rwa [Function.iterate_succ_apply] at hj'

theorem rstep_sound (L : Language Bool) (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ) :
    ∀ (m : ℕ) (flag : List Bool) (st : List Bool × List Bool) (rem : List Bool),
      ∃ flag' st' rem',
        (rstep f)^[m] (pairB flag (pairB (pairB st.1 st.2) rem)) =
          pairB flag' (pairB st' rem') ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < m → (adv^[j] st).1 ++ (adv^[j] st).2 ∈ Lᶜ) := by
  intro m
  induction m with
  | zero =>
    intro flag st rem
    refine ⟨flag, pairB st.1 st.2, rem, rfl, fun hfl =>
      ⟨hfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  | succ m ih =>
    intro flag st rem
    rw [Function.iterate_succ_apply]
    let w := (unpairB rem).1
    let rem' := (unpairB rem).2
    let okFlag := boolToFlag (f (st.1 ++ st.2, w))
    let flag1 := sel flag okFlag [true]
    have hst : rstep f (pairB flag (pairB (pairB st.1 st.2) rem)) =
        pairB flag1 (pairB (pairB (adv st).1 (adv st).2) rem') := by
      simp [rstep, unpairB_pairB, adv, w, rem', okFlag, flag1]
    rw [hst]
    obtain ⟨flag', st', rem'', heq, hinv⟩ := ih flag1 (adv st) rem'
    refine ⟨flag', st', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hok0 : okFlag = [] := by
      simpa [flag1, sel, hflag0] using hfl1
    have hcur : st.1 ++ st.2 ∈ Lᶜ := by
      have hfcur : f (st.1 ++ st.2, w) = true := by
        simp only [okFlag, boolToFlag] at hok0
        cases hv : f (st.1 ++ st.2, w) with
        | true => rfl
        | false => simp [hv] at hok0
      exact hf (st.1 ++ st.2) w hfcur
    refine ⟨hflag0, fun j hj => ?_⟩
    cases j with
    | zero => simpa using hcur
    | succ j' =>
      rw [Function.iterate_succ_apply]
      exact hrest j' (by omega)

def runR (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (rstep f)^[(true :: (unpairB s).1).length]
    (pairB [] (pairB (pairB [] (unpairB s).1) (unpairB s).2))

def verR (f : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runR f (pairB p.1 p.2))).1 = [])

theorem cpt_verR (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verR f) := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => true :: (unpairB s).1) :=
    cpt_cons1 true cpt_unpairB1
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [] (pairB (pairB [] (unpairB s).1) (unpairB s).2)) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_pairB2 (cpt_const []) cpt_unpairB1) cpt_unpairB2)
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runR f) :=
    cpt_iterGrow (cpt_rstep f hf) 10 (rstep_length f) hcnt harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runR f s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runR f s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  have hdecP : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (verR f) := by
    unfold verR
    exact cpt_comp cpt_pairB hdecS
  rw [henc]
  exact hdecP

theorem conp_flip_prefix_aux (L : Language Bool) (hL : L ∈ PvsNP.coNP) :
    ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) ∈
      PvsNP.coNP := by
  classical
  change ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool)ᶜ ∈
    PvsNP.NP
  obtain ⟨R, p, ⟨f, hfR, hfc⟩, hlen, hmem⟩ :=
    L045 Lᶜ ((PvsNP.Units.fr_ladner.NP_iff Lᶜ).1 hL)
  have hfL : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ := fun u w h =>
    (hmem u).2 ⟨w, (hfR (u, w)).2 h⟩
  have hbound : ∀ u w : List Bool, f (u, w) = true → w.length ≤ p.eval u.length := fun u w h =>
    hlen u w ((hfR (u, w)).2 h)
  let Q : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C 1) * (Polynomial.C 2 * p + Polynomial.C 1)
  refine ⟨verR f, Q, cpt_verR f hfc, fun x => ?_⟩
  constructor
  · intro hx
    have hflipMem : ∀ j : ℕ, (x.take j).reverse ++ x.drop j ∈ Lᶜ := by
      intro j hmemL
      exact hx ⟨j, hmemL⟩
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        w.length ≤ p.eval x.length ∧ f ((x.take j).reverse ++ x.drop j, w) = true := by
      intro j
      obtain ⟨w, hw⟩ := (hmem ((x.take j).reverse ++ x.drop j)).1 (hflipMem j)
      have hfw : f ((x.take j).reverse ++ x.drop j, w) = true :=
        (hfR ((x.take j).reverse ++ x.drop j, w)).1 hw
      have hwl : w.length ≤ p.eval x.length := by
        have h1 := hbound ((x.take j).reverse ++ x.drop j) w hfw
        have hlenEq : ((x.take j).reverse ++ x.drop j).length = x.length := by
          simp only [List.length_append, List.length_reverse, List.length_take, List.length_drop]
          omega
        rwa [hlenEq] at h1
      exact ⟨w, hwl, hfw⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ,
        (pickW j).length ≤ p.eval x.length ∧
          f ((x.take j).reverse ++ x.drop j, pickW j) = true :=
      fun j => Classical.choose_spec (hexW j)
    let ws : List (List Bool) := (List.range (x.length + 1)).map pickW
    let cert : List Bool := encWitnesses ws
    have hwsLen : ws.length = x.length + 1 := by simp [ws]
    have hwB : ∀ w ∈ ws, w.length ≤ p.eval x.length := by
      intro w hw
      simp only [ws, List.mem_map, List.mem_range] at hw
      obtain ⟨j, _, rfl⟩ := hw
      exact (hpickW j).1
    have hcertLen : cert.length ≤ Q.eval x.length := by
      have h1 := encWitnesses_length_le ws (p.eval x.length) hwB
      rw [hwsLen] at h1
      change (encWitnesses ws).length ≤ Q.eval x.length
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      exact h1
    refine ⟨cert, hcertLen, ?_⟩
    have hok : ∀ (j : ℕ) (hj : j < x.length + 1),
        f ((adv^[j] ([], x)).1 ++ (adv^[j] ([], x)).2, ws[j]'(by rw [hwsLen]; exact hj)) =
          true := by
      intro j hj
      have hw : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by simp [ws]
      rw [hw, adv_iter]
      exact (hpickW j).2
    obtain ⟨st', rem', hrunEq⟩ := rstep_complete f (x.length + 1) ([], x) ws hwsLen hok
    have hrunR : runR f (pairB x cert) = pairB [] (pairB st' rem') := by
      unfold runR
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    simp [verR, hrunR, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runR f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', st', rem', hrunEq, hinv⟩ :=
      rstep_sound L f hfL (x.length + 1) [] ([], x) cert
    have hrunR : runR f (pairB x cert) = pairB flag' (pairB st' rem') := by
      unfold runR
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    rw [hrunR, unpairB_pairB] at hacc'
    obtain ⟨_, hflips⟩ := hinv hacc'
    rintro ⟨i, hi⟩
    have hlt : min i x.length < x.length + 1 := Nat.lt_succ_of_le (Nat.min_le_right _ _)
    have hm := hflips (min i x.length) hlt
    rw [adv_iter] at hm
    by_cases hle : i ≤ x.length
    · rw [Nat.min_eq_left hle] at hm
      exact hm hi
    · have hgt : x.length ≤ i := Nat.le_of_not_le hle
      rw [Nat.min_eq_right hgt] at hm
      have ht : x.take i = x := List.take_of_length_le hgt
      have hd : x.drop i = [] := List.drop_eq_nil_of_le hgt
      have htx : x.take x.length = x := List.take_length
      have hdx : x.drop x.length = [] := List.drop_length
      rw [ht, hd] at hi
      rw [htx, hdx] at hm
      exact hm hi

end PvsNP.Units.tc_closure_flip_prefix_conp

/-- coNP is closed under reversing a prefix (TM2). -/
theorem PvsNP.Units.tc_closure_flip_prefix_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) ∈
        PvsNP.coNP :=
  PvsNP.Units.tc_closure_flip_prefix_conp.conp_flip_prefix_aux
