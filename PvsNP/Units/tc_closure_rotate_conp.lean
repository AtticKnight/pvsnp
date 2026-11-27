import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tc_closure_rotate_conp

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

theorem rot1_eq_rotate_one (x : List Bool) : x.tail ++ head1 x = x.rotate 1 := by
  cases x with
  | nil => rfl
  | cons b t => simp [head1]

theorem rot1_length (x : List Bool) : (x.tail ++ head1 x).length = x.length := by
  rw [rot1_eq_rotate_one, List.length_rotate]

def rstep (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let cur := (unpairB r1).1
  let rem := (unpairB r1).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let okFlag := boolToFlag (f (cur, w))
  let flag' := sel flag okFlag [true]
  pairB flag' (pairB (cur.tail ++ head1 cur) rem')

theorem rstep_length (f : List Bool × List Bool → Bool) (s : List Bool) :
    (rstep f s).length ≤ s.length + 4 := by
  dsimp only [rstep]
  simp only [pairB_length, rot1_length]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hfl : (sel (unpairB s).1
      (boolToFlag (f ((unpairB (unpairB s).2).1, (unpairB (unpairB (unpairB s).2).2).1)))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs
    · cases f ((unpairB (unpairB s).2).1, (unpairB (unpairB (unpairB s).2).2).1) <;>
        simp [boolToFlag]
    · simp
  omega

theorem cpt_rstep (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (rstep f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hcur := cpt_unpairB1_1 hr1
  have hrem := cpt_unpairB2_1 hr1
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f ((unpairB (unpairB s).2).1,
        (unpairB (unpairB (unpairB s).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair hcur hw) hf) cpt_boolToFlag
  have hflag' := cpt_sel hflag hok (cpt_const [true])
  have hcur' := cpt_app2 (cpt_tail1 hcur) (cpt_comp hcur cpt_head1)
  exact cpt_pairB2 hflag' (cpt_pairB2 hcur' hrem')

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
    ∀ (m : ℕ) (cur : List Bool) (ws : List (List Bool)) (hlen : ws.length = m),
      (∀ (j : ℕ) (hj : j < m), f (cur.rotate j, ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ cur' rem',
        (rstep f)^[m] (pairB [] (pairB cur (encWitnesses ws))) =
          pairB [] (pairB cur' rem') := by
  intro m
  induction m with
  | zero =>
    intro cur ws _ _
    exact ⟨cur, encWitnesses ws, rfl⟩
  | succ m ih =>
    intro cur ws hlen hok
    cases ws with
    | nil => simp at hlen
    | cons w rest =>
      have h0 := hok 0 (Nat.zero_lt_succ m)
      simp only [List.getElem_cons_zero, List.rotate_zero] at h0
      have hst : rstep f (pairB [] (pairB cur (encWitnesses (w :: rest)))) =
          pairB [] (pairB (cur.rotate 1) (encWitnesses rest)) := by
        simp only [rstep, encWitnesses, unpairB_pairB, h0, boolToFlag, sel, ↓reduceIte,
          rot1_eq_rotate_one]
      rw [Function.iterate_succ_apply, hst]
      apply ih (cur.rotate 1) rest (by simp at hlen; omega)
      intro j hj
      have hj' := hok (j + 1) (by omega)
      simp only [List.getElem_cons_succ] at hj'
      rw [List.rotate_rotate, Nat.add_comm 1 j]
      exact hj'

theorem rstep_sound (L : Language Bool) (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ) :
    ∀ (m : ℕ) (flag cur rem : List Bool),
      ∃ flag' cur' rem',
        (rstep f)^[m] (pairB flag (pairB cur rem)) =
          pairB flag' (pairB cur' rem') ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < m → cur.rotate j ∈ Lᶜ) := by
  intro m
  induction m with
  | zero =>
    intro flag cur rem
    refine ⟨flag, cur, rem, rfl, fun hfl => ⟨hfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  | succ m ih =>
    intro flag cur rem
    rw [Function.iterate_succ_apply]
    let w := (unpairB rem).1
    let rem' := (unpairB rem).2
    let okFlag := boolToFlag (f (cur, w))
    let flag1 := sel flag okFlag [true]
    have hst : rstep f (pairB flag (pairB cur rem)) =
        pairB flag1 (pairB (cur.rotate 1) rem') := by
      simp [rstep, unpairB_pairB, rot1_eq_rotate_one, w, rem', okFlag, flag1]
    rw [hst]
    obtain ⟨flag', cur', rem'', heq, hinv⟩ := ih flag1 (cur.rotate 1) rem'
    refine ⟨flag', cur', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hok0 : okFlag = [] := by
      simpa [flag1, sel, hflag0] using hfl1
    have hcur : cur ∈ Lᶜ := by
      have hfcur : f (cur, w) = true := by
        simp only [okFlag, boolToFlag] at hok0
        cases hv : f (cur, w) with
        | true => rfl
        | false => simp [hv] at hok0
      exact hf cur w hfcur
    refine ⟨hflag0, fun j hj => ?_⟩
    cases j with
    | zero => simpa using hcur
    | succ j' =>
      have hrot : cur.rotate (j' + 1) = (cur.rotate 1).rotate j' := by
        rw [List.rotate_rotate, Nat.add_comm 1 j']
      rw [hrot]
      exact hrest j' (by omega)

def runR (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (rstep f)^[(true :: (unpairB s).1).length]
    (pairB [] (pairB (unpairB s).1 (unpairB s).2))

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
      (fun s => pairB [] (pairB (unpairB s).1 (unpairB s).2)) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB1 cpt_unpairB2)
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runR f) :=
    cpt_iterGrow (cpt_rstep f hf) 4 (rstep_length f) hcnt harg
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

theorem conp_rotate_aux (L : Language Bool) (hL : L ∈ PvsNP.coNP) :
    ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) ∈ PvsNP.coNP := by
  classical
  change ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool)ᶜ ∈ PvsNP.NP
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
    have hrotMem : ∀ j : ℕ, x.rotate j ∈ Lᶜ := by
      intro j hmemL
      exact hx ⟨j, hmemL⟩
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        w.length ≤ p.eval x.length ∧ f (x.rotate j, w) = true := by
      intro j
      obtain ⟨w, hw⟩ := (hmem (x.rotate j)).1 (hrotMem j)
      have hfw : f (x.rotate j, w) = true := (hfR (x.rotate j, w)).1 hw
      have hwl : w.length ≤ p.eval x.length := by
        have h1 := hbound (x.rotate j) w hfw
        simpa [List.length_rotate] using h1
      exact ⟨w, hwl, hfw⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ, (pickW j).length ≤ p.eval x.length ∧ f (x.rotate j, pickW j) = true :=
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
        f (x.rotate j, ws[j]'(by rw [hwsLen]; exact hj)) = true := by
      intro j hj
      have hw : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by
        simp [ws]
      rw [hw]
      exact (hpickW j).2
    obtain ⟨cur', rem', hrunEq⟩ := rstep_complete f (x.length + 1) x ws hwsLen hok
    have hrunR : runR f (pairB x cert) = pairB [] (pairB cur' rem') := by
      unfold runR
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    simp [verR, hrunR, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runR f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', cur', rem', hrunEq, hinv⟩ :=
      rstep_sound L f hfL (x.length + 1) [] x cert
    have hrunR : runR f (pairB x cert) = pairB flag' (pairB cur' rem') := by
      unfold runR
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    rw [hrunR, unpairB_pairB] at hacc'
    obtain ⟨_, hrots⟩ := hinv hacc'
    rintro ⟨k, hk⟩
    cases x with
    | nil =>
      have h0 := hrots 0 (by simp)
      simp only [List.rotate_nil] at h0 hk
      exact h0 hk
    | cons b t =>
      have hpos : 0 < (b :: t).length := by simp
      have hlt : k % (b :: t).length < (b :: t).length + 1 :=
        Nat.lt_succ_of_lt (Nat.mod_lt k hpos)
      have hrot := hrots (k % (b :: t).length) hlt
      rw [List.rotate_mod] at hrot
      exact hrot hk

end PvsNP.Units.tc_closure_rotate_conp

/-- coNP is closed under cyclic shift (TM2). -/
theorem PvsNP.Units.tc_closure_rotate_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_rotate_conp.conp_rotate_aux
