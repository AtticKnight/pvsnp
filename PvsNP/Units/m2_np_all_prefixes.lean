import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_np_all_prefixes

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

theorem head1_length_le (v : List Bool) : (head1 v).length ≤ 1 := by
  cases v <;> simp [head1]

theorem take_succ_eq (u v : List Bool) (j : ℕ) :
    u ++ v.take (j + 1) = (u ++ head1 v) ++ v.tail.take j := by
  cases v with
  | nil => simp [head1]
  | cons b vt => simp [head1, List.append_assoc]

def pstep (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let u := (unpairB r1).1
  let r2 := (unpairB r1).2
  let v := (unpairB r2).1
  let rem := (unpairB r2).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let flag' := sel flag (boolToFlag (f (u, w))) [true]
  pairB flag' (pairB (u ++ head1 v) (pairB v.tail rem'))

theorem pstep_length (f : List Bool × List Bool → Bool) (s : List Bool) :
    (pstep f s).length ≤ s.length + 7 := by
  dsimp only [pstep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have h4 := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  have hh := head1_length_le (unpairB (unpairB (unpairB s).2).2).1
  have hfl : (sel (unpairB s).1
      (boolToFlag (f ((unpairB (unpairB s).2).1,
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1)))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs
    · cases f ((unpairB (unpairB s).2).1,
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1) <;> simp [boolToFlag]
    · simp
  omega

theorem cpt_pstep (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (pstep f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hu := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hv := cpt_unpairB1_1 hr2
  have hrem := cpt_unpairB2_1 hr2
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f ((unpairB (unpairB s).2).1,
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair hu hw) hf) cpt_boolToFlag
  have hflag' := cpt_sel hflag hok (cpt_const [true])
  have hu' := cpt_app2 hu (cpt_comp hv cpt_head1)
  have hv' := cpt_tail1 hv
  exact cpt_pairB2 hflag' (cpt_pairB2 hu' (cpt_pairB2 hv' hrem'))

def encCerts : List (List Bool) → List Bool
  | [] => []
  | w :: rest => pairB w (encCerts rest)

theorem encCerts_length_le (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ w ∈ ws, w.length ≤ B) :
    (encCerts ws).length ≤ ws.length * (2 * B + 1) := by
  induction ws with
  | nil => simp [encCerts]
  | cons w rest ih =>
    have hw : w.length ≤ B := hB w (by simp)
    have hrest := ih (fun z hz => hB z (by simp [hz]))
    simp only [encCerts, pairB_length, List.length_cons]
    have hmul : (rest.length + 1) * (2 * B + 1) = rest.length * (2 * B + 1) + (2 * B + 1) := by
      ring
    omega

theorem pstep_complete (f : List Bool × List Bool → Bool) :
    ∀ (k : ℕ) (u v : List Bool) (ws : List (List Bool)) (hlen : ws.length = k),
      (∀ (j : ℕ) (hj : j < k), f (u ++ v.take j, ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ u' v' rem',
        (pstep f)^[k] (pairB [] (pairB u (pairB v (encCerts ws)))) =
          pairB [] (pairB u' (pairB v' rem')) := by
  intro k
  induction k with
  | zero =>
    intro u v ws _ _
    exact ⟨u, v, encCerts ws, rfl⟩
  | succ k ih =>
    intro u v ws hlen hok
    cases ws with
    | nil => simp at hlen
    | cons w rest =>
      have h0 := hok 0 (Nat.zero_lt_succ k)
      simp only [List.getElem_cons_zero, List.take_zero, List.append_nil] at h0
      have hst : pstep f (pairB [] (pairB u (pairB v (encCerts (w :: rest))))) =
          pairB [] (pairB (u ++ head1 v) (pairB v.tail (encCerts rest))) := by
        simp [pstep, encCerts, unpairB_pairB, h0, boolToFlag, sel]
      rw [Function.iterate_succ_apply, hst]
      apply ih (u ++ head1 v) v.tail rest (by simp at hlen; omega)
      intro j hj
      have hj' := hok (j + 1) (by omega)
      simp only [List.getElem_cons_succ] at hj'
      rw [take_succ_eq u v j] at hj'
      exact hj'

theorem pstep_sound (L : Language Bool) (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ L) :
    ∀ (k : ℕ) (flag u v rem : List Bool),
      ∃ flag' u' v' rem',
        (pstep f)^[k] (pairB flag (pairB u (pairB v rem))) =
          pairB flag' (pairB u' (pairB v' rem')) ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < k → (u ++ v.take j) ∈ L) := by
  intro k
  induction k with
  | zero =>
    intro flag u v rem
    refine ⟨flag, u, v, rem, rfl, fun hfl => ⟨hfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  | succ k ih =>
    intro flag u v rem
    rw [Function.iterate_succ_apply]
    let w := (unpairB rem).1
    let rem' := (unpairB rem).2
    let flag1 := sel flag (boolToFlag (f (u, w))) [true]
    have hst : pstep f (pairB flag (pairB u (pairB v rem))) =
        pairB flag1 (pairB (u ++ head1 v) (pairB v.tail rem')) := by
      simp [pstep, unpairB_pairB, w, rem', flag1]
    rw [hst]
    obtain ⟨flag', u', v', rem'', heq, hinv⟩ := ih flag1 (u ++ head1 v) v.tail rem'
    refine ⟨flag', u', v', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hfuw : f (u, w) = true := by
      simp only [flag1, sel, hflag0, ↓reduceIte, boolToFlag] at hfl1
      cases hv : f (u, w) with
      | true => rfl
      | false => simp [hv] at hfl1
    have huL : u ∈ L := hf u w hfuw
    refine ⟨hflag0, fun j hj => ?_⟩
    cases j with
    | zero => simpa using huL
    | succ j' =>
      rw [take_succ_eq u v j']
      exact hrest j' (by omega)

theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial d c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h d)

def runP (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (pstep f)^[(true :: (unpairB s).1).length]
    (pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2)))

def verP (f : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runP f (pairB p.1 p.2))).1 = [])

theorem cpt_verP (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verP f) := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => true :: (unpairB s).1) :=
    cpt_cons1 true cpt_unpairB1
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2))) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB1 cpt_unpairB2))
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runP f) :=
    cpt_iterGrow (cpt_pstep f hf) 7 (pstep_length f) hcnt harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runP f s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runP f s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  have hdecP : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (verP f) := by
    unfold verP
    exact cpt_comp cpt_pairB hdecS
  rw [henc]
  exact hdecP

theorem np_all_prefixes_aux (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | ∀ y : List Bool, y <+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  classical
  obtain ⟨R, p, ⟨f, hfR, hfc⟩, hlen, hmem⟩ :=
    L045 L ((PvsNP.Units.fr_ladner.NP_iff L).1 hL)
  have hfL : ∀ u w : List Bool, f (u, w) = true → u ∈ L := fun u w h =>
    (hmem u).2 ⟨w, (hfR (u, w)).2 h⟩
  have hbound : ∀ u w : List Bool, f (u, w) = true → w.length ≤ p.eval u.length := fun u w h =>
    hlen u w ((hfR (u, w)).2 h)
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C 1) * (Polynomial.C 2 * p + Polynomial.C 1)
  refine ⟨verP f, Q, cpt_verP f hfc, fun x => ?_⟩
  constructor
  · intro hx
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        j < x.length + 1 → w.length ≤ p.eval x.length ∧ f (x.take j, w) = true := by
      intro j
      by_cases hj : j < x.length + 1
      · have hyL : x.take j ∈ L := hx (x.take j) (List.take_prefix j x)
        obtain ⟨w, hw⟩ := (hmem (x.take j)).1 hyL
        have hfw : f (x.take j, w) = true := (hfR (x.take j, w)).1 hw
        have hwl : w.length ≤ p.eval x.length :=
          (hbound (x.take j) w hfw).trans (poly_eval_mono p (by simp))
        exact ⟨w, fun _ => ⟨hwl, hfw⟩⟩
      · exact ⟨[], fun h => absurd h hj⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ, j < x.length + 1 →
        (pickW j).length ≤ p.eval x.length ∧ f (x.take j, pickW j) = true :=
      fun j hj => Classical.choose_spec (hexW j) hj
    let ws : List (List Bool) := (List.range (x.length + 1)).map pickW
    let cert : List Bool := encCerts ws
    have hwsLen : ws.length = x.length + 1 := by simp [ws]
    have hwB : ∀ w ∈ ws, w.length ≤ p.eval x.length := by
      intro w hw
      simp only [ws, List.mem_map, List.mem_range] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      exact (hpickW j hj).1
    have hcertLen : cert.length ≤ Q.eval x.length := by
      have h1 := encCerts_length_le ws (p.eval x.length) hwB
      rw [hwsLen] at h1
      change (encCerts ws).length ≤ Q.eval x.length
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      exact h1
    refine ⟨cert, hcertLen, ?_⟩
    have hok : ∀ (j : ℕ) (hj : j < x.length + 1),
        f ([] ++ x.take j, ws[j]'(by rw [hwsLen]; exact hj)) = true := by
      intro j hj
      have hwj : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by simp [ws]
      simpa only [hwj, List.nil_append] using (hpickW j hj).2
    obtain ⟨u', v', rem', hrunEq⟩ := pstep_complete f (x.length + 1) [] x ws hwsLen hok
    have hrunP : runP f (pairB x cert) = pairB [] (pairB u' (pairB v' rem')) := by
      unfold runP
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    simp [verP, hrunP, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runP f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', u', v', rem', hrunEq, hinv⟩ :=
      pstep_sound L f hfL (x.length + 1) [] [] x cert
    have hrunP : runP f (pairB x cert) = pairB flag' (pairB u' (pairB v' rem')) := by
      unfold runP
      simpa only [unpairB_pairB, List.length_cons] using hrunEq
    rw [hrunP, unpairB_pairB] at hacc'
    obtain ⟨_, hprefs⟩ := hinv hacc'
    intro y hy
    obtain ⟨r, rfl⟩ := hy
    have hlt : y.length < (y ++ r).length + 1 := by simp
    have h1 := hprefs y.length hlt
    simpa only [List.nil_append, List.take_left] using h1

end PvsNP.Units.m2_np_all_prefixes

/-- If a language is in NP, the language of strings whose initial segments all belong to it is in NP. -/
theorem PvsNP.Units.m2_np_all_prefixes :
    ∀ L ∈ PvsNP.NP, ({x : List Bool | ∀ y : List Bool, y <+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_all_prefixes.np_all_prefixes_aux
