import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_all_prefixes
import PvsNP.Units.m2_np_inter

namespace PvsNP.Units.tc_closure_rev_factor_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.m2_np_all_prefixes

/-- One step of a generic scan: check candidate `C st` against the next certificate, then move
the state with `T`. -/
def gstep (T C : List Bool → List Bool) (f : List Bool × List Bool → Bool) (s : List Bool) :
    List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let st := (unpairB r1).1
  let rem := (unpairB r1).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let flag' := sel flag (boolToFlag (f (C st, w))) [true]
  pairB flag' (pairB (T st) rem')

theorem sel_len (fl : List Bool) (b : Bool) : (sel fl (boolToFlag b) [true]).length ≤ 1 := by
  unfold sel
  split_ifs
  · cases b <;> simp [boolToFlag]
  · simp

theorem gstep_length (T C : List Bool → List Bool) (f : List Bool × List Bool → Bool) (c : ℕ)
    (hT : ∀ s, (T s).length ≤ s.length + c) (s : List Bool) :
    (gstep T C f s).length ≤ s.length + (2 * c + 4) := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hT' := hT (unpairB (unpairB s).2).1
  have hsel := sel_len (unpairB s).1
    (f (C (unpairB (unpairB s).2).1, (unpairB (unpairB (unpairB s).2).2).1))
  simp only [gstep, pairB_length]
  omega

theorem cpt_gstep (T C : List Bool → List Bool) (f : List Bool × List Bool → Bool)
    (hTc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T)
    (hCc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) C)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (gstep T C f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hst := cpt_unpairB1_1 hr1
  have hrem := cpt_unpairB2_1 hr1
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f (C (unpairB (unpairB s).2).1,
        (unpairB (unpairB (unpairB s).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair (cpt_comp hst hCc) hw) hf) cpt_boolToFlag
  have hflag' := cpt_sel hflag hok (cpt_const [true])
  exact cpt_pairB2 hflag' (cpt_pairB2 (cpt_comp hst hTc) hrem')

theorem gstep_complete (T C : List Bool → List Bool) (f : List Bool × List Bool → Bool) :
    ∀ (k : ℕ) (st : List Bool) (ws : List (List Bool)) (hlen : ws.length = k),
      (∀ (j : ℕ) (hj : j < k), f (C (T^[j] st), ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ st' rem', (gstep T C f)^[k] (pairB [] (pairB st (encCerts ws))) =
        pairB [] (pairB st' rem') := by
  intro k
  induction k with
  | zero =>
    intro st ws _ _
    exact ⟨st, encCerts ws, rfl⟩
  | succ k ih =>
    intro st ws hlen hok
    cases ws with
    | nil => cases hlen
    | cons w rest =>
      have h0 := hok 0 (Nat.zero_lt_succ k)
      simp only [List.getElem_cons_zero, Function.iterate_zero_apply] at h0
      have hst : gstep T C f (pairB [] (pairB st (encCerts (w :: rest)))) =
          pairB [] (pairB (T st) (encCerts rest)) := by
        simp [gstep, encCerts, unpairB_pairB, h0, boolToFlag, sel]
      rw [Function.iterate_succ_apply, hst]
      have hlen' : rest.length = k := by
        rw [List.length_cons] at hlen
        exact Nat.succ.inj hlen
      apply ih (T st) rest hlen'
      intro j hj
      have hj' := hok (j + 1) (Nat.succ_lt_succ hj)
      simp only [List.getElem_cons_succ] at hj'
      rw [Function.iterate_succ_apply] at hj'
      exact hj'

theorem gstep_sound (M : Language Bool) (T C : List Bool → List Bool)
    (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ M) :
    ∀ (k : ℕ) (flag st rem : List Bool),
      ∃ flag' st' rem',
        (gstep T C f)^[k] (pairB flag (pairB st rem)) = pairB flag' (pairB st' rem') ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < k → C (T^[j] st) ∈ M) := by
  intro k
  induction k with
  | zero =>
    intro flag st rem
    exact ⟨flag, st, rem, rfl, fun hfl => ⟨hfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  | succ k ih =>
    intro flag st rem
    rw [Function.iterate_succ_apply]
    let w := (unpairB rem).1
    let rem' := (unpairB rem).2
    let flag1 := sel flag (boolToFlag (f (C st, w))) [true]
    have hst : gstep T C f (pairB flag (pairB st rem)) =
        pairB flag1 (pairB (T st) rem') := by
      simp [gstep, unpairB_pairB, w, rem', flag1]
    rw [hst]
    obtain ⟨flag', st', rem'', heq, hinv⟩ := ih flag1 (T st) rem'
    refine ⟨flag', st', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hfcand : f (C st, w) = true := by
      simp only [flag1, sel, hflag0, ↓reduceIte, boolToFlag] at hfl1
      cases hv : f (C st, w) with
      | true => rfl
      | false => simp [hv] at hfl1
    have hcandM : C st ∈ M := hf (C st) w hfcand
    refine ⟨hflag0, fun j hj => ?_⟩
    cases j with
    | zero => exact hcandM
    | succ j' =>
      rw [Function.iterate_succ_apply]
      exact hrest j' (Nat.lt_of_succ_lt_succ hj)

def runG (T C I : List Bool → List Bool) (f : List Bool × List Bool → Bool) (s : List Bool) :
    List Bool :=
  (gstep T C f)^[(unpairB s).1.length] (pairB [] (pairB (I (unpairB s).1) (unpairB s).2))

def verG (T C I : List Bool → List Bool) (f : List Bool × List Bool → Bool)
    (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runG T C I f (pairB p.1 p.2))).1 = [])

theorem cpt_verG (T C I : List Bool → List Bool) (f : List Bool × List Bool → Bool) (c : ℕ)
    (hTc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T)
    (hCc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) C)
    (hIc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) I)
    (hT : ∀ s, (T s).length ≤ s.length + c)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verG T C I f) := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [] (pairB (I (unpairB s).1) (unpairB s).2)) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_comp cpt_unpairB1 hIc) cpt_unpairB2)
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runG T C I f) :=
    cpt_iterGrow (cpt_gstep T C f hTc hCc hf) (2 * c + 4) (gstep_length T C f c hT)
      cpt_unpairB1 harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runG T C I f s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runG T C I f s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  have hdecP : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (verG T C I f) := by
    unfold verG
    exact cpt_comp cpt_pairB hdecS
  rw [henc]
  exact hdecP

theorem iter_len (T : List Bool → List Bool) (c : ℕ) (hT : ∀ s, (T s).length ≤ s.length + c) :
    ∀ (j : ℕ) (s : List Bool), (T^[j] s).length ≤ s.length + j * c := by
  intro j
  induction j with
  | zero => intro s; simp
  | succ j ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have h1 := ih (T s)
    have h2 := hT s
    have h3 : (j + 1) * c = j * c + c := Nat.succ_mul j c
    rw [h3]
    omega

/-- NP is closed under a scan over `|x|` poly-time states, each yielding one candidate. -/
theorem gen_np (M : Language Bool) (hM : M ∈ PvsNP.NP) (T C I : List Bool → List Bool) (c : ℕ)
    (hTc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T)
    (hCc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) C)
    (hIc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) I)
    (hT : ∀ s, (T s).length ≤ s.length + c) (hC : ∀ s, (C s).length ≤ s.length + c)
    (hI : ∀ s, (I s).length ≤ 2 * s.length + 2) :
    ({x : List Bool | ∀ j : ℕ, j < x.length → C (T^[j] (I x)) ∈ M} : Language Bool) ∈
      PvsNP.NP := by
  classical
  obtain ⟨R, p, ⟨f, hfR, hfc⟩, hlen, hmem⟩ :=
    L045 M ((PvsNP.Units.fr_ladner.NP_iff M).1 hM)
  have hfL : ∀ u w : List Bool, f (u, w) = true → u ∈ M := fun u w h =>
    (hmem u).2 ⟨w, (hfR (u, w)).2 h⟩
  have hbound : ∀ u w : List Bool, f (u, w) = true → w.length ≤ p.eval u.length := fun u w h =>
    hlen u w ((hfR (u, w)).2 h)
  let B : Polynomial ℕ := Polynomial.C (2 + c) * Polynomial.X + Polynomial.C (2 + c)
  let Q : Polynomial ℕ := Polynomial.X * (Polynomial.C 2 * p.comp B + Polynomial.C 1)
  refine ⟨verG T C I f, Q, cpt_verG T C I f c hTc hCc hIc hT hfc, fun x => ?_⟩
  have hcandB : ∀ j : ℕ, j < x.length → (C (T^[j] (I x))).length ≤ B.eval x.length := by
    intro j hj
    have h1 := hC (T^[j] (I x))
    have h2 := iter_len T c hT j (I x)
    have h3 := hI x
    have h4 : j * c ≤ x.length * c := Nat.mul_le_mul_right c (le_of_lt hj)
    have h5 : (2 + c) * x.length = 2 * x.length + x.length * c := by ring
    simp only [B, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  constructor
  · intro hx
    have hx' : ∀ j : ℕ, j < x.length → C (T^[j] (I x)) ∈ M := hx
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        j < x.length → w.length ≤ (p.comp B).eval x.length ∧ f (C (T^[j] (I x)), w) = true := by
      intro j
      by_cases hj : j < x.length
      · obtain ⟨w, hw⟩ := (hmem _).1 (hx' j hj)
        have hfw : f (C (T^[j] (I x)), w) = true := (hfR _).1 hw
        refine ⟨w, fun _ => ⟨?_, hfw⟩⟩
        rw [Polynomial.eval_comp]
        exact le_trans (hbound _ w hfw) (poly_eval_mono p (hcandB j hj))
      · exact ⟨[], fun h => absurd h hj⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ, j < x.length →
        (pickW j).length ≤ (p.comp B).eval x.length ∧ f (C (T^[j] (I x)), pickW j) = true :=
      fun j hj => Classical.choose_spec (hexW j) hj
    let ws : List (List Bool) := (List.range x.length).map pickW
    let cert : List Bool := encCerts ws
    have hwsLen : ws.length = x.length := by simp [ws]
    have hwB : ∀ w ∈ ws, w.length ≤ (p.comp B).eval x.length := by
      intro w hw
      simp only [ws, List.mem_map, List.mem_range] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      exact (hpickW j hj).1
    have hcertLen : cert.length ≤ Q.eval x.length := by
      have h1 := encCerts_length_le ws ((p.comp B).eval x.length) hwB
      rw [hwsLen] at h1
      change (encCerts ws).length ≤ Q.eval x.length
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X]
      exact h1
    refine ⟨cert, hcertLen, ?_⟩
    have hok : ∀ (j : ℕ) (hj : j < x.length),
        f (C (T^[j] (I x)), ws[j]'(by rw [hwsLen]; exact hj)) = true := by
      intro j hj
      have hwj : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by simp [ws]
      rw [hwj]
      exact (hpickW j hj).2
    obtain ⟨st', rem', hrunEq⟩ := gstep_complete T C f x.length (I x) ws hwsLen hok
    have hrunG : runG T C I f (pairB x cert) = pairB [] (pairB st' rem') := by
      unfold runG
      simpa only [unpairB_pairB] using hrunEq
    simp [verG, hrunG, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runG T C I f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', st', rem', hrunEq, hinv⟩ :=
      gstep_sound M T C f hfL x.length [] (I x) cert
    have hrunG : runG T C I f (pairB x cert) = pairB flag' (pairB st' rem') := by
      unfold runG
      simpa only [unpairB_pairB] using hrunEq
    rw [hrunG, unpairB_pairB] at hacc'
    exact (hinv hacc').2

/-- Inner scan state `pairB a (pairB rest acc)`: move the head of `rest` onto `acc`. -/
def T1 (st : List Bool) : List Bool :=
  pairB (unpairB st).1 (pairB (unpairB (unpairB st).2).1.tail
    (head1 (unpairB (unpairB st).2).1 ++ (unpairB (unpairB st).2).2))

def C1 (st : List Bool) : List Bool :=
  (unpairB st).1 ++ ((unpairB (unpairB st).2).2 ++ (unpairB (unpairB st).2).1)

def I1 (s : List Bool) : List Bool := pairB (unpairB s).2 (pairB (unpairB s).1 [])

/-- Outer scan state `pairB r u`: move the head of `r` to the end of `u`. -/
def T2 (st : List Bool) : List Bool :=
  pairB (unpairB st).1.tail ((unpairB st).2 ++ head1 (unpairB st).1)

def I2 (x : List Bool) : List Bool := pairB x []

theorem cpt_T1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T1 := by
  have ha := cpt_unpairB1
  have hr2 := cpt_unpairB2
  have hrest := cpt_unpairB1_1 hr2
  have hacc := cpt_unpairB2_1 hr2
  exact cpt_pairB2 ha (cpt_pairB2 (cpt_tail1 hrest) (cpt_app2 (cpt_comp hrest cpt_head1) hacc))

theorem cpt_C1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) C1 := by
  have ha := cpt_unpairB1
  have hr2 := cpt_unpairB2
  have hrest := cpt_unpairB1_1 hr2
  have hacc := cpt_unpairB2_1 hr2
  exact cpt_app2 ha (cpt_app2 hacc hrest)

theorem cpt_I1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) I1 :=
  cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const []))

theorem cpt_T2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T2 :=
  cpt_pairB2 (cpt_tail1 cpt_unpairB1) (cpt_app2 cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_head1))

theorem cpt_I2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) I2 :=
  cpt_pairB2 cpt_id (cpt_const [])

theorem len_T1 (s : List Bool) : (T1 s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have hh := head1_length_le (unpairB (unpairB s).2).1
  simp only [T1, pairB_length, List.length_append, List.length_tail]
  omega

theorem len_C1 (s : List Bool) : (C1 s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  simp only [C1, List.length_append]
  omega

theorem len_I1 (s : List Bool) : (I1 s).length ≤ 2 * s.length + 2 := by
  have h1 := unpairB_length s
  simp only [I1, pairB_length, List.length_nil]
  omega

theorem len_T2 (s : List Bool) : (T2 s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have hh := head1_length_le (unpairB s).1
  simp only [T2, pairB_length, List.length_append, List.length_tail]
  omega

theorem len_C2 (s : List Bool) : ((fun t : List Bool => t) s).length ≤ s.length + 3 :=
  Nat.le_add_right _ _

theorem take_len_app (a b : List Bool) : (a ++ b).take a.length = a := by
  first
    | (simp; done)
    | exact List.take_left' rfl
    | exact List.take_left a b

theorem drop_len_app (a b : List Bool) : (a ++ b).drop a.length = b := by
  first
    | (simp; done)
    | exact List.drop_left' rfl
    | exact List.drop_left a b

theorem len_I2 (s : List Bool) : (I2 s).length ≤ 2 * s.length + 2 := by
  simp only [I2, pairB_length, List.length_nil]
  omega

theorem iterT1 : ∀ (j : ℕ) (a rest acc : List Bool),
    T1^[j] (pairB a (pairB rest acc)) = pairB a (pairB (rest.drop j) ((rest.take j).reverse ++ acc)) := by
  intro j
  induction j with
  | zero => intro a rest acc; simp
  | succ j ih =>
    intro a rest acc
    rw [Function.iterate_succ_apply]
    have hst : T1 (pairB a (pairB rest acc)) = pairB a (pairB rest.tail (head1 rest ++ acc)) := by
      simp [T1, unpairB_pairB]
    rw [hst, ih]
    cases rest with
    | nil => simp [head1]
    | cons b t => simp [head1, List.append_assoc]

theorem iterT2 : ∀ (i : ℕ) (r u : List Bool),
    T2^[i] (pairB r u) = pairB (r.drop i) (u ++ r.take i) := by
  intro i
  induction i with
  | zero => intro r u; simp
  | succ i ih =>
    intro r u
    rw [Function.iterate_succ_apply]
    have hst : T2 (pairB r u) = pairB r.tail (u ++ head1 r) := by
      simp [T2, unpairB_pairB]
    rw [hst, ih]
    cases r with
    | nil => simp [head1]
    | cons b t => simp [head1, List.append_assoc]

theorem state_eq (x : List Bool) (i : ℕ) :
    T2^[i] (I2 x) = pairB (x.drop i) (x.take i) := by
  rw [show I2 x = pairB x [] from rfl, iterT2]
  simp

theorem cand_eq (x : List Bool) (i j : ℕ) :
    C1 (T1^[j] (I1 (pairB (x.drop i) (x.take i)))) =
      x.take i ++ (((x.drop i).take j).reverse ++ (x.drop i).drop j) := by
  have hI : I1 (pairB (x.drop i) (x.take i)) = pairB (x.take i) (pairB (x.drop i) []) := by
    simp [I1, unpairB_pairB]
  rw [hI, iterT1]
  simp [C1, unpairB_pairB]

theorem main_iff (L : Language Bool) (x : List Bool) :
    (¬ ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L) ↔
    (¬ x ∈ L ∧ ∀ i : ℕ, i < x.length → ∀ j : ℕ, j < (T2^[i] (I2 x)).length →
      ¬ (C1 (T1^[j] (I1 (T2^[i] (I2 x)))) ∈ L)) := by
  constructor
  · intro hx
    refine ⟨fun hxL => hx ⟨[], [], x, by simp, by simpa using hxL⟩, ?_⟩
    intro i _ j _ hmem
    rw [state_eq, cand_eq] at hmem
    exact hx ⟨x.take i, (x.drop i).take j, (x.drop i).drop j,
      by rw [List.append_assoc, List.take_append_drop, List.take_append_drop],
      by rw [List.append_assoc]; exact hmem⟩
  · rintro ⟨hxL, hall⟩ ⟨u, v, w, rfl, hmem⟩
    by_cases hlt : u.length < (u ++ v ++ w).length
    · have hall' := hall u.length hlt
      rw [state_eq] at hall'
      have hj : v.length <
          (pairB ((u ++ v ++ w).drop u.length) ((u ++ v ++ w).take u.length)).length := by
        rw [pairB_length, List.length_drop, List.length_take]
        simp only [List.length_append]
        omega
      have hc := hall' v.length hj
      rw [cand_eq] at hc
      simp only [List.append_assoc] at hc
      rw [take_len_app, drop_len_app, take_len_app, drop_len_app] at hc
      exact hc (by rw [← List.append_assoc]; exact hmem)
    · have hv : v = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_append] at hlt
        omega
      have hw : w = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_append] at hlt
        omega
      subst hv
      subst hw
      exact hxL (by simpa using hmem)

theorem main_aux (L : Language Bool) (hL : L ∈ PvsNP.coNP) :
    ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} :
      Language Bool) ∈ PvsNP.coNP := by
  change ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} :
    Language Bool)ᶜ ∈ PvsNP.NP
  have hM : Lᶜ ∈ PvsNP.NP := hL
  have h1 := gen_np Lᶜ hM T1 C1 I1 3 cpt_T1 cpt_C1 cpt_I1 len_T1 len_C1 len_I1
  have h2 := gen_np _ h1 T2 (fun t : List Bool => t) I2 3 cpt_T2 cpt_id cpt_I2 len_T2 len_C2
    len_I2
  have h3 := PvsNP.Units.m2_np_inter _ _ hM h2
  have heq : ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} :
      Language Bool)ᶜ = Lᶜ ⊓ ({x : List Bool | ∀ i : ℕ, i < x.length →
        T2^[i] (I2 x) ∈ ({s : List Bool | ∀ j : ℕ, j < s.length → C1 (T1^[j] (I1 s)) ∈ Lᶜ} :
          Language Bool)} : Language Bool) := by
    first
      | exact Set.ext fun x => main_iff L x
      | (ext x; exact main_iff L x)
  rw [heq]
  exact h3

end PvsNP.Units.tc_closure_rev_factor_conp

/-- coNP is closed under reversing one block (TM2): the complement is an intersection of `Lᶜ`
with a nested scan over all split points (outer) and all block ends (inner), each an NP language
by the generic certificate-list scan `gen_np`. -/
theorem PvsNP.Units.tc_closure_rev_factor_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_rev_factor_conp.main_aux
