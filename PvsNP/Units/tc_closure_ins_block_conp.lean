import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_all_prefixes

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_ins_block_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.m2_np_all_prefixes

def isTFδ (q : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  match q.val, b with
  | 0, true  => (1, none)
  | 0, false => (2, none)
  | 1, false => (2, some true)
  | 1, true  => (2, none)
  | _, _     => (2, none)

def isTF (v : List Bool) : List Bool :=
  fstRun isTFδ (fun _ => none) 0 v

theorem isTF_state2 (v : List Bool) : fstRun isTFδ (fun _ => none) 2 v = [] := by
  induction v with
  | nil => rfl
  | cons b t ih => simp [fstRun, isTFδ, ih]

theorem isTF_eq (v : List Bool) :
    isTF v = match v with | true :: false :: _ => [true] | _ => [] := by
  cases v with
  | nil => rfl
  | cons a t =>
    cases a with
    | false => simp [isTF, fstRun, isTFδ, isTF_state2]
    | true =>
      cases t with
      | nil => simp [isTF, fstRun, isTFδ]
      | cons b t2 =>
        cases b with
        | false => simp [isTF, fstRun, isTFδ, isTF_state2]
        | true => simp [isTF, fstRun, isTFδ, isTF_state2]

theorem cpt_isTF :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) isTF :=
  fst_polyTime _ _ _ isTFδ (fun _ => none) 0 (fun _ => rfl)

def ibstep (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let u := (unpairB r1).1
  let r2 := (unpairB r1).2
  let v := (unpairB r2).1
  let rem := (unpairB r2).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let cand := u ++ v.tail.tail
  let stepFlag := sel (isTF v) [] (boolToFlag (f (cand, w)))
  let flag' := sel flag stepFlag [true]
  pairB flag' (pairB (u ++ head1 v) (pairB v.tail rem'))

theorem ibstep_length (f : List Bool × List Bool → Bool) (s : List Bool) :
    (ibstep f s).length ≤ s.length + 7 := by
  dsimp only [ibstep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have h4 := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  have hh := head1_length_le (unpairB (unpairB (unpairB s).2).2).1
  have hfl : (sel (unpairB s).1
      (sel (isTF (unpairB (unpairB (unpairB s).2).2).1) []
        (boolToFlag (f ((unpairB (unpairB s).2).1 ++
          (unpairB (unpairB (unpairB s).2).2).1.tail.tail,
          (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs
    · simp
    · cases f ((unpairB (unpairB s).2).1 ++
        (unpairB (unpairB (unpairB s).2).2).1.tail.tail,
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1) <;> simp [boolToFlag]
    · simp
  omega

theorem cpt_ibstep (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (ibstep f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hu := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hv := cpt_unpairB1_1 hr2
  have hrem := cpt_unpairB2_1 hr2
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hcand := cpt_app2 hu (cpt_tail1 (cpt_tail1 hv))
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f ((unpairB (unpairB s).2).1 ++
        (unpairB (unpairB (unpairB s).2).2).1.tail.tail,
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair hcand hw) hf) cpt_boolToFlag
  have hsf := cpt_sel (cpt_comp hv cpt_isTF) (cpt_const []) hok
  have hflag' := cpt_sel hflag hsf (cpt_const [true])
  have hu' := cpt_app2 hu (cpt_comp hv cpt_head1)
  have hv' := cpt_tail1 hv
  exact cpt_pairB2 hflag' (cpt_pairB2 hu' (cpt_pairB2 hv' hrem'))

def ibAt (u v : List Bool) (j : ℕ) : List Bool :=
  (u ++ v.take j) ++ (v.drop j).tail.tail

theorem ibAt_zero (u v : List Bool) :
    ibAt u v 0 = u ++ v.tail.tail := by
  simp [ibAt]

theorem ibAt_succ (u v : List Bool) (j : ℕ) :
    ibAt u v (j + 1) = ibAt (u ++ head1 v) v.tail j := by
  cases v with
  | nil => simp [ibAt, head1]
  | cons b vt => simp [ibAt, head1, List.append_assoc]

theorem drop_succ_eq (v : List Bool) (j : ℕ) :
    v.drop (j + 1) = v.tail.drop j := by
  cases v with
  | nil => simp
  | cons b vt => simp

theorem ibstep_complete (f : List Bool × List Bool → Bool) :
    ∀ (k : ℕ) (u v : List Bool) (ws : List (List Bool)) (hlen : ws.length = k),
      (∀ (j : ℕ) (hj : j < k), isTF (v.drop j) ≠ [] →
        f (ibAt u v j, ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ u' v' rem',
        (ibstep f)^[k] (pairB [] (pairB u (pairB v (encCerts ws)))) =
          pairB [] (pairB u' (pairB v' rem')) := by
  intro k
  induction k with
  | zero =>
    intro u v ws _ _
    exact ⟨u, v, encCerts ws, rfl⟩
  | succ k ih =>
    intro u v ws hlen hok
    cases ws with
    | nil => cases hlen
    | cons w rest =>
      have hsf0 : sel (isTF v) [] (boolToFlag (f (u ++ v.tail.tail, w))) = [] := by
        by_cases htf : isTF v = []
        · simp [sel, htf]
        · have h0 := hok 0 (Nat.zero_lt_succ k) (by simpa using htf)
          simp only [List.getElem_cons_zero, ibAt_zero] at h0
          simp [sel, htf, h0, boolToFlag]
      have hst : ibstep f (pairB [] (pairB u (pairB v (encCerts (w :: rest))))) =
          pairB [] (pairB (u ++ head1 v) (pairB v.tail (encCerts rest))) := by
        simp only [ibstep, encCerts, unpairB_pairB, hsf0]
        rfl
      rw [Function.iterate_succ_apply, hst]
      have hlen' : rest.length = k := by
        rw [List.length_cons] at hlen
        exact Nat.succ.inj hlen
      apply ih (u ++ head1 v) v.tail rest hlen'
      intro j hj htf
      have hj' := hok (j + 1) (Nat.succ_lt_succ hj) (by rwa [drop_succ_eq])
      simp only [List.getElem_cons_succ] at hj'
      rw [ibAt_succ u v j] at hj'
      exact hj'

theorem ibstep_sound (L : Language Bool) (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ) :
    ∀ (k : ℕ) (flag u v rem : List Bool),
      ∃ flag' u' v' rem',
        (ibstep f)^[k] (pairB flag (pairB u (pairB v rem))) =
          pairB flag' (pairB u' (pairB v' rem')) ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < k → isTF (v.drop j) ≠ [] → ibAt u v j ∈ Lᶜ) := by
  intro k
  induction k with
  | zero =>
    intro flag u v rem
    refine ⟨flag, u, v, rem, rfl, fun hfl => ⟨hfl, fun j hj _ => absurd hj (Nat.not_lt_zero j)⟩⟩
  | succ k ih =>
    intro flag u v rem
    rw [Function.iterate_succ_apply]
    let w := (unpairB rem).1
    let rem' := (unpairB rem).2
    let cand := u ++ v.tail.tail
    let sf := sel (isTF v) [] (boolToFlag (f (cand, w)))
    let flag1 := sel flag sf [true]
    have hst : ibstep f (pairB flag (pairB u (pairB v rem))) =
        pairB flag1 (pairB (u ++ head1 v) (pairB v.tail rem')) := by
      simp [ibstep, unpairB_pairB, w, rem', cand, sf, flag1]
    rw [hst]
    obtain ⟨flag', u', v', rem'', heq, hinv⟩ := ih flag1 (u ++ head1 v) v.tail rem'
    refine ⟨flag', u', v', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hsf0 : sf = [] := by
      simpa [flag1, sel, hflag0] using hfl1
    refine ⟨hflag0, fun j hj htf => ?_⟩
    cases j with
    | zero =>
      rw [ibAt_zero]
      simp only [List.drop_zero] at htf
      have hfcand : f (cand, w) = true := by
        simp only [sf, sel, htf, ↓reduceIte, boolToFlag] at hsf0
        cases hv : f (cand, w) with
        | true => rfl
        | false => simp [hv] at hsf0
      exact hf cand w hfcand
    | succ j' =>
      rw [ibAt_succ u v j']
      rw [drop_succ_eq] at htf
      exact hrest j' (Nat.lt_of_succ_lt_succ hj) htf

def runIB (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (ibstep f)^[(unpairB s).1.length]
    (pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2)))

def verIB (f : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runIB f (pairB p.1 p.2))).1 = [])

theorem cpt_verIB (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verIB f) := by
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2))) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB1 cpt_unpairB2))
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runIB f) :=
    cpt_iterGrow (cpt_ibstep f hf) 7 (ibstep_length f) cpt_unpairB1 harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runIB f s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runIB f s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  unfold verIB
  exact cpt_comp cpt_pairB hdecS

theorem main :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L} :
        Language Bool) ∈ PvsNP.coNP := by
  classical
  intro L hL
  change ({x : List Bool | ∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L} :
    Language Bool)ᶜ ∈ PvsNP.NP
  obtain ⟨R, p, ⟨f, hfR, hfc⟩, hlen, hmem⟩ :=
    L045 Lᶜ ((PvsNP.Units.fr_ladner.NP_iff Lᶜ).1 hL)
  have hfL : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ := fun u w h =>
    (hmem u).2 ⟨w, (hfR (u, w)).2 h⟩
  have hbound : ∀ u w : List Bool, f (u, w) = true → w.length ≤ p.eval u.length := fun u w h =>
    hlen u w ((hfR (u, w)).2 h)
  let Q : Polynomial ℕ := Polynomial.X * (Polynomial.C 2 * p + Polynomial.C 1)
  refine ⟨verIB f, Q, cpt_verIB f hfc, fun x => ?_⟩
  constructor
  · intro hx
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        w.length ≤ p.eval x.length ∧
        (j < x.length → isTF (x.drop j) ≠ [] → f (ibAt [] x j, w) = true) := by
      intro j
      by_cases hcond : j < x.length ∧ isTF (x.drop j) ≠ []
      · rcases hcond with ⟨hj, htf⟩
        have hsplit : x = x.take j ++ x.drop j := (List.take_append_drop j x).symm
        cases hdrop : x.drop j with
        | nil => rw [hdrop, isTF_eq] at htf; exact absurd rfl htf
        | cons a rest1 =>
          cases a with
          | false => rw [hdrop, isTF_eq] at htf; exact absurd rfl htf
          | true =>
            cases rest1 with
            | nil => rw [hdrop, isTF_eq] at htf; exact absurd rfl htf
            | cons b v =>
              cases b with
              | true => rw [hdrop, isTF_eq] at htf; exact absurd rfl htf
              | false =>
                have hx_eq : x = x.take j ++ [true, false] ++ v := by
                  rw [hdrop] at hsplit; simpa [List.append_assoc] using hsplit
                have hib_eq : ibAt [] x j = x.take j ++ v := by
                  simp [ibAt, hdrop]
                have hib_mem : ibAt [] x j ∈ Lᶜ := by
                  intro hmemL
                  rw [hib_eq] at hmemL
                  exact hx ⟨x.take j, v, hx_eq, hmemL⟩
                have hib_len : (ibAt [] x j).length ≤ x.length := by
                  have h1 : (ibAt [] x j).length = (x.take j ++ v).length := congrArg List.length hib_eq
                  have h2 : x.length = (x.take j ++ [true, false] ++ v).length := congrArg List.length hx_eq
                  simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2
                  omega
                obtain ⟨w, hw⟩ := (hmem (ibAt [] x j)).1 hib_mem
                have hfw : f (ibAt [] x j, w) = true := (hfR (ibAt [] x j, w)).1 hw
                have hwl : w.length ≤ p.eval x.length :=
                  (hbound (ibAt [] x j) w hfw).trans (poly_eval_mono p hib_len)
                exact ⟨w, hwl, fun _ _ => hfw⟩
      · exact ⟨[], Nat.zero_le _, fun hj htf => absurd ⟨hj, htf⟩ hcond⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ, (pickW j).length ≤ p.eval x.length ∧
        (j < x.length → isTF (x.drop j) ≠ [] → f (ibAt [] x j, pickW j) = true) :=
      fun j => Classical.choose_spec (hexW j)
    let ws : List (List Bool) := (List.range x.length).map pickW
    let cert : List Bool := encCerts ws
    have hwsLen : ws.length = x.length := by simp [ws]
    have hwB : ∀ w ∈ ws, w.length ≤ p.eval x.length := by
      intro w hw
      simp only [ws, List.mem_map, List.mem_range] at hw
      obtain ⟨j, _, rfl⟩ := hw
      exact (hpickW j).1
    have hcertLen : cert.length ≤ Q.eval x.length := by
      have h1 := encCerts_length_le ws (p.eval x.length) hwB
      rw [hwsLen] at h1
      change (encCerts ws).length ≤ Q.eval x.length
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      exact h1
    refine ⟨cert, hcertLen, ?_⟩
    have hok : ∀ (j : ℕ) (hj : j < x.length), isTF (x.drop j) ≠ [] →
        f (ibAt [] x j, ws[j]'(by rw [hwsLen]; exact hj)) = true := by
      intro j hj htf
      have hwj : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by simp [ws]
      rw [hwj]
      exact (hpickW j).2 hj htf
    obtain ⟨u', v', rem', hrunEq⟩ := ibstep_complete f x.length [] x ws hwsLen hok
    have hrunIB : runIB f (pairB x cert) = pairB [] (pairB u' (pairB v' rem')) := by
      unfold runIB
      simpa only [unpairB_pairB] using hrunEq
    simp [verIB, hrunIB, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runIB f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', u', v', rem', hrunEq, hinv⟩ :=
      ibstep_sound L f hfL x.length [] [] x cert
    have hrunIB : runIB f (pairB x cert) = pairB flag' (pairB u' (pairB v' rem')) := by
      unfold runIB
      simpa only [unpairB_pairB] using hrunEq
    rw [hrunIB, unpairB_pairB] at hacc'
    obtain ⟨_, hibs⟩ := hinv hacc'
    rintro ⟨u, v, rfl, hmemL⟩
    have hlt : u.length < (u ++ [true, false] ++ v).length := by simp
    have hdrop : (u ++ [true, false] ++ v).drop u.length = true :: false :: v := by
      rw [List.append_assoc, List.drop_left]; rfl
    have htf : isTF ((u ++ [true, false] ++ v).drop u.length) ≠ [] := by
      rw [hdrop, isTF_eq]; simp
    have h1 := hibs u.length hlt htf
    have hib_eq : ibAt [] (u ++ [true, false] ++ v) u.length = u ++ v := by
      have ht : (u ++ [true, false] ++ v).take u.length = u := by
        rw [List.append_assoc, List.take_left]
      simp [ibAt, ht, hdrop]
    rw [hib_eq] at h1
    exact h1 hmemL

end PvsNP.Units.tc_closure_ins_block_conp

theorem PvsNP.Units.tc_closure_ins_block_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L} :
        Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_ins_block_conp.main
