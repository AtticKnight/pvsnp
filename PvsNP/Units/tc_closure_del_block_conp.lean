import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_all_prefixes

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_del_block_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.m2_np_all_prefixes

def insAt (u v : List Bool) (j : ℕ) : List Bool :=
  (u ++ v.take j) ++ ([true, false] ++ v.drop j)

theorem insAt_zero (u v : List Bool) :
    insAt u v 0 = u ++ ([true, false] ++ v) := by
  simp [insAt]

theorem insAt_succ (u v : List Bool) (j : ℕ) :
    insAt u v (j + 1) = insAt (u ++ head1 v) v.tail j := by
  cases v with
  | nil => simp [insAt, head1]
  | cons b vt => simp [insAt, head1, List.append_assoc]

def dstep (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let u := (unpairB r1).1
  let r2 := (unpairB r1).2
  let v := (unpairB r2).1
  let rem := (unpairB r2).2
  let w := (unpairB rem).1
  let rem' := (unpairB rem).2
  let cand := u ++ ([true, false] ++ v)
  let flag' := sel flag (boolToFlag (f (cand, w))) [true]
  pairB flag' (pairB (u ++ head1 v) (pairB v.tail rem'))

theorem dstep_length (f : List Bool × List Bool → Bool) (s : List Bool) :
    (dstep f s).length ≤ s.length + 7 := by
  dsimp only [dstep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have h4 := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  have hh := head1_length_le (unpairB (unpairB (unpairB s).2).2).1
  have hfl : (sel (unpairB s).1
      (boolToFlag (f ((unpairB (unpairB s).2).1 ++
        ([true, false] ++ (unpairB (unpairB (unpairB s).2).2).1),
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1)))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs
    · cases f ((unpairB (unpairB s).2).1 ++
        ([true, false] ++ (unpairB (unpairB (unpairB s).2).2).1),
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1) <;> simp [boolToFlag]
    · simp
  omega

theorem cpt_dstep (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (dstep f) := by
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hu := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hv := cpt_unpairB1_1 hr2
  have hrem := cpt_unpairB2_1 hr2
  have hw := cpt_unpairB1_1 hrem
  have hrem' := cpt_unpairB2_1 hrem
  have hcand := cpt_app2 hu (cpt_cons1 true (cpt_cons1 false hv))
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (f ((unpairB (unpairB s).2).1 ++
        ([true, false] ++ (unpairB (unpairB (unpairB s).2).2).1),
        (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))) :=
    cpt_comp (cpt_comp (cpt_pair hcand hw) hf) cpt_boolToFlag
  have hflag' := cpt_sel hflag hok (cpt_const [true])
  have hu' := cpt_app2 hu (cpt_comp hv cpt_head1)
  have hv' := cpt_tail1 hv
  exact cpt_pairB2 hflag' (cpt_pairB2 hu' (cpt_pairB2 hv' hrem'))

theorem dstep_complete (f : List Bool × List Bool → Bool) :
    ∀ (k : ℕ) (u v : List Bool) (ws : List (List Bool)) (hlen : ws.length = k),
      (∀ (j : ℕ) (hj : j < k), f (insAt u v j, ws[j]'(by rw [hlen]; exact hj)) = true) →
      ∃ u' v' rem',
        (dstep f)^[k] (pairB [] (pairB u (pairB v (encCerts ws)))) =
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
      have h0 := hok 0 (Nat.zero_lt_succ k)
      simp only [List.getElem_cons_zero, insAt_zero, List.cons_append, List.nil_append] at h0
      have hst : dstep f (pairB [] (pairB u (pairB v (encCerts (w :: rest))))) =
          pairB [] (pairB (u ++ head1 v) (pairB v.tail (encCerts rest))) := by
        simp [dstep, encCerts, unpairB_pairB, h0, boolToFlag, sel]
      rw [Function.iterate_succ_apply, hst]
      have hlen' : rest.length = k := by
        rw [List.length_cons] at hlen
        exact Nat.succ.inj hlen
      apply ih (u ++ head1 v) v.tail rest hlen'
      intro j hj
      have hj' := hok (j + 1) (Nat.succ_lt_succ hj)
      simp only [List.getElem_cons_succ] at hj'
      rw [insAt_succ u v j] at hj'
      exact hj'

theorem dstep_sound (L : Language Bool) (f : List Bool × List Bool → Bool)
    (hf : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ) :
    ∀ (k : ℕ) (flag u v rem : List Bool),
      ∃ flag' u' v' rem',
        (dstep f)^[k] (pairB flag (pairB u (pairB v rem))) =
          pairB flag' (pairB u' (pairB v' rem')) ∧
        (flag' = [] → flag = [] ∧ ∀ j : ℕ, j < k → insAt u v j ∈ Lᶜ) := by
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
    let cand := u ++ ([true, false] ++ v)
    let flag1 := sel flag (boolToFlag (f (cand, w))) [true]
    have hst : dstep f (pairB flag (pairB u (pairB v rem))) =
        pairB flag1 (pairB (u ++ head1 v) (pairB v.tail rem')) := by
      simp [dstep, unpairB_pairB, w, rem', cand, flag1]
    rw [hst]
    obtain ⟨flag', u', v', rem'', heq, hinv⟩ := ih flag1 (u ++ head1 v) v.tail rem'
    refine ⟨flag', u', v', rem'', heq, fun hfl' => ?_⟩
    obtain ⟨hfl1, hrest⟩ := hinv hfl'
    have hflag0 : flag = [] := by
      by_contra hne
      simp [flag1, sel, hne] at hfl1
    have hfcand : f (cand, w) = true := by
      simp only [flag1, sel, hflag0, ↓reduceIte, boolToFlag] at hfl1
      cases hv : f (cand, w) with
      | true => rfl
      | false => simp [hv] at hfl1
    have hcandL : cand ∈ Lᶜ := hf cand w hfcand
    refine ⟨hflag0, fun j hj => ?_⟩
    cases j with
    | zero =>
      rw [insAt_zero]
      exact hcandL
    | succ j' =>
      rw [insAt_succ u v j']
      exact hrest j' (Nat.lt_of_succ_lt_succ hj)

def runD (f : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (dstep f)^[((unpairB s).1 ++ [true]).length]
    (pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2)))

def verD (f : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runD f (pairB p.1 p.2))).1 = [])

theorem cpt_verD (f : List Bool × List Bool → Bool)
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verD f) := by
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [] (pairB [] (pairB (unpairB s).1 (unpairB s).2))) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB1 cpt_unpairB2))
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1 ++ [true]) :=
    cpt_app2 cpt_unpairB1 (cpt_const [true])
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (runD f) :=
    cpt_iterGrow (cpt_dstep f hf) 7 (dstep_length f) hcnt harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runD f s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runD f s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  unfold verD
  exact cpt_comp cpt_pairB hdecS

theorem main :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} :
        Language Bool) ∈ PvsNP.coNP := by
  classical
  intro L hL
  change ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} :
    Language Bool)ᶜ ∈ PvsNP.NP
  obtain ⟨R, p, ⟨f, hfR, hfc⟩, hlen, hmem⟩ :=
    L045 Lᶜ ((PvsNP.Units.fr_ladner.NP_iff Lᶜ).1 hL)
  have hfL : ∀ u w : List Bool, f (u, w) = true → u ∈ Lᶜ := fun u w h =>
    (hmem u).2 ⟨w, (hfR (u, w)).2 h⟩
  have hbound : ∀ u w : List Bool, f (u, w) = true → w.length ≤ p.eval u.length := fun u w h =>
    hlen u w ((hfR (u, w)).2 h)
  let Q : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C 1) *
      (Polynomial.C 2 * p.comp (Polynomial.X + Polynomial.C 2) + Polynomial.C 1)
  refine ⟨verD f, Q, cpt_verD f hfc, fun x => ?_⟩
  constructor
  · intro hx
    have hexW : ∀ j : ℕ, ∃ w : List Bool,
        j < x.length + 1 → w.length ≤ p.eval (x.length + 2) ∧ f (insAt [] x j, w) = true := by
      intro j
      by_cases hj : j < x.length + 1
      · have hsplit : x = x.take j ++ x.drop j := (List.take_append_drop j x).symm
        have hins_eq : insAt [] x j = x.take j ++ [true, false] ++ x.drop j := by
          simp [insAt, List.append_assoc]
        have hins_mem : insAt [] x j ∈ Lᶜ := by
          intro hmemL
          rw [hins_eq] at hmemL
          exact hx ⟨x.take j, x.drop j, hsplit, hmemL⟩
        have hins_len : (insAt [] x j).length ≤ x.length + 2 := by
          rw [hins_eq]
          have h1 : (x.take j).length + (x.drop j).length = x.length := by
            rw [← List.length_append, List.take_append_drop]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨w, hw⟩ := (hmem (insAt [] x j)).1 hins_mem
        have hfw : f (insAt [] x j, w) = true := (hfR (insAt [] x j, w)).1 hw
        have hwl : w.length ≤ p.eval (x.length + 2) :=
          (hbound (insAt [] x j) w hfw).trans (poly_eval_mono p hins_len)
        exact ⟨w, fun _ => ⟨hwl, hfw⟩⟩
      · exact ⟨[], fun h => absurd h hj⟩
    let pickW : ℕ → List Bool := fun j => Classical.choose (hexW j)
    have hpickW : ∀ j : ℕ, j < x.length + 1 →
        (pickW j).length ≤ p.eval (x.length + 2) ∧ f (insAt [] x j, pickW j) = true :=
      fun j hj => Classical.choose_spec (hexW j) hj
    let ws : List (List Bool) := (List.range (x.length + 1)).map pickW
    let cert : List Bool := encCerts ws
    have hwsLen : ws.length = x.length + 1 := by simp [ws]
    have hwB : ∀ w ∈ ws, w.length ≤ p.eval (x.length + 2) := by
      intro w hw
      simp only [ws, List.mem_map, List.mem_range] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      exact (hpickW j hj).1
    have hcertLen : cert.length ≤ Q.eval x.length := by
      have h1 := encCerts_length_le ws (p.eval (x.length + 2)) hwB
      rw [hwsLen] at h1
      change (encCerts ws).length ≤ Q.eval x.length
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_comp]
      exact h1
    refine ⟨cert, hcertLen, ?_⟩
    have hok : ∀ (j : ℕ) (hj : j < x.length + 1),
        f (insAt [] x j, ws[j]'(by rw [hwsLen]; exact hj)) = true := by
      intro j hj
      have hwj : ws[j]'(by rw [hwsLen]; exact hj) = pickW j := by simp [ws]
      rw [hwj]
      exact (hpickW j hj).2
    obtain ⟨u', v', rem', hrunEq⟩ := dstep_complete f (x.length + 1) [] x ws hwsLen hok
    have hrunD : runD f (pairB x cert) = pairB [] (pairB u' (pairB v' rem')) := by
      unfold runD
      simpa only [unpairB_pairB, List.length_append, List.length_singleton] using hrunEq
    simp [verD, hrunD, unpairB_pairB]
  · rintro ⟨cert, _, hacc⟩
    have hacc' : (unpairB (runD f (pairB x cert))).1 = [] := of_decide_eq_true hacc
    obtain ⟨flag', u', v', rem', hrunEq, hinv⟩ :=
      dstep_sound L f hfL (x.length + 1) [] [] x cert
    have hrunD : runD f (pairB x cert) = pairB flag' (pairB u' (pairB v' rem')) := by
      unfold runD
      simpa only [unpairB_pairB, List.length_append, List.length_singleton] using hrunEq
    rw [hrunD, unpairB_pairB] at hacc'
    obtain ⟨_, hinss⟩ := hinv hacc'
    rintro ⟨u, v, rfl, hmemL⟩
    have hlt : u.length < (u ++ v).length + 1 := by simp
    have h1 := hinss u.length hlt
    have hins_eq : insAt [] (u ++ v) u.length = u ++ [true, false] ++ v := by
      simp [insAt, List.append_assoc]
    rw [hins_eq] at h1
    exact h1 hmemL

end PvsNP.Units.tc_closure_del_block_conp

theorem PvsNP.Units.tc_closure_del_block_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} :
        Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_del_block_conp.main
