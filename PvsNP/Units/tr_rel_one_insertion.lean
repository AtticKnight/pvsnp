import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_np_all_prefixes

namespace PvsNP.Units.tr_rel_one_insertion

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.m2_np_all_prefixes

def delAt (u v : List Bool) (j : ℕ) : List Bool :=
  (u ++ v.take j) ++ (v.drop j).tail

theorem delAt_zero (u v : List Bool) :
    delAt u v 0 = u ++ v.tail := by
  simp [delAt]

theorem delAt_succ (u v : List Bool) (j : ℕ) :
    delAt u v (j + 1) = delAt (u ++ head1 v) v.tail j := by
  cases v with
  | nil => simp [delAt, head1]
  | cons b vt => simp [delAt, head1, List.append_assoc]

def insStep (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let r1 := (unpairB s).2
  let u := (unpairB r1).1
  let r2 := (unpairB r1).2
  let v := (unpairB r2).1
  let x := (unpairB r2).2
  let cand := u ++ v.tail
  let flag' := sel flag [] (boolToFlag (decide (cand = x)))
  pairB flag' (pairB (u ++ head1 v) (pairB v.tail x))

theorem sel_flag_length_le (flag : List Bool) (b : Bool) :
    (sel flag [] (boolToFlag b)).length ≤ 1 := by
  cases flag <;> cases b <;> simp [sel, boolToFlag]

theorem sel_flag_eq_nil_iff (flag : List Bool) (b : Bool) :
    sel flag [] (boolToFlag b) = [] ↔ flag = [] ∨ b = true := by
  cases flag <;> cases b <;> simp [sel, boolToFlag]

theorem insStep_length (s : List Bool) :
    (insStep s).length ≤ s.length + 7 := by
  dsimp only [insStep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hh := head1_length_le (unpairB (unpairB (unpairB s).2).2).1
  have hfl := sel_flag_length_le (unpairB s).1
    (decide ((unpairB (unpairB s).2).1 ++ (unpairB (unpairB (unpairB s).2).2).1.tail =
      (unpairB (unpairB (unpairB s).2).2).2))
  omega

theorem cpt_insStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) insStep := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have heq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    have h := PvsNP.Units.m2_eq_polytime
    rw [henc] at h
    exact h
  have hflag := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hu := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hv := cpt_unpairB1_1 hr2
  have hx := cpt_unpairB2_1 hr2
  have hcand := cpt_app2 hu (cpt_tail1 hv)
  have hok : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => boolToFlag (decide ((unpairB (unpairB s).2).1 ++
        (unpairB (unpairB (unpairB s).2).2).1.tail =
        (unpairB (unpairB (unpairB s).2).2).2))) :=
    cpt_comp (cpt_comp (cpt_pair hcand hx) heq) cpt_boolToFlag
  have hflag' := cpt_sel hflag (cpt_const []) hok
  have hu' := cpt_app2 hu (cpt_comp hv cpt_head1)
  have hv' := cpt_tail1 hv
  exact cpt_pairB2 hflag' (cpt_pairB2 hu' (cpt_pairB2 hv' hx))

theorem insStep_iter (x : List Bool) :
    ∀ (k : ℕ) (flag u v : List Bool),
      ∃ flag' u' v',
        insStep^[k] (pairB flag (pairB u (pairB v x))) =
          pairB flag' (pairB u' (pairB v' x)) ∧
        (flag' = [] ↔ flag = [] ∨ ∃ j < k, delAt u v j = x) := by
  intro k
  induction k with
  | zero =>
    intro flag u v
    refine ⟨flag, u, v, rfl, ?_⟩
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, hj, _⟩)
      · exact h
      · exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro flag u v
    rw [Function.iterate_succ_apply]
    let flag1 := sel flag [] (boolToFlag (decide (u ++ v.tail = x)))
    have hst : insStep (pairB flag (pairB u (pairB v x))) =
        pairB flag1 (pairB (u ++ head1 v) (pairB v.tail x)) := by
      simp [insStep, unpairB_pairB, flag1]
    rw [hst]
    obtain ⟨flag', u', v', heq, hiff⟩ := ih flag1 (u ++ head1 v) v.tail
    refine ⟨flag', u', v', heq, ?_⟩
    rw [hiff]
    have hfl1 : flag1 = [] ↔ flag = [] ∨ u ++ v.tail = x := by
      have h0 := sel_flag_eq_nil_iff flag (decide (u ++ v.tail = x))
      simpa only [flag1, decide_eq_true_eq] using h0
    rw [hfl1]
    constructor
    · rintro ((hfl | heq0) | ⟨j, hj, hdel⟩)
      · exact Or.inl hfl
      · exact Or.inr ⟨0, Nat.zero_lt_succ k, by rw [delAt_zero]; exact heq0⟩
      · exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by rw [delAt_succ]; exact hdel⟩
    · rintro (hfl | ⟨j, hj, hdel⟩)
      · exact Or.inl (Or.inl hfl)
      · cases j with
        | zero =>
          rw [delAt_zero] at hdel
          exact Or.inl (Or.inr hdel)
        | succ j' =>
          rw [delAt_succ] at hdel
          exact Or.inr ⟨j', Nat.lt_of_succ_lt_succ hj, hdel⟩

def runIns (s : List Bool) : List Bool :=
  insStep^[(unpairB s).2.length]
    (pairB [true] (pairB [] (pairB (unpairB s).2 (unpairB s).1)))

def decIns (p : List Bool × List Bool) : Bool :=
  decide ((unpairB (runIns (pairB p.1 p.2))).1 = [])

theorem cpt_decIns :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer decIns := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB [true] (pairB [] (pairB (unpairB s).2 (unpairB s).1))) :=
    cpt_pairB2 (cpt_const [true]) (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB2 cpt_unpairB1))
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) runIns :=
    cpt_iterGrow cpt_insStep 7 insStep_length cpt_unpairB2 harg
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (runIns s)).1) :=
    cpt_unpairB1_1 hrun
  have hdecS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (runIns s)).1 = [])) :=
    cpt_comp hflag cpt_isEmpty
  have hdecP : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool decIns := by
    unfold decIns
    exact cpt_comp cpt_pairB hdecS
  rw [henc]
  exact hdecP

end PvsNP.Units.tr_rel_one_insertion

/-- Whether one string is another with one bit inserted is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_one_insertion :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (∃ (u v : List Bool) (b : Bool), p.1 = u ++ v ∧ p.2 = u ++ b :: v) ↔ f p = true := by
  refine ⟨PvsNP.Units.tr_rel_one_insertion.decIns, PvsNP.Units.tr_rel_one_insertion.cpt_decIns, ?_⟩
  rintro ⟨x, y⟩
  obtain ⟨flag', u', v', hiter, hiff⟩ :=
    PvsNP.Units.tr_rel_one_insertion.insStep_iter x y.length [true] [] y
  have hrun : PvsNP.Units.tr_rel_one_insertion.runIns
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB x y) =
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB flag'
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB u'
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB v' x)) := by
    unfold PvsNP.Units.tr_rel_one_insertion.runIns
    simpa only [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB] using hiter
  unfold PvsNP.Units.tr_rel_one_insertion.decIns
  rw [hrun, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB, decide_eq_true_eq, hiff]
  constructor
  · rintro ⟨u, v, b, rfl, rfl⟩
    refine Or.inr ⟨u.length, by simp, ?_⟩
    simp [PvsNP.Units.tr_rel_one_insertion.delAt]
  · rintro (hcons | ⟨j, hj, hdel⟩)
    · cases hcons
    · have hsplit : y.take j ++ y.drop j = y := List.take_append_drop j y
      cases hdrop : y.drop j with
      | nil =>
        have hlen_drop : (y.drop j).length = 0 := by rw [hdrop]; rfl
        rw [List.length_drop] at hlen_drop
        omega
      | cons b v =>
        have hy_eq : y = y.take j ++ b :: v := hsplit.symm.trans (by rw [hdrop])
        have hdel_eq : PvsNP.Units.tr_rel_one_insertion.delAt [] y j = y.take j ++ v := by
          simp [PvsNP.Units.tr_rel_one_insertion.delAt, hdrop]
        rw [hdel_eq] at hdel
        exact ⟨y.take j, v, b, hdel.symm, hy_eq⟩
