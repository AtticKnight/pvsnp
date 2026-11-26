import Mathlib
import PvsNP.Defs
import CookLevin

/-
Original proof of `PvsNP.Units.m3_sat_to_3occ_sat`: reduces `SATStr` in polynomial time
to 3-occurrence SAT (`∀ v, ((SATStr.cnfOf y).flatten.countP (fun l => l.2 == v)) ≤ 3 ∧ SAT (SATStr.cnfOf y)`).

Algorithm (implemented directly in `CookLevin.Lang.Cmd` and compiled via
`PolyTimeComputableLang.toMachine` with automatic polynomial cost via `Cmd.costLeSize_of_chk`):
1. Run `SATStr.satStrBuild` so register `CNF_STREAM` (`= 2`) holds `encodeCnf (SATStr.cnfOf x)`
   (replacing any malformed input by `encodeCnf [[]] = [0]`) and register `0` (`OUT`) is `[]`.
2. Pass 1 (`forBnd POS CNF_STREAM`): scan `encodeCnf N`; replace every literal `(pol, v)`
   whose terminating `0` sits at bit index `p` with `(pol, p)`. Since distinct literals have
   strictly increasing terminating indices `p`, every variable appears at most once in Pass 1.
3. Pass 2 (`forBnd V CNF_STREAM`): for each original variable `v < (encodeCnf N).length`,
   scan `encodeCnf N` to collect the fresh IDs `p₁ < p₂ < ... < pₖ` of occurrences of `v`.
   When `k ≥ 2`, emit the implication cycle `(¬p₁ ∨ p₂), ..., (¬pₖ₋₁ ∨ pₖ), (¬pₖ ∨ p₁)`.
   Each fresh ID `pᵢ` appears at most once negatively and once positively across all cycle
   clauses (hence `≤ 1 + 2 = 3` times total), and the cycle forces all occurrences of `v`
   to share one truth value, preserving satisfiability.
-/

namespace PvsNP.Units.m3_sat_to_3occ_sat

open CookLevin CookLevin.Lang EvalCnfCmd CnfWellFormed

/-! ### Registers (all `< 25`, disjoint from `SATStr`'s `0..3`, `19..24`) -/

abbrev OUT : Var := 0
abbrev INP : Var := 2
abbrev CUR : Var := 4
abbrev POS : Var := 5
abbrev HD : Var := 6
abbrev IN_LIT : Var := 7
abbrev GOT_POL : Var := 8
abbrev POL : Var := 9
abbrev VREG : Var := 10
abbrev CUR_VAR : Var := 11
abbrev EQ : Var := 12
abbrev HAS_FIRST : Var := 13
abbrev MULTI : Var := 14
abbrev FIRST_ID : Var := 15
abbrev PREV_ID : Var := 16

/-! ### Pure CNF transformation `to3Occ` -/

def rewriteClause (off : Nat) : clause → clause × Nat
  | [] => ([], off + 1)
  | (pol, v) :: C =>
      let q := off + v + 2
      let (C', off') := rewriteClause (q + 1) C
      ((pol, q) :: C', off')

def rewriteCnf (off : Nat) : cnf → cnf × Nat
  | [] => ([], off)
  | C :: N =>
      let (C', off1) := rewriteClause off C
      let (N', off2) := rewriteCnf off1 N
      (C' :: N', off2)

def occClause (v : var) (off : Nat) : clause → List Nat × Nat
  | [] => ([], off + 1)
  | (_, u) :: C =>
      let q := off + u + 2
      let (qs, off') := occClause v (q + 1) C
      (if u == v then q :: qs else qs, off')

def occCnf (v : var) (off : Nat) : cnf → List Nat × Nat
  | [] => ([], off)
  | C :: N =>
      let (qs1, off1) := occClause v off C
      let (qs2, off2) := occCnf v off1 N
      (qs1 ++ qs2, off2)

def impChain (prev : Nat) : List Nat → cnf
  | [] => []
  | q :: qs => [(false, prev), (true, q)] :: impChain q qs

def cycleClauses : List Nat → cnf
  | [] => []
  | [_] => []
  | first :: q :: qs => impChain first (q :: qs) ++ [[(false, (q :: qs).getLast (by simp)), (true, first)]]

def allCycles (N : cnf) : cnf :=
  (List.range (encodeCnf N).length).flatMap (fun v => cycleClauses (occCnf v 0 N).1)

def to3Occ (N : cnf) : cnf :=
  (rewriteCnf 0 N).1 ++ allCycles N

/-! ### Structural properties of `rewriteCnf`, `occCnf`, and `cycleClauses` -/

theorem encodeLit_len (l : literal) : (encodeLit l).length = l.2 + 3 := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).length = v + 3
  simp

theorem rewriteClause_snd (off : Nat) (C : clause) :
    (rewriteClause off C).2 = off + (encodeClause C).length := by
  induction C generalizing off with
  | nil => rfl
  | cons l C ih =>
      rcases l with ⟨pol, v⟩
      simp only [rewriteClause, CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons,
        List.length_append, encodeLit_len]
      have h := ih (off + v + 2 + 1)
      simp only [CnfSerialize.encodeClause_eq, List.length_append] at h
      omega

theorem rewriteCnf_snd (off : Nat) (N : cnf) :
    (rewriteCnf off N).2 = off + (encodeCnf N).length := by
  induction N generalizing off with
  | nil => rfl
  | cons C N ih =>
      simp only [rewriteCnf, CnfSerialize.encodeCnf_cons, List.length_append]
      rw [rewriteClause_snd, ih]
      omega

theorem occClause_snd (v : var) (off : Nat) (C : clause) :
    (occClause v off C).2 = off + (encodeClause C).length := by
  induction C generalizing off with
  | nil => rfl
  | cons l C ih =>
      rcases l with ⟨pol, u⟩
      simp only [occClause, CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons,
        List.length_append, encodeLit_len]
      have h := ih (off + u + 2 + 1)
      simp only [CnfSerialize.encodeClause_eq, List.length_append] at h
      omega

theorem occCnf_snd (v : var) (off : Nat) (N : cnf) :
    (occCnf v off N).2 = off + (encodeCnf N).length := by
  induction N generalizing off with
  | nil => rfl
  | cons C N ih =>
      simp only [occCnf, CnfSerialize.encodeCnf_cons, List.length_append]
      rw [occClause_snd, ih]
      omega

theorem rewriteClause_vars_range (off : Nat) (C : clause) :
    ∀ l ∈ (rewriteClause off C).1, off ≤ l.2 ∧ l.2 < (rewriteClause off C).2 := by
  induction C generalizing off with
  | nil => intro l hl; simp [rewriteClause] at hl
  | cons a C ih =>
      rcases a with ⟨pol, v⟩
      intro l hl
      rw [rewriteClause_snd]
      have hlen : (encodeClause ((pol, v) :: C)).length = v + 3 + (encodeClause C).length := by
        rw [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons, CnfSerialize.encodeClause_eq]
        simp only [List.length_append, encodeLit_len]; omega
      rw [hlen]
      simp only [rewriteClause, List.mem_cons] at hl
      rcases hl with rfl | hl
      · refine ⟨Nat.le_trans (Nat.le_add_right off v) (Nat.le_add_right _ 2), ?_⟩
        dsimp only
        rw [← Nat.add_assoc, ← Nat.add_assoc]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 2 < 3) (off + v)) (Nat.le_add_right _ _)
      · have h1 := ih (off + v + 2 + 1) l hl
        rw [rewriteClause_snd] at h1
        refine ⟨Nat.le_trans (Nat.le_trans (Nat.le_add_right off v) (Nat.le_add_right _ 2))
                  (Nat.le_trans (Nat.le_succ _) h1.1), ?_⟩
        have hsum : off + v + 2 + 1 + (encodeClause C).length = off + (v + 3 + (encodeClause C).length) := by
          rw [Nat.add_assoc off v 2, Nat.add_assoc off (v + 2) 1, Nat.add_assoc v 2 1, Nat.add_assoc off (v + 3)]
        exact hsum ▸ h1.2

theorem rewriteCnf_vars_range (off : Nat) (N : cnf) :
    ∀ l ∈ (rewriteCnf off N).1.flatten, off ≤ l.2 ∧ l.2 < (rewriteCnf off N).2 := by
  induction N generalizing off with
  | nil => intro l hl; simp [rewriteCnf] at hl
  | cons C N ih =>
      intro l hl
      rw [rewriteCnf_snd, CnfSerialize.encodeCnf_cons, List.length_append]
      simp only [rewriteCnf, List.flatten_cons, List.mem_append] at hl
      rcases hl with h1 | h2
      · have hr := rewriteClause_vars_range off C l h1
        rw [rewriteClause_snd] at hr
        exact ⟨hr.1, Nat.lt_of_lt_of_le hr.2 (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _)⟩
      · have hr := ih (rewriteClause off C).2 l h2
        rw [rewriteCnf_snd, rewriteClause_snd] at hr
        refine ⟨Nat.le_trans (Nat.le_add_right off (encodeClause C).length) hr.1, ?_⟩
        rw [← Nat.add_assoc]
        exact hr.2

theorem rewriteClause_countP_le_one (off : Nat) (C : clause) (w : var) :
    (rewriteClause off C).1.countP (fun l => l.2 == w) ≤ 1 := by
  induction C generalizing off with
  | nil => simp [rewriteClause]
  | cons a C ih =>
      rcases a with ⟨pol, v⟩
      simp only [rewriteClause, List.countP_cons]
      by_cases hw : off + v + 2 = w
      · have hzero : (rewriteClause (off + v + 2 + 1) C).1.countP (fun l => l.2 == w) = 0 := by
          rw [List.countP_eq_zero]
          intro l hl
          have hr := rewriteClause_vars_range (off + v + 2 + 1) C l hl
          have hlt : w < l.2 := Nat.lt_of_lt_of_le (hw ▸ Nat.lt_succ_self (off + v + 2)) hr.1
          simp [Nat.ne_of_gt hlt]
        rw [hzero]; simp [hw]
      · have hne : (off + v + 2 == w) = false := beq_false_of_ne hw
        rw [hne]
        simpa using ih (off + v + 2 + 1)

theorem rewriteCnf_countP_le_one (off : Nat) (N : cnf) (w : var) :
    (rewriteCnf off N).1.flatten.countP (fun l => l.2 == w) ≤ 1 := by
  induction N generalizing off with
  | nil => simp [rewriteCnf]
  | cons C N ih =>
      simp only [rewriteCnf, List.flatten_cons, List.countP_append]
      by_cases hlt : w < (rewriteClause off C).2
      · have hzero : (rewriteCnf (rewriteClause off C).2 N).1.flatten.countP (fun l => l.2 == w) = 0 := by
          rw [List.countP_eq_zero]
          intro l hl
          have hr := rewriteCnf_vars_range (rewriteClause off C).2 N l hl
          simp [Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hr.1)]
        rw [hzero, Nat.add_zero]
        exact rewriteClause_countP_le_one off C w
      · have hzero : (rewriteClause off C).1.countP (fun l => l.2 == w) = 0 := by
          rw [List.countP_eq_zero]
          intro l hl
          have hr := rewriteClause_vars_range off C l hl
          simp [Nat.ne_of_lt (Nat.lt_of_lt_of_le hr.2 (Nat.le_of_not_lt hlt))]
        rw [hzero, Nat.zero_add]
        exact ih (rewriteClause off C).2

theorem occClause_range (v : var) (off : Nat) (C : clause) :
    ∀ q ∈ (occClause v off C).1, off ≤ q ∧ q < (occClause v off C).2 := by
  induction C generalizing off with
  | nil => intro q hq; simp [occClause] at hq
  | cons a C ih =>
      rcases a with ⟨pol, u⟩
      intro q hq
      have hs1 := occClause_snd v off ((pol, u) :: C)
      have hs2 := occClause_snd v (off + u + 2 + 1) C
      have hlen : (encodeClause ((pol, u) :: C)).length = u + 3 + (encodeClause C).length := by
        rw [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons, CnfSerialize.encodeClause_eq]
        simp only [List.length_append, encodeLit_len]; omega
      simp only [occClause] at hq
      split_ifs at hq with huv
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · omega
        · have h1 := ih (off + u + 2 + 1) q hq
          omega
      · have h1 := ih (off + u + 2 + 1) q hq
        omega

theorem occCnf_range (v : var) (off : Nat) (N : cnf) :
    ∀ q ∈ (occCnf v off N).1, off ≤ q ∧ q < (occCnf v off N).2 := by
  induction N generalizing off with
  | nil => intro q hq; simp [occCnf] at hq
  | cons C N ih =>
      intro q hq
      have hs0 := occCnf_snd v off (C :: N)
      have hs1 := occClause_snd v off C
      have hs2 := occCnf_snd v (occClause v off C).2 N
      have hlen : (encodeCnf (C :: N)).length = (encodeClause C).length + (encodeCnf N).length := by
        rw [CnfSerialize.encodeCnf_cons, List.length_append]
      simp only [occCnf, List.mem_append] at hq
      rcases hq with h1 | h2
      · have hr := occClause_range v off C q h1
        omega
      · have hr := ih (occClause v off C).2 q h2
        omega

theorem occClause_nodup (v : var) (off : Nat) (C : clause) :
    (occClause v off C).1.Nodup := by
  induction C generalizing off with
  | nil => simp [occClause]
  | cons a C ih =>
      rcases a with ⟨pol, u⟩
      simp only [occClause]
      split_ifs
      · refine List.nodup_cons.mpr ⟨?_, ih (off + u + 2 + 1)⟩
        intro hmem
        have hr := occClause_range v (off + u + 2 + 1) C _ hmem
        omega
      · exact ih (off + u + 2 + 1)

theorem occCnf_nodup (v : var) (off : Nat) (N : cnf) :
    (occCnf v off N).1.Nodup := by
  induction N generalizing off with
  | nil => simp [occCnf]
  | cons C N ih =>
      simp only [occCnf]
      rw [List.nodup_append]
      refine ⟨occClause_nodup v off C, ih (occClause v off C).2, ?_⟩
      intro a ha b hb hab
      subst hab
      have h1 := occClause_range v off C a ha
      have h2 := occCnf_range v (occClause v off C).2 N a hb
      omega

theorem occClause_disjoint (v₁ v₂ : var) (hne : v₁ ≠ v₂) (off : Nat) (C : clause) :
    ∀ q, q ∈ (occClause v₁ off C).1 → q ∉ (occClause v₂ off C).1 := by
  induction C generalizing off with
  | nil => intro q hq; simp [occClause] at hq
  | cons a C ih =>
      rcases a with ⟨pol, u⟩
      intro q h1 h2
      simp only [occClause] at h1 h2
      by_cases hu1 : u = v₁
      · have hu2 : u ≠ v₂ := fun heq => hne (hu1.symm.trans heq)
        have hb1 : (u == v₁) = true := beq_iff_eq.mpr hu1
        have hb2 : (u == v₂) = false := beq_false_of_ne hu2
        simp only [hb1, hb2, ite_true, Bool.false_eq_true, ite_false, List.mem_cons] at h1 h2
        rcases h1 with rfl | h1'
        · have hr := occClause_range v₂ (off + u + 2 + 1) C _ h2; omega
        · exact ih (off + u + 2 + 1) q h1' h2
      · have hb1 : (u == v₁) = false := beq_false_of_ne hu1
        simp only [hb1, Bool.false_eq_true, ite_false] at h1
        by_cases hu2 : u = v₂
        · have hb2 : (u == v₂) = true := beq_iff_eq.mpr hu2
          simp only [hb2, ite_true, List.mem_cons] at h2
          rcases h2 with rfl | h2'
          · have hr := occClause_range v₁ (off + u + 2 + 1) C _ h1; omega
          · exact ih (off + u + 2 + 1) q h1 h2'
        · have hb2 : (u == v₂) = false := beq_false_of_ne hu2
          simp only [hb2, Bool.false_eq_true, ite_false] at h2
          exact ih (off + u + 2 + 1) q h1 h2

theorem occCnf_disjoint (v₁ v₂ : var) (hne : v₁ ≠ v₂) (off : Nat) (N : cnf) :
    ∀ q, q ∈ (occCnf v₁ off N).1 → q ∉ (occCnf v₂ off N).1 := by
  induction N generalizing off with
  | nil => intro q hq; simp [occCnf] at hq
  | cons C N ih =>
      intro q h1 h2
      simp only [occCnf, List.mem_append] at h1 h2
      have hsnd : (occClause v₁ off C).2 = (occClause v₂ off C).2 := by
        rw [occClause_snd, occClause_snd]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact occClause_disjoint v₁ v₂ hne off C q h1 h2
      · have r1 := occClause_range v₁ off C q h1
        have r2 := occCnf_range v₂ (occClause v₂ off C).2 N q h2
        omega
      · have r1 := occCnf_range v₁ (occClause v₁ off C).2 N q h1
        have r2 := occClause_range v₂ off C q h2
        omega
      · rw [hsnd] at h1
        exact ih (occClause v₂ off C).2 q h1 h2

/-! ### Clean exact occurrence count for `impChain` and `cycleClauses` -/

theorem impChain_countP_eq (prev : Nat) (q : Nat) (qs : List Nat)
    (hnd : (prev :: q :: qs).Nodup) (w : var) :
    (impChain prev (q :: qs)).flatten.countP (fun l => l.2 == w) +
      (if w = (q :: qs).getLast (by simp) then 1 else 0) +
      (if w = prev then 1 else 0) =
    if w ∈ prev :: q :: qs then 2 else 0 := by
  induction qs generalizing prev q with
  | nil =>
      simp only [impChain, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.countP_cons, List.countP_nil, List.getLast_singleton, List.mem_cons,
        List.not_mem_nil, or_false]
      have hne : prev ≠ q := by
        have h1 := (List.nodup_cons.mp hnd).1
        simpa using h1
      by_cases hp : w = prev
      · subst hp
        have hne' : (q == w) = false := beq_false_of_ne (Ne.symm hne)
        simp [hne', hne]
      · by_cases hq : w = q
        · subst hq
          have hne' : (prev == w) = false := beq_false_of_ne hne
          simp [hne', Ne.symm hne]
        · have hp' : (prev == w) = false := beq_false_of_ne (Ne.symm hp)
          have hq' : (q == w) = false := beq_false_of_ne (Ne.symm hq)
          simp [hp', hq', hp, hq]
  | cons q2 rest ih =>
      have hnd_tail : (q :: q2 :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hp_not_in : prev ∉ q :: q2 :: rest := (List.nodup_cons.mp hnd).1
      have hih := ih q q2 hnd_tail
      simp only [impChain, List.flatten_cons, List.countP_append, List.countP_cons,
        List.countP_nil] at hih ⊢
      have hlast : (q :: q2 :: rest).getLast (by simp) = (q2 :: rest).getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hlast]
      by_cases hp : w = prev
      · subst hp
        have hwnot : w ∉ q :: q2 :: rest := hp_not_in
        have hwneq : w ≠ q := fun h => hwnot (by simp [h])
        have hwneL : w ≠ (q2 :: rest).getLast (by simp) := fun h =>
          hwnot (List.mem_cons_of_mem _ (h ▸ List.getLast_mem (by simp)))
        simp only [hwnot, ite_false, hwneq, hwneL] at hih
        have h1 : (q == w) = false := beq_false_of_ne (Ne.symm hwneq)
        have hmemw : w ∈ w :: q :: q2 :: rest := by simp
        simp only [h1, Bool.false_eq_true, beq_self_eq_true, ite_true, ite_false, hwneL, hmemw] at hih ⊢
        omega
      · have h1 : (prev == w) = false := beq_false_of_ne (Ne.symm hp)
        by_cases hq : w = q
        · subst hq
          have hmem : w ∈ w :: q2 :: rest := by simp
          simp only [hmem, ite_true] at hih
          have hmem2 : w ∈ prev :: w :: q2 :: rest := by simp
          simp only [hmem2, ite_true, hp, ite_false, h1, Bool.false_eq_true, beq_self_eq_true] at hih ⊢
          omega
        · have h2 : (q == w) = false := beq_false_of_ne (Ne.symm hq)
          have hiff : w ∈ prev :: q :: q2 :: rest ↔ w ∈ q :: q2 :: rest := by
            simp [hp]
          simp only [hiff, hp, hq, ite_false, h1, h2, Bool.false_eq_true] at hih ⊢
          omega

theorem cycleClauses_countP (L : List Nat) (hnd : L.Nodup) (w : var) :
    (cycleClauses L).flatten.countP (fun l => l.2 == w) ≤ if w ∈ L then 2 else 0 := by
  cases L with
  | nil => simp [cycleClauses]
  | cons first rest =>
      cases rest with
      | nil => simp [cycleClauses]
      | cons q qs =>
          simp only [cycleClauses, List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.countP_append, List.countP_cons, List.countP_nil]
          have h := impChain_countP_eq first q qs hnd w
          have hlast : ((q :: qs).getLast (by simp) == w) = decide (w = (q :: qs).getLast (by simp)) := by
            by_cases he : w = (q :: qs).getLast (by simp)
            · simp [he]
            · simp [he, beq_false_of_ne (Ne.symm he)]
          have hfirst : (first == w) = decide (w = first) := by
            by_cases he : w = first
            · simp [he]
            · simp [he, beq_false_of_ne (Ne.symm he)]
          rw [hlast, hfirst]
          by_cases h1 : w = (q :: qs).getLast (by simp) <;>
            by_cases h2 : w = first <;>
            simp [h1, h2] at h ⊢ <;> omega

theorem allCycles_countP_le_two (N : cnf) (w : var) :
    (allCycles N).flatten.countP (fun l => l.2 == w) ≤ 2 := by
  unfold allCycles
  have hgen : ∀ (vs : List Nat), vs.Nodup →
      (vs.flatMap (fun v => cycleClauses (occCnf v 0 N).1)).flatten.countP (fun l => l.2 == w) ≤
        if ∃ v ∈ vs, w ∈ (occCnf v 0 N).1 then 2 else 0 := by
    intro vs hnd
    induction vs with
    | nil => simp
    | cons v rest ih =>
        obtain ⟨hv_not, hnd_rest⟩ := List.nodup_cons.mp hnd
        simp only [List.flatMap_cons, List.flatten_append, List.countP_append]
        have h1 := cycleClauses_countP (occCnf v 0 N).1 (occCnf_nodup v 0 N) w
        have h2 := ih hnd_rest
        by_cases hwv : w ∈ (occCnf v 0 N).1
        · have hno : ¬ ∃ u ∈ rest, w ∈ (occCnf u 0 N).1 := by
            rintro ⟨u, hu, hwu⟩
            have hne : v ≠ u := fun heq => hv_not (heq ▸ hu)
            exact occCnf_disjoint v u hne 0 N w hwv hwu
          simp only [hwv, ite_true] at h1
          simp only [hno, ite_false] at h2
          have hex : ∃ u ∈ v :: rest, w ∈ (occCnf u 0 N).1 := ⟨v, by simp, hwv⟩
          simp only [hex, ite_true]
          omega
        · simp only [hwv, ite_false] at h1
          have hiff : (∃ u ∈ v :: rest, w ∈ (occCnf u 0 N).1) ↔
              (∃ u ∈ rest, w ∈ (occCnf u 0 N).1) := by
            constructor
            · rintro ⟨u, hu, hwu⟩
              simp only [List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact absurd hwu hwv
              · exact ⟨u, hu, hwu⟩
            · rintro ⟨u, hu, hwu⟩
              exact ⟨u, List.mem_cons_of_mem _ hu, hwu⟩
          simp only [hiff]
          omega
  have h := hgen (List.range (encodeCnf N).length) List.nodup_range
  split_ifs at h <;> omega

theorem to3Occ_countP_le_three (N : cnf) (w : var) :
    (to3Occ N).flatten.countP (fun l => l.2 == w) ≤ 3 := by
  unfold to3Occ
  rw [List.flatten_append, List.countP_append]
  have h1 := rewriteCnf_countP_le_one 0 N w
  have h2 := allCycles_countP_le_two N w
  omega

/-! ### Equisatisfiability: `SAT N ↔ SAT (to3Occ N)` -/

theorem eval_impChain_imp (a : assgn) (prev : Nat) (qs : List Nat)
    (heval : evalCnf a (impChain prev qs) = true) :
    evalVar a prev = true → ∀ q ∈ qs, evalVar a q = true := by
  induction qs generalizing prev with
  | nil => intro _ q hq; simp at hq
  | cons q rest ih =>
      intro hprev x hx
      simp only [impChain, evalCnf, List.all_cons, Bool.and_eq_true] at heval
      have hcl : evalClause a [(false, prev), (true, q)] = true := heval.1
      have hqtrue : evalVar a q = true := by
        simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
          Bool.or_eq_true, decide_eq_true_eq] at hcl
        rcases hcl with h1 | h2
        · rw [hprev] at h1; cases h1
        · exact h2
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact hqtrue
      · exact ih q heval.2 hqtrue x hx'

theorem eval_impChain_last (a : assgn) (prev : Nat) (qs : List Nat) (hne : qs ≠ [])
    (heval : evalCnf a (impChain prev qs) = true) :
    evalVar a prev = true → evalVar a (qs.getLast hne) = true :=
  fun hp => eval_impChain_imp a prev qs heval hp _ (List.getLast_mem hne)

theorem eval_cycleClauses_const (a : assgn) (L : List Nat)
    (heval : evalCnf a (cycleClauses L) = true) :
    ∀ x ∈ L, ∀ y ∈ L, evalVar a x = evalVar a y := by
  cases L with
  | nil => intro x hx; simp at hx
  | cons first rest =>
      cases rest with
      | nil =>
          intro x hx y hy
          simp only [List.mem_singleton] at hx hy
          rw [hx, hy]
      | cons q qs =>
          simp only [cycleClauses, evalCnf_app_iff] at heval
          obtain ⟨hchain, hclose⟩ := heval
          have hclose_cl : evalClause a [(false, (q :: qs).getLast (by simp)), (true, first)] = true := by
            simpa [evalCnf] using hclose
          have hlast_to_first : evalVar a ((q :: qs).getLast (by simp)) = true →
              evalVar a first = true := by
            intro hlast
            simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
              Bool.or_eq_true, decide_eq_true_eq] at hclose_cl
            rcases hclose_cl with h1 | h2
            · rw [hlast] at h1; cases h1
            · exact h2
          have hfirst_to_all : evalVar a first = true → ∀ z ∈ first :: q :: qs, evalVar a z = true := by
            intro hf z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · exact hf
            · exact eval_impChain_imp a first (q :: qs) hchain hf z hz'
          have hall_to_first : ∀ z ∈ first :: q :: qs, evalVar a z = true → evalVar a first = true := by
            intro z hz hzt
            rcases List.mem_cons.mp hz with rfl | hz'
            · exact hzt
            · have hsuffix : ∀ (p : Nat) (ls : List Nat) (hne : ls ≠ []),
                  evalCnf a (impChain p ls) = true →
                  z ∈ p :: ls → evalVar a z = true → evalVar a (ls.getLast hne) = true := by
                intro p ls
                induction ls generalizing p with
                | nil => intro hne; exact absurd rfl hne
                | cons b bs ih =>
                    intro _ hev hzmem hzv
                    rcases List.mem_cons.mp hzmem with rfl | hzmem'
                    · exact eval_impChain_last a z (b :: bs) (by simp) hev hzv
                    · simp only [impChain, evalCnf, List.all_cons, Bool.and_eq_true] at hev
                      cases bs with
                      | nil =>
                          have hzb : z = b := by simpa using hzmem'
                          subst hzb; simpa using hzv
                      | cons b2 bs2 =>
                          rw [List.getLast_cons (by simp)]
                          exact ih b (by simp) hev.2 hzmem' hzv
              exact hlast_to_first (hsuffix first (q :: qs) (by simp) hchain (List.mem_cons_of_mem _ hz') hzt)
          intro x hx y hy
          cases hxval : evalVar a x with
          | true => exact (hfirst_to_all (hall_to_first x hx hxval) y hy).symm
          | false =>
              cases hyval : evalVar a y with
              | false => rfl
              | true =>
                  have := hfirst_to_all (hall_to_first y hy hyval) x hx
                  rw [hxval] at this; cases this

theorem eval_impChain_of_const (a : assgn) (prev : Nat) (qs : List Nat) (b : Bool)
    (hconst : ∀ x ∈ prev :: qs, evalVar a x = b) :
    evalCnf a (impChain prev qs) = true := by
  induction qs generalizing prev with
  | nil => simp [impChain, evalCnf]
  | cons q rest ih =>
      simp only [impChain, evalCnf, List.all_cons, Bool.and_eq_true]
      constructor
      · simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
          Bool.or_eq_true, decide_eq_true_eq]
        rw [hconst prev (by simp), hconst q (by simp)]
        cases b <;> simp
      · exact ih q (fun x hx => hconst x (List.mem_cons_of_mem _ hx))

theorem eval_cycleClauses_of_const (a : assgn) (L : List Nat) (b : Bool)
    (hconst : ∀ x ∈ L, evalVar a x = b) :
    evalCnf a (cycleClauses L) = true := by
  cases L with
  | nil => simp [cycleClauses, evalCnf]
  | cons first rest =>
      cases rest with
      | nil => simp [cycleClauses, evalCnf]
      | cons q qs =>
          simp only [cycleClauses, evalCnf_app_iff]
          constructor
          · exact eval_impChain_of_const a first (q :: qs) b hconst
          · simp only [evalCnf, List.all_cons, List.all_nil, Bool.and_true,
              evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
              Bool.or_eq_true, decide_eq_true_eq]
            rw [hconst _ (List.mem_cons_of_mem _ (List.getLast_mem (by simp))),
              hconst first (by simp)]
            cases b <;> simp

theorem var_lt_encodeClause (C : clause) (l : literal) (hl : l ∈ C) :
    l.2 < (encodeClause C).length := by
  induction C with
  | nil => simp at hl
  | cons a C ih =>
      rcases List.mem_cons.mp hl with rfl | hl'
      · rw [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons]
        simp only [List.length_append, List.length_cons, List.length_nil, encodeLit_len]
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3))
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      · have h := ih hl'
        rw [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons]
        rw [CnfSerialize.encodeClause_eq] at h
        simp only [List.length_append, List.length_cons, List.length_nil, encodeLit_len] at h ⊢
        exact Nat.lt_of_lt_of_le h (by rw [Nat.add_assoc (a.2 + 3)]; exact Nat.le_add_left _ _)

theorem var_lt_encodeCnf (N : cnf) (C : clause) (hC : C ∈ N) (l : literal) (hl : l ∈ C) :
    l.2 < (encodeCnf N).length := by
  induction N with
  | nil => simp at hC
  | cons C0 N ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append]
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact Nat.lt_of_lt_of_le (var_lt_encodeClause C l hl) (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (ih hC') (Nat.le_add_left _ _)

theorem rewriteClause_eval_iff (a a' : assgn) (off : Nat) (C : clause)
    (hagree : ∀ v q, q ∈ (occClause v off C).1 → evalVar a' q = evalVar a v) :
    evalClause a' (rewriteClause off C).1 = evalClause a C := by
  induction C generalizing off with
  | nil => rfl
  | cons l C ih =>
      rcases l with ⟨pol, v⟩
      simp only [rewriteClause, evalClause, List.any_cons]
      have hq : off + v + 2 ∈ (occClause v off ((pol, v) :: C)).1 := by
        simp [occClause]
      have hv := hagree v (off + v + 2) hq
      have hlit : evalLiteral a' (pol, off + v + 2) = evalLiteral a (pol, v) := by
        simp [evalLiteral, hv]
      rw [hlit]
      congr 1
      apply ih (off + v + 2 + 1)
      intro u q hqu
      apply hagree u q
      simp only [occClause]
      split_ifs
      · exact List.mem_cons_of_mem _ hqu
      · exact hqu

theorem rewriteCnf_eval_iff (a a' : assgn) (off : Nat) (N : cnf)
    (hagree : ∀ v q, q ∈ (occCnf v off N).1 → evalVar a' q = evalVar a v) :
    evalCnf a' (rewriteCnf off N).1 = evalCnf a N := by
  induction N generalizing off with
  | nil => rfl
  | cons C N ih =>
      simp only [rewriteCnf, evalCnf, List.all_cons]
      have h1 : evalClause a' (rewriteClause off C).1 = evalClause a C := by
        apply rewriteClause_eval_iff a a' off C
        intro v q hq
        exact hagree v q (by simp [occCnf, hq])
      have h2 : evalCnf a' (rewriteCnf (rewriteClause off C).2 N).1 = evalCnf a N := by
        apply ih (rewriteClause off C).2
        intro v q hq
        apply hagree v q
        simp only [occCnf, List.mem_append]
        right
        have hsnd : (occClause v off C).2 = (rewriteClause off C).2 := by
          rw [occClause_snd, rewriteClause_snd]
        rw [hsnd]
        exact hq
      rw [h1]
      exact congrArg (evalClause a C && ·) h2

theorem to3Occ_sat_iff (N : cnf) : SAT N ↔ SAT (to3Occ N) := by
  have hmem_var : ∀ (v q off : Nat) (M : cnf), q ∈ (occCnf v off M).1 →
      ∃ C ∈ M, ∃ pol, (pol, v) ∈ C := by
    intro v q off M
    induction M generalizing off with
    | nil => intro h; simp [occCnf] at h
    | cons C M ih =>
        intro h
        simp only [occCnf, List.mem_append] at h
        rcases h with h1 | h2
        · refine ⟨C, by simp, ?_⟩
          clear ih
          induction C generalizing off with
          | nil => simp [occClause] at h1
          | cons l C ihC =>
              rcases l with ⟨pol, u⟩
              simp only [occClause] at h1
              by_cases huv : u = v
              · subst huv; exact ⟨pol, by simp⟩
              · have hne : (u == v) = false := beq_false_of_ne huv
                simp only [hne, Bool.false_eq_true, ite_false] at h1
                obtain ⟨p', hp'⟩ := ihC (off + u + 2 + 1) h1
                exact ⟨p', List.mem_cons_of_mem _ hp'⟩
        · obtain ⟨C', hC', pol, hpol⟩ := ih (occClause v off C).2 h2
          exact ⟨C', List.mem_cons_of_mem _ hC', pol, hpol⟩
  constructor
  · rintro ⟨a, ha⟩
    let a' : assgn := (List.range (encodeCnf N).length).flatMap
      (fun v => if evalVar a v then (occCnf v 0 N).1 else [])
    have ha'_iff : ∀ v q, q ∈ (occCnf v 0 N).1 → evalVar a' q = evalVar a v := by
      intro v q hq
      obtain ⟨C, hC, pol, hpol⟩ := hmem_var v q 0 N hq
      have hvlt : v < (encodeCnf N).length := var_lt_encodeCnf N C hC (pol, v) hpol
      cases hav : evalVar a v with
      | true =>
          change decide (q ∈ a') = true
          apply decide_eq_true
          simp only [a', List.mem_flatMap, List.mem_range]
          exact ⟨v, hvlt, by simpa [hav] using hq⟩
      | false =>
          change decide (q ∈ a') = false
          apply decide_eq_false
          simp only [a', List.mem_flatMap, List.mem_range, not_exists, not_and]
          intro u _ hqu
          split_ifs at hqu with hau
          · have hne : v ≠ u := fun heq => by subst heq; rw [hav] at hau; cases hau
            exact occCnf_disjoint v u hne 0 N q hq hqu
          · simp at hqu
    refine ⟨a', ?_⟩
    show evalCnf a' ((rewriteCnf 0 N).1 ++ allCycles N) = true
    rw [evalCnf_app_iff]
    constructor
    · rw [rewriteCnf_eval_iff a a' 0 N ha'_iff]; exact ha
    · rw [evalCnf_clause_iff]
      intro C hC
      simp only [allCycles, List.mem_flatMap, List.mem_range] at hC
      obtain ⟨v, _, hCv⟩ := hC
      have hcyc := eval_cycleClauses_of_const a' (occCnf v 0 N).1 (evalVar a v)
        (fun q hq => ha'_iff v q hq)
      exact (evalCnf_clause_iff a' _).mp hcyc C hCv
  · rintro ⟨a', ha'⟩
    have hsplit := (evalCnf_app_iff a' (rewriteCnf 0 N).1 (allCycles N)).mp ha'
    let a : assgn := (List.range (encodeCnf N).length).filter
      (fun v => match (occCnf v 0 N).1 with | [] => false | q :: _ => evalVar a' q)
    refine ⟨a, ?_⟩
    show evalCnf a N = true
    rw [← rewriteCnf_eval_iff a a' 0 N]
    · exact hsplit.1
    · intro v q hq
      obtain ⟨C, hC, pol, hpol⟩ := hmem_var v q 0 N hq
      have hvlt : v < (encodeCnf N).length := var_lt_encodeCnf N C hC (pol, v) hpol
      have hcyc : evalCnf a' (cycleClauses (occCnf v 0 N).1) = true := by
        rw [evalCnf_clause_iff]
        intro C hC
        apply (evalCnf_clause_iff a' (allCycles N)).mp hsplit.2
        simp only [allCycles, List.mem_flatMap, List.mem_range]
        exact ⟨v, hvlt, hC⟩
      have hconst := eval_cycleClauses_const a' (occCnf v 0 N).1 hcyc
      cases hocc : (occCnf v 0 N).1 with
      | nil => rw [hocc] at hq; simp at hq
      | cons q0 qs =>
          have heq : evalVar a' q = evalVar a' q0 :=
            hconst q hq q0 (by rw [hocc]; simp)
          rw [heq]
          symm
          change decide (v ∈ a) = evalVar a' q0
          simp [a, List.mem_filter, List.mem_range, hvlt, hocc]

/-! ### The `CookLevin.Lang.Cmd` program computing `encodeCnf (to3Occ (cnfOf x))` -/

def pass1Body : Cmd :=
  Cmd.op (.head HD CUR) ;;
  Cmd.op (.tail CUR CUR) ;;
  Cmd.ifBit IN_LIT
    (Cmd.ifBit GOT_POL
      (Cmd.ifBit HD
        (Cmd.op (.clear HD))
        (Cmd.op (.clear IN_LIT) ;;
         Cmd.op (.appendOne OUT) ;;
         Cmd.ifBit POL (Cmd.op (.appendOne OUT)) (Cmd.op (.appendZero OUT)) ;;
         Cmd.op (.concat OUT OUT POS) ;;
         Cmd.op (.appendZero OUT)))
      (Cmd.op (.copy POL HD) ;;
       Cmd.op (.clear GOT_POL) ;; Cmd.op (.appendOne GOT_POL)))
    (Cmd.ifBit HD
      (Cmd.op (.clear IN_LIT) ;; Cmd.op (.appendOne IN_LIT) ;; Cmd.op (.clear GOT_POL))
      (Cmd.op (.appendZero OUT)))

def pass1 : Cmd :=
  Cmd.op (.copy CUR INP) ;;
  Cmd.op (.clear IN_LIT) ;;
  Cmd.op (.clear GOT_POL) ;;
  Cmd.op (.clear POL) ;;
  Cmd.forBnd POS INP pass1Body

def emitBinClause (r1 r2 : Var) : Cmd :=
  Cmd.op (.appendOne OUT) ;;
  Cmd.op (.appendZero OUT) ;;
  Cmd.op (.concat OUT OUT r1) ;;
  Cmd.op (.appendZero OUT) ;;
  Cmd.op (.appendOne OUT) ;;
  Cmd.op (.appendOne OUT) ;;
  Cmd.op (.concat OUT OUT r2) ;;
  Cmd.op (.appendZero OUT) ;;
  Cmd.op (.appendZero OUT)

def pass2InnerBody : Cmd :=
  Cmd.op (.head HD CUR) ;;
  Cmd.op (.tail CUR CUR) ;;
  Cmd.ifBit IN_LIT
    (Cmd.ifBit GOT_POL
      (Cmd.ifBit HD
        (Cmd.op (.appendOne CUR_VAR))
        (Cmd.op (.clear IN_LIT) ;;
         Cmd.op (.eqBit EQ CUR_VAR VREG) ;;
         Cmd.ifBit EQ
           (Cmd.ifBit HAS_FIRST
             (Cmd.op (.clear MULTI) ;; Cmd.op (.appendOne MULTI) ;;
              emitBinClause PREV_ID POS ;;
              Cmd.op (.copy PREV_ID POS))
             (Cmd.op (.clear HAS_FIRST) ;; Cmd.op (.appendOne HAS_FIRST) ;;
              Cmd.op (.copy FIRST_ID POS) ;;
              Cmd.op (.copy PREV_ID POS)))
           (Cmd.op (.clear EQ))))
      (Cmd.op (.clear GOT_POL) ;; Cmd.op (.appendOne GOT_POL)))
    (Cmd.ifBit HD
      (Cmd.op (.clear IN_LIT) ;; Cmd.op (.appendOne IN_LIT) ;;
       Cmd.op (.clear GOT_POL) ;; Cmd.op (.clear CUR_VAR))
      (Cmd.op (.clear HD)))

def pass2OuterBody : Cmd :=
  Cmd.op (.copy CUR INP) ;;
  Cmd.op (.clear IN_LIT) ;;
  Cmd.op (.clear GOT_POL) ;;
  Cmd.op (.clear CUR_VAR) ;;
  Cmd.op (.clear HAS_FIRST) ;;
  Cmd.op (.clear MULTI) ;;
  Cmd.op (.clear FIRST_ID) ;;
  Cmd.op (.clear PREV_ID) ;;
  Cmd.forBnd POS INP pass2InnerBody ;;
  Cmd.ifBit MULTI (emitBinClause PREV_ID FIRST_ID) (Cmd.op (.clear MULTI))

def pass2 : Cmd :=
  Cmd.forBnd VREG INP pass2OuterBody

def redCmd : Cmd :=
  SATStr.satStrBuild ;; pass1 ;; pass2

def regMask : Nat := 2 ^ 25 - 1

theorem redCmd_chk : (redCmd.chk regMask).1 = true := by decide

theorem redCmd_usesBelow : Cmd.UsesBelow redCmd 25 := by
  have h1 : Cmd.UsesBelow SATStr.satStrBuild 25 := by
    simp [SATStr.satStrBuild, SATStr.satStrPre, SATStr.satStrPostA, SATStr.satStrPostB,
      SATStr.badBranch, SATStr.scanBody, Cmd.UsesBelow, Op.UsesBelow,
      SATStr.WCUR, SATStr.WIDX, SATStr.WHD, SATStr.WSA, SATStr.WSB, SATStr.WTAL,
      EvalCnfCmd.OUTPUT, EvalCnfCmd.CLAUSE_TALLY, EvalCnfCmd.CNF_STREAM, EvalCnfCmd.ASSGN]
  have h2 : Cmd.UsesBelow pass1 25 := by
    simp only [pass1, pass1Body, Cmd.UsesBelow, Op.UsesBelow]; decide
  have h3 : Cmd.UsesBelow pass2 25 := by
    simp only [pass2, pass2OuterBody, pass2InnerBody, emitBinClause, Cmd.UsesBelow, Op.UsesBelow]
    repeat (first | apply And.intro | decide)
  exact ⟨h1, h2, h3⟩

/-! ### Helper for evaluating `forBnd` over slices -/

def runLoop (cnt : Var) (body : Cmd) (s : State) (start len : Nat) : State :=
  (List.range len).foldl (fun st k => body.eval (st.set cnt (List.replicate (start + k) 1))) s

theorem runLoop_succ_right (cnt : Var) (body : Cmd) (s : State) (start k : Nat) :
    runLoop cnt body s start (k + 1) =
      body.eval ((runLoop cnt body s start k).set cnt (List.replicate (start + k) 1)) := by
  unfold runLoop
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem forBnd_eval_eq (cnt bnd : Var) (body : Cmd) (s : State) :
    (Cmd.forBnd cnt bnd body).eval s = runLoop cnt body s 0 (s.get bnd).length := by
  unfold Cmd.eval Cmd.run runLoop
  have hgen : ∀ (l : List Nat) (st : State) (c : Nat),
      (l.foldl (fun acc i =>
        let s' := acc.1.set cnt (List.replicate i 1)
        let r := Cmd.run body s'
        (r.1, acc.2 + r.2)) (st, c)).1 =
      l.foldl (fun st i => body.eval (st.set cnt (List.replicate i 1))) st := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons i is ih =>
        intro st c
        simp only [List.foldl_cons]
        exact ih _ _
  have h := hgen (List.range (s.get bnd).length) s 0
  simpa [Cmd.eval] using h

theorem runLoop_zero (cnt : Var) (body : Cmd) (s : State) (start : Nat) :
    runLoop cnt body s start 0 = s := rfl

theorem runLoop_succ (cnt : Var) (body : Cmd) (s : State) (start n : Nat) :
    runLoop cnt body s start (n + 1) =
      runLoop cnt body (body.eval (s.set cnt (List.replicate start 1))) (start + 1) n := by
  unfold runLoop
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [Nat.add_zero]
  congr 1; funext st k
  have : start + (k + 1) = start + 1 + k := by omega
  rw [this]

theorem runLoop_add (cnt : Var) (body : Cmd) (s : State) (start a b : Nat) :
    runLoop cnt body s start (a + b) =
      runLoop cnt body (runLoop cnt body s start a) (start + a) b := by
  induction a generalizing s start with
  | zero => simp [runLoop_zero]
  | succ a ih =>
      have : a + 1 + b = (a + b) + 1 := by omega
      rw [this, runLoop_succ, runLoop_succ, ih]
      have h2 : start + 1 + a = start + (a + 1) := by omega
      rw [h2]

/-! ### Pass 1 functional correctness -/

def p1Inv (s : State) (cur : List Nat) (out : List Nat) (inLit gotPol : Bool) (pol : List Nat) : Prop :=
  s.get CUR = cur ∧
  s.get OUT = out ∧
  s.get IN_LIT = (if inLit then [1] else []) ∧
  s.get GOT_POL = (if gotPol then [1] else []) ∧
  s.get POL = pol

theorem pass1Body_step (s : State) (hd : Nat) (rest out pol : List Nat)
    (inLit gotPol : Bool) (pos : Nat) (hhd : hd ≤ 1)
    (hinv : p1Inv s (hd :: rest) out inLit gotPol pol) :
    let s1 := pass1Body.eval (s.set POS (List.replicate pos 1))
    if inLit then
      if gotPol then
        if hd = 1 then p1Inv s1 rest out true true pol
        else p1Inv s1 rest (out ++ [1, if pol = [1] then 1 else 0] ++ List.replicate pos 1 ++ [0])
          false true pol
      else p1Inv s1 rest out true true [hd]
    else
      if hd = 1 then p1Inv s1 rest out true false pol
      else p1Inv s1 rest (out ++ [0]) false gotPol pol := by
  obtain ⟨hCUR, hOUT, hIL, hGP, hPOL⟩ := hinv
  have hget : ∀ r, r ≠ POS → (s.set POS (List.replicate pos 1)).get r = s.get r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  cases inLit with
  | false =>
      rcases (show hd = 0 ∨ hd = 1 by omega) with rfl | rfl
      · simp only [Bool.false_eq_true, ite_false, show (0 : Nat) ≠ 1 by decide]
        simp only [pass1Body, Cmd.eval_seq, Cmd.eval_op, Op.eval, p1Inv]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
        simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR, hOUT, hIL, hGP, hPOL]
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        simp only [pass1Body, Cmd.eval_seq, Cmd.eval_op, Op.eval, p1Inv]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
        simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
          hget, hCUR, hOUT, hIL, hGP, hPOL]
  | true =>
      cases gotPol with
      | false =>
          simp only [Bool.false_eq_true, ite_true, ite_false]
          simp only [pass1Body, Cmd.eval_seq, Cmd.eval_op, Op.eval, p1Inv]
          rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
          rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hGP])]
          simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
            hget, hCUR, hOUT, hIL, hGP, hPOL]
      | true =>
          rcases (show hd = 0 ∨ hd = 1 by omega) with rfl | rfl
          · simp only [ite_true, show (0 : Nat) ≠ 1 by decide, ite_false]
            simp only [pass1Body, Cmd.eval_seq, Cmd.eval_op, Op.eval, p1Inv]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hGP])]
            rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
            by_cases hpol1 : pol = [1]
            · simp only [hpol1, ite_true, Cmd.eval_seq, Cmd.eval_op, Op.eval]
              rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hPOL, hpol1])]
              simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
                hget, hCUR, hOUT, hIL, hGP, hPOL, hpol1, List.append_assoc]
            · simp only [hpol1, ite_false, Cmd.eval_seq, Cmd.eval_op, Op.eval]
              rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hPOL, hpol1])]
              simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
                hget, hCUR, hOUT, hIL, hGP, hPOL, List.append_assoc]
          · simp only [ite_true]
            simp only [pass1Body, Cmd.eval_seq, Cmd.eval_op, Op.eval, p1Inv]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hGP])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
            simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
              hget, hCUR, hOUT, hIL, hGP, hPOL]

theorem pass1_rep_ones (v : Nat) (rest out pol : List Nat) (start : Nat) (s : State)
    (hinv : p1Inv s (List.replicate v 1 ++ rest) out true true pol) :
    p1Inv (runLoop POS pass1Body s start v) rest out true true pol := by
  induction v generalizing start s with
  | zero => simpa [runLoop_zero] using hinv
  | succ v ih =>
      rw [runLoop_succ]
      have h1 := pass1Body_step s 1 (List.replicate v 1 ++ rest) out pol true true start (by decide)
        (by simpa [List.replicate_succ] using hinv)
      simp only [ite_true] at h1
      exact ih (start + 1) _ h1

theorem pass1_encodeLit (l : literal) (rest out pol : List Nat) (off : Nat) (gotPol : Bool) (s : State)
    (hinv : p1Inv s (encodeLit l ++ rest) out false gotPol pol) :
    ∃ pol', p1Inv (runLoop POS pass1Body s off (encodeLit l).length)
      rest (out ++ encodeLit (l.1, off + l.2 + 2)) false true pol' := by
  rcases l with ⟨b, v⟩
  rw [encodeLit_len]
  have henc : encodeLit (b, v) ++ rest = 1 :: (if b then 1 else 0) :: (List.replicate v 1 ++ (0 :: rest)) := by
    simp [EvalCnfCmd.encodeLit, List.append_assoc]
  rw [henc] at hinv
  have hlen : v + 3 = 1 + (1 + (v + 1)) := by
    rw [Nat.add_comm 1 (v + 1), Nat.add_assoc, Nat.add_comm 1 (v + 2), Nat.add_assoc]
  rw [hlen, runLoop_add, runLoop_add, runLoop_add]
  rw [runLoop_succ, runLoop_zero]
  have h1 := pass1Body_step s 1 _ out pol false gotPol off (by decide) hinv
  simp only [Bool.false_eq_true, ite_false, ite_true] at h1
  rw [runLoop_succ, runLoop_zero]
  have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
  have h2 := pass1Body_step _ (if b then 1 else 0) _ out pol true false (off + 1) hb h1
  simp only [Bool.false_eq_true, ite_true, ite_false] at h2
  have h3 := pass1_rep_ones v (0 :: rest) out [if b then 1 else 0] (off + 1 + 1) _ h2
  rw [runLoop_succ, runLoop_zero]
  have h4 := pass1Body_step _ 0 rest out [if b then 1 else 0] true true (off + 1 + 1 + v) (by decide) h3
  simp only [ite_true, show (0 : Nat) ≠ 1 by decide, ite_false] at h4
  refine ⟨[if b then 1 else 0], ?_⟩
  have hpos : off + 1 + 1 + v = off + v + 2 := by omega
  have hpol_eq : (if [if b then 1 else 0] = [1] then 1 else 0) = if b then 1 else 0 := by
    cases b <;> decide
  rw [hpos] at h4 ⊢
  rw [hpol_eq] at h4
  simpa [EvalCnfCmd.encodeLit, List.append_assoc] using h4

theorem pass1_clauseBody (C : clause) (rest out pol : List Nat) (off : Nat) (gotPol : Bool) (s : State)
    (hinv : p1Inv s (CnfSerialize.clauseBody C ++ rest) out false gotPol pol) :
    ∃ pol' gp', p1Inv (runLoop POS pass1Body s off (CnfSerialize.clauseBody C).length)
      rest (out ++ CnfSerialize.clauseBody (rewriteClause off C).1) false gp' pol' := by
  induction C generalizing rest out pol off gotPol s with
  | nil => exact ⟨pol, gotPol, by simpa [CnfSerialize.clauseBody, rewriteClause, runLoop_zero] using hinv⟩
  | cons l C ih =>
      rcases l with ⟨b, v⟩
      rw [CnfSerialize.clauseBody_cons, List.length_append, runLoop_add]
      rw [CnfSerialize.clauseBody_cons, List.append_assoc] at hinv
      obtain ⟨pol1, h1⟩ := pass1_encodeLit (b, v) (CnfSerialize.clauseBody C ++ rest) out pol off gotPol s hinv
      rw [encodeLit_len] at h1 ⊢
      have hpos : off + (v + 3) = off + v + 2 + 1 := by omega
      rw [hpos]
      obtain ⟨pol2, gp2, h2⟩ := ih rest (out ++ encodeLit (b, off + v + 2)) pol1 (off + v + 2 + 1) true _ h1
      refine ⟨pol2, gp2, ?_⟩
      simpa [rewriteClause, CnfSerialize.clauseBody_cons, List.append_assoc] using h2

theorem pass1_encodeClause (C : clause) (rest out pol : List Nat) (off : Nat) (gotPol : Bool) (s : State)
    (hinv : p1Inv s (encodeClause C ++ rest) out false gotPol pol) :
    ∃ pol' gp', p1Inv (runLoop POS pass1Body s off (encodeClause C).length)
      rest (out ++ encodeClause (rewriteClause off C).1) false gp' pol' := by
  rw [CnfSerialize.encodeClause_eq, List.length_append, runLoop_add]
  rw [CnfSerialize.encodeClause_eq, List.append_assoc] at hinv
  obtain ⟨pol1, gp1, h1⟩ := pass1_clauseBody C (0 :: rest) out pol off gotPol s hinv
  rw [show ([0] : List Nat).length = 1 from rfl, runLoop_succ, runLoop_zero]
  have h2 := pass1Body_step _ 0 rest _ pol1 false gp1 (off + (CnfSerialize.clauseBody C).length) (by decide) h1
  simp only [Bool.false_eq_true, ite_false, show (0 : Nat) ≠ 1 by decide] at h2
  refine ⟨pol1, gp1, ?_⟩
  simpa [CnfSerialize.encodeClause_eq, List.append_assoc] using h2

theorem pass1_encodeCnf (N : cnf) (rest out pol : List Nat) (off : Nat) (gotPol : Bool) (s : State)
    (hinv : p1Inv s (encodeCnf N ++ rest) out false gotPol pol) :
    ∃ pol' gp', p1Inv (runLoop POS pass1Body s off (encodeCnf N).length)
      rest (out ++ encodeCnf (rewriteCnf off N).1) false gp' pol' := by
  induction N generalizing rest out pol off gotPol s with
  | nil => exact ⟨pol, gotPol, by simpa [EvalCnfCmd.encodeCnf, rewriteCnf, runLoop_zero] using hinv⟩
  | cons C N ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append, runLoop_add]
      rw [CnfSerialize.encodeCnf_cons, List.append_assoc] at hinv
      obtain ⟨pol1, gp1, h1⟩ := pass1_encodeClause C (encodeCnf N ++ rest) out pol off gotPol s hinv
      have hoff : off + (encodeClause C).length = (rewriteClause off C).2 := (rewriteClause_snd off C).symm
      rw [hoff]
      obtain ⟨pol2, gp2, h2⟩ := ih rest (out ++ encodeClause (rewriteClause off C).1) pol1 (rewriteClause off C).2 gp1 _ h1
      refine ⟨pol2, gp2, ?_⟩
      simpa [rewriteCnf, CnfSerialize.encodeCnf_cons, List.append_assoc] using h2

theorem pass1_eval_out (s : State) (N : cnf) (hINP : s.get INP = encodeCnf N) (hOUT : s.get OUT = []) :
    (pass1.eval s).get OUT = encodeCnf (rewriteCnf 0 N).1 ∧
    (pass1.eval s).get INP = encodeCnf N := by
  have hnw : INP ∉ pass1.writes := by decide
  have hINP' : (pass1.eval s).get INP = encodeCnf N := by
    rw [Cmd.eval_get_of_not_writes _ _ _ hnw, hINP]
  refine ⟨?_, hINP'⟩
  unfold pass1
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, forBnd_eval_eq]
  set s0 := (Cmd.op (.clear POL)).eval ((Cmd.op (.clear GOT_POL)).eval
    ((Cmd.op (.clear IN_LIT)).eval ((Cmd.op (.copy CUR INP)).eval s)))
  have hs0_inp : s0.get INP = encodeCnf N := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne, hINP, INP, CUR, IN_LIT, GOT_POL, POL]
  have hs0_inv : p1Inv s0 (encodeCnf N ++ []) [] false false [] := by
    simp [p1Inv, s0, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
      hINP, hOUT, OUT, INP, CUR, IN_LIT, GOT_POL, POL]
  rw [hs0_inp]
  obtain ⟨_, _, hfinal⟩ := pass1_encodeCnf N [] [] [] 0 false s0 hs0_inv
  simpa using hfinal.2.1

/-! ### Pass 2 functional correctness -/

theorem emitBinClause_eval (r1 r2 : Var) (s : State)
    (hr1 : r1 ≠ OUT) (hr2 : r2 ≠ OUT) (v1 v2 : Nat)
    (h1 : s.get r1 = List.replicate v1 1) (h2 : s.get r2 = List.replicate v2 1) :
    (emitBinClause r1 r2).eval s =
      s.set OUT (s.get OUT ++ encodeClause [(false, v1), (true, v2)]) := by
  unfold emitBinClause
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
    State.get_set_ne _ OUT _ r1 hr1, State.get_set_ne _ OUT _ r2 hr2, h1, h2]
  congr 1
  simp [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons, CnfSerialize.clauseBody,
    EvalCnfCmd.encodeLit, List.append_assoc]

def p2Inv (s : State) (v : Nat) (cur out : List Nat)
    (inLit gotPol : Bool) (curVar : List Nat) (acc : List Nat) : Prop :=
  s.get VREG = List.replicate v 1 ∧
  s.get CUR = cur ∧
  s.get OUT = out ∧
  s.get IN_LIT = (if inLit then [1] else []) ∧
  s.get GOT_POL = (if gotPol then [1] else []) ∧
  s.get CUR_VAR = curVar ∧
  match acc with
  | [] =>
      s.get HAS_FIRST = [] ∧ s.get MULTI = []
  | [first] =>
      s.get HAS_FIRST = [1] ∧ s.get MULTI = [] ∧
      s.get FIRST_ID = List.replicate first 1 ∧
      s.get PREV_ID = List.replicate first 1
  | first :: q :: qs =>
      s.get HAS_FIRST = [1] ∧ s.get MULTI = [1] ∧
      s.get FIRST_ID = List.replicate first 1 ∧
      s.get PREV_ID = List.replicate ((q :: qs).getLast (by simp)) 1

def chainOf : List Nat → cnf
  | [] => []
  | first :: qs => impChain first qs

theorem chainOf_append_one (acc : List Nat) (q : Nat) :
    chainOf (acc ++ [q]) =
      match acc with
      | [] => []
      | [first] => [[(false, first), (true, q)]]
      | first :: q1 :: qs =>
          chainOf (first :: q1 :: qs) ++ [[(false, (q1 :: qs).getLast (by simp)), (true, q)]] := by
  have himp : ∀ (p : Nat) (l : List Nat),
      impChain p (l ++ [q]) = impChain p l ++
        match l with
        | [] => [[(false, p), (true, q)]]
        | a :: as => [[(false, (a :: as).getLast (by simp)), (true, q)]] := by
    intro p l
    induction l generalizing p with
    | nil => rfl
    | cons a as ih =>
        cases as with
        | nil => simp [impChain]
        | cons b bs =>
            rw [List.cons_append, impChain, ih a]
            simp [impChain, List.getLast_cons]
  cases acc with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => simp [chainOf, impChain]
      | cons q1 qs =>
          simp only [List.cons_append, chainOf]
          exact himp first (q1 :: qs)

theorem pass2InnerBody_step (s : State) (v pos : Nat) (hd : Nat) (rest out curVar acc : List Nat)
    (inLit gotPol : Bool) (hhd : hd ≤ 1)
    (hinv : p2Inv s v (hd :: rest) out inLit gotPol curVar acc) :
    let s1 := pass2InnerBody.eval (s.set POS (List.replicate pos 1))
    if inLit then
      if gotPol then
        if hd = 1 then p2Inv s1 v rest out true true (curVar ++ [1]) acc
        else if curVar = List.replicate v 1 then
          p2Inv s1 v rest
            (out ++ match acc with
              | [] => []
              | [first] => encodeClause [(false, first), (true, pos)]
              | _ :: q1 :: qs => encodeClause [(false, (q1 :: qs).getLast (by simp)), (true, pos)])
            false true curVar (acc ++ [pos])
        else
          p2Inv s1 v rest out false true curVar acc
      else p2Inv s1 v rest out true true curVar acc
    else
      if hd = 1 then p2Inv s1 v rest out true false [] acc
      else p2Inv s1 v rest out false gotPol curVar acc := by
  obtain ⟨hV, hCUR, hOUT, hIL, hGP, hCV, hACC⟩ := hinv
  have hget : ∀ r, r ≠ POS → (s.set POS (List.replicate pos 1)).get r = s.get r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  cases inLit with
  | false =>
      rcases (show hd = 0 ∨ hd = 1 by omega) with rfl | rfl
      · simp only [Bool.false_eq_true, ite_false, show (0 : Nat) ≠ 1 by decide]
        simp only [pass2InnerBody, Cmd.eval_seq, Cmd.eval_op, Op.eval]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
        · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
        · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
        · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hIL]
        · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
        · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV]
        · rcases acc with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;>
            simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC]
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        simp only [pass2InnerBody, Cmd.eval_seq, Cmd.eval_op, Op.eval]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
        · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
        · rcases acc with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;>
            simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC]
  | true =>
      cases gotPol with
      | false =>
          simp only [Bool.false_eq_true, ite_true, ite_false]
          simp only [pass2InnerBody, Cmd.eval_seq, Cmd.eval_op, Op.eval]
          rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
          rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [State.get_set_ne, hget, hGP])]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hIL]
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
          · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV]
          · rcases acc with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;>
              simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC]
      | true =>
          rcases (show hd = 0 ∨ hd = 1 by omega) with rfl | rfl
          · simp only [ite_true, show (0 : Nat) ≠ 1 by decide, ite_false]
            simp only [pass2InnerBody, Cmd.eval_seq, Cmd.eval_op]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [Op.eval, State.get_set_ne, hget, hIL])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [Op.eval, State.get_set_ne, hget, hGP])]
            rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [Op.eval, State.get_set_ne, State.get_set_eq, hget, hCUR])]
            simp only [Cmd.eval_seq, Cmd.eval_op]
            by_cases heq : curVar = List.replicate v 1
            · simp only [heq, ite_true]
              have hEQ_true :
                  ((Op.eval (Op.eqBit EQ CUR_VAR VREG)
                    (Op.eval (Op.clear IN_LIT)
                      (Op.eval (Op.tail CUR CUR)
                        (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1))))))).get EQ = [1] := by
                simp [Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR, hCV, hV, heq]
              rw [Cmd.eval_ifBit_true _ _ _ _ hEQ_true]
              cases acc with
              | nil =>
                  have hHF :
                      ((Op.eval (Op.eqBit EQ CUR_VAR VREG)
                        (Op.eval (Op.clear IN_LIT)
                          (Op.eval (Op.tail CUR CUR)
                            (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1))))))).get HAS_FIRST ≠ [1] := by
                    simp [Op.eval, State.get_set_ne, hget, hACC.1]
                  rw [Cmd.eval_ifBit_false _ _ _ _ hHF]
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV, heq]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.2]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                  · simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
              | cons first restAcc =>
                  cases restAcc with
                  | nil =>
                      have hHF :
                          ((Op.eval (Op.eqBit EQ CUR_VAR VREG)
                            (Op.eval (Op.clear IN_LIT)
                              (Op.eval (Op.tail CUR CUR)
                                (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1))))))).get HAS_FIRST = [1] := by
                        simp [Op.eval, State.get_set_ne, hget, hACC.1]
                      rw [Cmd.eval_ifBit_true _ _ _ _ hHF]
                      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
                      have hPREV_pre :
                          ((Cmd.op (Op.appendOne MULTI)).eval
                            ((Cmd.op (Op.clear MULTI)).eval
                              (Op.eval (Op.eqBit EQ CUR_VAR VREG)
                                (Op.eval (Op.clear IN_LIT)
                                  (Op.eval (Op.tail CUR CUR)
                                    (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1)))))))).get PREV_ID =
                            List.replicate first 1 := by
                        simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.2.2.2]
                      have hPOS_pre :
                          ((Cmd.op (Op.appendOne MULTI)).eval
                            ((Cmd.op (Op.clear MULTI)).eval
                              (Op.eval (Op.eqBit EQ CUR_VAR VREG)
                                (Op.eval (Op.clear IN_LIT)
                                  (Op.eval (Op.tail CUR CUR)
                                    (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1)))))))).get POS =
                            List.replicate pos 1 := by
                        simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      rw [emitBinClause_eval PREV_ID POS _ (by decide) (by decide) first pos hPREV_pre hPOS_pre]
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hOUT]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV, heq]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.1]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.2.2.1]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                  | cons q1 qs =>
                      have hHF :
                          ((Op.eval (Op.eqBit EQ CUR_VAR VREG)
                            (Op.eval (Op.clear IN_LIT)
                              (Op.eval (Op.tail CUR CUR)
                                (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1))))))).get HAS_FIRST = [1] := by
                        simp [Op.eval, State.get_set_ne, hget, hACC.1]
                      rw [Cmd.eval_ifBit_true _ _ _ _ hHF]
                      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
                      have hPREV_pre :
                          ((Cmd.op (Op.appendOne MULTI)).eval
                            ((Cmd.op (Op.clear MULTI)).eval
                              (Op.eval (Op.eqBit EQ CUR_VAR VREG)
                                (Op.eval (Op.clear IN_LIT)
                                  (Op.eval (Op.tail CUR CUR)
                                    (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1)))))))).get PREV_ID =
                            List.replicate ((q1 :: qs).getLast (by simp)) 1 := by
                        simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.2.2.2]
                      have hPOS_pre :
                          ((Cmd.op (Op.appendOne MULTI)).eval
                            ((Cmd.op (Op.clear MULTI)).eval
                              (Op.eval (Op.eqBit EQ CUR_VAR VREG)
                                (Op.eval (Op.clear IN_LIT)
                                  (Op.eval (Op.tail CUR CUR)
                                    (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1)))))))).get POS =
                            List.replicate pos 1 := by
                        simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      rw [emitBinClause_eval PREV_ID POS _ (by decide) (by decide)
                        ((q1 :: qs).getLast (by simp)) pos hPREV_pre hPOS_pre]
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hOUT]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV, heq]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.1]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
                      · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC.2.2.1]
                      · have hlast : ∀ h : q1 :: qs.append [pos] ≠ [],
                            (q1 :: qs.append [pos]).getLast h = pos := fun _ =>
                          List.getLast_append_singleton (l := q1 :: qs) (a := pos)
                        rw [hlast]
                        simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
            · simp only [heq, ite_false]
              have hEQ_false :
                  ((Op.eval (Op.eqBit EQ CUR_VAR VREG)
                    (Op.eval (Op.clear IN_LIT)
                      (Op.eval (Op.tail CUR CUR)
                        (Op.eval (Op.head HD CUR) (s.set POS (List.replicate pos 1))))))).get EQ ≠ [1] := by
                simp [Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR, hCV, hV, heq]
              rw [Cmd.eval_ifBit_false _ _ _ _ hEQ_false]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
              · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
              · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
              · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
              · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
              · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hCV]
              · rcases acc with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;>
                  simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC]
          · simp only [ite_true]
            simp only [pass2InnerBody, Cmd.eval_seq, Cmd.eval_op, Op.eval]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hIL])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, hget, hGP])]
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [State.get_set_ne, State.get_set_eq, hget, hCUR])]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hV]
            · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCUR]
            · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hOUT]
            · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hIL]
            · simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hGP]
            · simp [Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne, hget, hCV]
            · rcases acc with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;>
                simp [Cmd.eval_op, Op.eval, State.get_set_ne, hget, hACC]

theorem pass2_rep_ones (u v : Nat) (rest out curVar acc : List Nat) (start : Nat) (s : State)
    (hinv : p2Inv s v (List.replicate u 1 ++ rest) out true true curVar acc) :
    p2Inv (runLoop POS pass2InnerBody s start u) v rest out true true (curVar ++ List.replicate u 1) acc := by
  induction u generalizing curVar start s with
  | zero => simpa [runLoop_zero] using hinv
  | succ u ih =>
      rw [runLoop_succ]
      have h1 := pass2InnerBody_step s v start 1 (List.replicate u 1 ++ rest) out curVar acc true true (by decide)
        (by simpa [List.replicate_succ] using hinv)
      simp only [ite_true] at h1
      have h2 := ih (curVar ++ [1]) (start + 1) _ h1
      simpa [List.replicate_succ, List.append_assoc] using h2

theorem encodeCnf_append (A B : cnf) : encodeCnf (A ++ B) = encodeCnf A ++ encodeCnf B := by
  induction A with
  | nil => rfl
  | cons C A ih => simp [CnfSerialize.encodeCnf_cons, ih, List.append_assoc]

theorem pass2_encodeLit (l : literal) (v off : Nat) (rest baseOut curVar acc : List Nat)
    (gotPol : Bool) (s : State)
    (hinv : p2Inv s v (encodeLit l ++ rest) (baseOut ++ encodeCnf (chainOf acc)) false gotPol curVar acc) :
    ∃ curVar',
      let acc' := if l.2 == v then acc ++ [off + l.2 + 2] else acc
      p2Inv (runLoop POS pass2InnerBody s off (encodeLit l).length) v rest
        (baseOut ++ encodeCnf (chainOf acc')) false true curVar' acc' := by
  rcases l with ⟨b, u⟩
  rw [encodeLit_len]
  have henc : encodeLit (b, u) ++ rest = 1 :: (if b then 1 else 0) :: (List.replicate u 1 ++ (0 :: rest)) := by
    simp [EvalCnfCmd.encodeLit, List.append_assoc]
  rw [henc] at hinv
  have hlen : u + 3 = 1 + (1 + (u + 1)) := by
    rw [Nat.add_comm 1 (u + 1), Nat.add_assoc, Nat.add_comm 1 (u + 2), Nat.add_assoc]
  rw [hlen, runLoop_add, runLoop_add, runLoop_add]
  rw [runLoop_succ, runLoop_zero]
  have h1 := pass2InnerBody_step s v off 1 _ _ curVar acc false gotPol (by decide) hinv
  simp only [Bool.false_eq_true, ite_false, ite_true] at h1
  rw [runLoop_succ, runLoop_zero]
  have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
  have h2 := pass2InnerBody_step _ v (off + 1) (if b then 1 else 0) _ _ [] acc true false hb h1
  simp only [Bool.false_eq_true, ite_true, ite_false] at h2
  have h3 := pass2_rep_ones u v (0 :: rest) _ [] acc (off + 1 + 1) _ h2
  rw [List.nil_append] at h3
  rw [runLoop_succ, runLoop_zero]
  have h4 := pass2InnerBody_step _ v (off + 1 + 1 + u) 0 rest _ (List.replicate u 1) acc true true (by decide) h3
  simp only [ite_true, show (0 : Nat) ≠ 1 by decide, ite_false] at h4
  refine ⟨List.replicate u 1, ?_⟩
  have hpos : off + 1 + 1 + (u : Nat) = off + (u : Nat) + 2 := by omega
  rw [hpos] at h4 ⊢
  have hrep_iff : List.replicate u 1 = List.replicate v 1 ↔ u = v := by
    constructor
    · intro h; have := congrArg List.length h; simpa using this
    · intro h; subst h; rfl
  by_cases huv : u = v
  · have hbe : (u == v) = true := beq_iff_eq.mpr huv
    simp only [hbe, ite_true]
    have hreq : List.replicate u 1 = List.replicate v 1 := hrep_iff.mpr huv
    simp only [hreq, ite_true] at h4
    rw [chainOf_append_one]
    cases acc with
    | nil => simpa [huv, chainOf, show encodeCnf [] = [] from rfl] using h4
    | cons first restAcc =>
        cases restAcc with
        | nil =>
            simpa [huv, chainOf, impChain, CnfSerialize.encodeCnf_cons, show encodeCnf [] = [] from rfl, List.append_assoc] using h4
        | cons q1 qs =>
            simpa [huv, encodeCnf_append, CnfSerialize.encodeCnf_cons, show encodeCnf [] = [] from rfl, List.append_assoc] using h4
  · have hbe : (u == v) = false := beq_false_of_ne huv
    simp only [hbe, Bool.false_eq_true, ite_false]
    have hreq : List.replicate u 1 ≠ List.replicate v 1 := fun h => huv (hrep_iff.mp h)
    simp only [hreq, ite_false] at h4
    exact h4

theorem pass2_clauseBody (C : clause) (v off : Nat) (rest baseOut curVar acc : List Nat)
    (gotPol : Bool) (s : State)
    (hinv : p2Inv s v (CnfSerialize.clauseBody C ++ rest)
      (baseOut ++ encodeCnf (chainOf acc)) false gotPol curVar acc) :
    ∃ curVar' gp',
      p2Inv (runLoop POS pass2InnerBody s off (CnfSerialize.clauseBody C).length) v rest
        (baseOut ++ encodeCnf (chainOf (acc ++ (occClause v off C).1)))
        false gp' curVar' (acc ++ (occClause v off C).1) := by
  induction C generalizing off rest curVar acc gotPol s with
  | nil =>
      exact ⟨curVar, gotPol, by simpa [CnfSerialize.clauseBody, occClause, runLoop_zero] using hinv⟩
  | cons l C ih =>
      rcases l with ⟨b, u⟩
      rw [CnfSerialize.clauseBody_cons, List.length_append, runLoop_add]
      rw [CnfSerialize.clauseBody_cons, List.append_assoc] at hinv
      obtain ⟨cv1, h1⟩ := pass2_encodeLit (b, u) v off (CnfSerialize.clauseBody C ++ rest) baseOut curVar acc gotPol s hinv
      rw [encodeLit_len] at h1 ⊢
      have hpos : off + (u + 3) = off + u + 2 + 1 := by omega
      rw [hpos]
      set acc1 := if u == v then acc ++ [off + u + 2] else acc
      obtain ⟨cv2, gp2, h2⟩ := ih (off + u + 2 + 1) rest cv1 acc1 true _ h1
      refine ⟨cv2, gp2, ?_⟩
      have hacc_eq : acc1 ++ (occClause v (off + u + 2 + 1) C).1 = acc ++ (occClause v off ((b, u) :: C)).1 := by
        simp only [acc1, occClause]
        split_ifs <;> simp [List.append_assoc]
      rw [hacc_eq] at h2
      exact h2

theorem pass2_encodeClause (C : clause) (v off : Nat) (rest baseOut curVar acc : List Nat)
    (gotPol : Bool) (s : State)
    (hinv : p2Inv s v (encodeClause C ++ rest)
      (baseOut ++ encodeCnf (chainOf acc)) false gotPol curVar acc) :
    ∃ curVar' gp',
      p2Inv (runLoop POS pass2InnerBody s off (encodeClause C).length) v rest
        (baseOut ++ encodeCnf (chainOf (acc ++ (occClause v off C).1)))
        false gp' curVar' (acc ++ (occClause v off C).1) := by
  rw [CnfSerialize.encodeClause_eq, List.length_append, runLoop_add]
  rw [CnfSerialize.encodeClause_eq, List.append_assoc] at hinv
  obtain ⟨cv1, gp1, h1⟩ := pass2_clauseBody C v off (0 :: rest) baseOut curVar acc gotPol s hinv
  rw [show ([0] : List Nat).length = 1 from rfl, runLoop_succ, runLoop_zero]
  have h2 := pass2InnerBody_step _ v (off + (CnfSerialize.clauseBody C).length) 0 rest _ cv1 _ false gp1 (by decide) h1
  simp only [Bool.false_eq_true, ite_false, show (0 : Nat) ≠ 1 by decide] at h2
  exact ⟨cv1, gp1, h2⟩

theorem pass2_encodeCnf (N : cnf) (v off : Nat) (rest baseOut curVar acc : List Nat)
    (gotPol : Bool) (s : State)
    (hinv : p2Inv s v (encodeCnf N ++ rest)
      (baseOut ++ encodeCnf (chainOf acc)) false gotPol curVar acc) :
    ∃ curVar' gp',
      p2Inv (runLoop POS pass2InnerBody s off (encodeCnf N).length) v rest
        (baseOut ++ encodeCnf (chainOf (acc ++ (occCnf v off N).1)))
        false gp' curVar' (acc ++ (occCnf v off N).1) := by
  induction N generalizing off rest curVar acc gotPol s with
  | nil =>
      exact ⟨curVar, gotPol, by simpa [EvalCnfCmd.encodeCnf, occCnf, runLoop_zero] using hinv⟩
  | cons C N ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append, runLoop_add]
      rw [CnfSerialize.encodeCnf_cons, List.append_assoc] at hinv
      obtain ⟨cv1, gp1, h1⟩ := pass2_encodeClause C v off (encodeCnf N ++ rest) baseOut curVar acc gotPol s hinv
      have hoff : off + (encodeClause C).length = (occClause v off C).2 := (occClause_snd v off C).symm
      rw [hoff]
      obtain ⟨cv2, gp2, h2⟩ := ih (occClause v off C).2 rest cv1 (acc ++ (occClause v off C).1) gp1 _ h1
      refine ⟨cv2, gp2, ?_⟩
      simpa [occCnf, List.append_assoc] using h2

theorem pass2OuterBody_eval (s : State) (N : cnf) (v : Nat) (baseOut : List Nat)
    (hINP : s.get INP = encodeCnf N) (hOUT : s.get OUT = baseOut) :
    let s1 := pass2OuterBody.eval (s.set VREG (List.replicate v 1))
    s1.get OUT = baseOut ++ encodeCnf (cycleClauses (occCnf v 0 N).1) ∧
    s1.get INP = encodeCnf N := by
  have hnw : INP ∉ pass2OuterBody.writes := by
    simp [pass2OuterBody, pass2InnerBody, emitBinClause, Cmd.writes, Op.writesTo]
  have hINP1 : (pass2OuterBody.eval (s.set VREG (List.replicate v 1))).get INP = encodeCnf N := by
    rw [Cmd.eval_get_of_not_writes _ _ _ hnw, State.get_set_ne _ _ _ _ (by decide), hINP]
  refine ⟨?_, hINP1⟩
  unfold pass2OuterBody
  simp only [Cmd.eval_seq]
  set s0 :=
    (Cmd.op (.clear PREV_ID)).eval ((Cmd.op (.clear FIRST_ID)).eval
      ((Cmd.op (.clear MULTI)).eval ((Cmd.op (.clear HAS_FIRST)).eval
        ((Cmd.op (.clear CUR_VAR)).eval ((Cmd.op (.clear GOT_POL)).eval
          ((Cmd.op (.clear IN_LIT)).eval ((Cmd.op (.copy CUR INP)).eval
            (s.set VREG (List.replicate v 1)))))))))
  have hs0_inp : s0.get INP = encodeCnf N := by
    simp [s0, Cmd.eval_op, Op.eval, State.get_set_ne, hINP]
  have hs0_inv : p2Inv s0 v (encodeCnf N ++ []) (baseOut ++ encodeCnf (chainOf [])) false false [] [] := by
    simp [p2Inv, chainOf, show encodeCnf [] = [] from rfl, s0, Cmd.eval_op, Op.eval,
      State.get_set_eq, State.get_set_ne, hINP, hOUT]
  rw [forBnd_eval_eq, hs0_inp]
  obtain ⟨_, _, hmid⟩ := pass2_encodeCnf N v 0 [] baseOut [] [] false s0 hs0_inv
  clear_value s0
  rw [List.nil_append] at hmid
  obtain ⟨_, _, hOUTm, _, _, _, hACCm⟩ := hmid
  cases hocc : (occCnf v 0 N).1 with
  | nil =>
      rw [hocc] at hACCm hOUTm
      have hM : (runLoop POS pass2InnerBody s0 0 (encodeCnf N).length).get MULTI ≠ [1] := by
        rw [hACCm.2]; simp
      rw [Cmd.eval_ifBit_false _ _ _ _ hM]
      simp [Cmd.eval_op, Op.eval, State.get_set_ne, hOUTm, chainOf, cycleClauses,
        show encodeCnf [] = [] from rfl]
  | cons first rest =>
      cases rest with
      | nil =>
          rw [hocc] at hACCm hOUTm
          have hM : (runLoop POS pass2InnerBody s0 0 (encodeCnf N).length).get MULTI ≠ [1] := by
            rw [hACCm.2.1]; simp
          rw [Cmd.eval_ifBit_false _ _ _ _ hM]
          simp [Cmd.eval_op, Op.eval, State.get_set_ne, hOUTm, chainOf, impChain, cycleClauses,
            show encodeCnf [] = [] from rfl]
      | cons q qs =>
          rw [hocc] at hACCm hOUTm
          have hM : (runLoop POS pass2InnerBody s0 0 (encodeCnf N).length).get MULTI = [1] := hACCm.2.1
          rw [Cmd.eval_ifBit_true _ _ _ _ hM]
          rw [emitBinClause_eval PREV_ID FIRST_ID _ (by decide) (by decide)
            ((q :: qs).getLast (by simp)) first hACCm.2.2.2 hACCm.2.2.1]
          rw [State.get_set_eq, hOUTm]
          simp only [chainOf, cycleClauses, encodeCnf_append, CnfSerialize.encodeCnf_cons,
            show encodeCnf [] = [] from rfl, List.append_assoc, List.append_nil]

theorem pass2_eval_out (s : State) (N : cnf) (baseOut : List Nat)
    (hINP : s.get INP = encodeCnf N) (hOUT : s.get OUT = baseOut) :
    (pass2.eval s).get OUT = baseOut ++ encodeCnf (allCycles N) := by
  unfold pass2
  rw [forBnd_eval_eq, hINP]
  have hloop : ∀ (k : Nat),
      (runLoop VREG pass2OuterBody s 0 k).get OUT =
        baseOut ++ encodeCnf ((List.range k).flatMap (fun v => cycleClauses (occCnf v 0 N).1)) ∧
      (runLoop VREG pass2OuterBody s 0 k).get INP = encodeCnf N := by
    intro k
    induction k with
    | zero => simp [runLoop_zero, hOUT, hINP, show encodeCnf [] = [] from rfl]
    | succ k ih =>
        rw [runLoop_succ_right, Nat.zero_add]
        have hstep := pass2OuterBody_eval (runLoop VREG pass2OuterBody s 0 k) N k _ ih.2 ih.1
        refine ⟨?_, hstep.2⟩
        rw [hstep.1, List.range_succ, List.flatMap_append, List.flatMap_singleton,
          encodeCnf_append, List.append_assoc]
  exact (hloop (encodeCnf N).length).1

/-! ### Putting the reduction together -/

def redFn (x : List Bool) : List Bool :=
  boolsOf (encodeCnf (to3Occ (SATStr.cnfOf x)))

theorem encodeCnf_bit (N : cnf) : ∀ v ∈ encodeCnf N, v ≤ 1 := by
  induction N with
  | nil => intro v hv; simp [show encodeCnf [] = [] from rfl] at hv
  | cons C N ih =>
      intro v hv
      rw [CnfSerialize.encodeCnf_cons, List.mem_append] at hv
      rcases hv with hC | hN
      · rw [CnfSerialize.encodeClause_eq, List.mem_append] at hC
        rcases hC with hB | h0
        · clear ih
          induction C with
          | nil => simp [CnfSerialize.clauseBody] at hB
          | cons l C ihC =>
              rw [CnfSerialize.clauseBody_cons, List.mem_append] at hB
              rcases hB with hl | hrest
              · rcases l with ⟨pol, u⟩
                simp only [EvalCnfCmd.encodeLit, List.mem_cons, List.mem_append,
                  List.mem_replicate, List.mem_singleton] at hl
                rcases hl with rfl | rfl | ⟨_, rfl⟩ | h0
                · omega
                · cases pol <;> simp
                · omega
                · simp at h0; omega
              · exact ihC hrest
        · simp only [List.mem_singleton] at h0; omega
      · exact ih v hN

theorem cmd_size_eval_le (c : Cmd) :
    ∀ s : State, State.size (c.eval s) ≤ State.size s + c.cost s := by
  induction c with
  | op o => intro s; exact Op.size_eval_le o s
  | seq c1 c2 ih1 ih2 =>
      intro s
      rw [Cmd.eval_seq, Cmd.cost_seq]
      have h1 := ih1 s
      have h2 := ih2 (c1.eval s)
      omega
  | ifBit t cT cE ihT ihE =>
      intro s
      by_cases ht : s.get t = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.cost_ifBit_true _ _ _ _ ht]
        have := ihT s; omega
      · rw [Cmd.eval_ifBit_false _ _ _ _ ht, Cmd.cost_ifBit_false _ _ _ _ ht]
        have := ihE s; omega
  | forBnd cnt bnd body ih =>
      intro s
      unfold Cmd.eval Cmd.cost Cmd.run
      set iters := (s.get bnd).length
      have hfold : ∀ (k : Nat), k ≤ iters →
          let res := (List.range k).foldl
            (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let r := Cmd.run body s'
              (r.1, acc.2 + r.2))
            (s, 0)
          State.size res.1 ≤ State.size s + res.2 + k * iters := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ihk =>
            intro hk
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hprev := ihk (by omega)
            set prev := (List.range k).foldl
              (fun acc i =>
                let s' := acc.1.set cnt (List.replicate i 1)
                let r := Cmd.run body s'
                (r.1, acc.2 + r.2))
              (s, 0)
            have hset : State.size (prev.1.set cnt (List.replicate k 1)) ≤ State.size prev.1 + k := by
              have hadd := State.size_set_add prev.1 cnt (List.replicate k 1)
              simp only [List.length_replicate] at hadd
              omega
            have hbody := ih (prev.1.set cnt (List.replicate k 1))
            unfold Cmd.eval Cmd.cost at hbody
            have hmul : (k + 1) * iters = k * iters + iters := by rw [Nat.add_mul, Nat.one_mul]
            dsimp only at hprev ⊢
            omega
      have hfin := hfold iters le_rfl
      dsimp only at hfin ⊢
      omega

theorem redCmd_eval_out (x : List Bool) :
    boolsOf ((redCmd.eval (certState x)).get OUT) = redFn x := by
  have hagree : AgreeBelow 25 (certState x) (SATStr.strEIn (x, [])) := by
    intro r _
    cases r with
    | zero => rfl
    | succ r => cases r <;> rfl
  have hbuild_uses : Cmd.UsesBelow SATStr.satStrBuild 25 := by
    simp [SATStr.satStrBuild, SATStr.satStrPre, SATStr.satStrPostA, SATStr.satStrPostB,
      SATStr.badBranch, SATStr.scanBody, Cmd.UsesBelow, Op.UsesBelow,
      SATStr.WCUR, SATStr.WIDX, SATStr.WHD, SATStr.WSA, SATStr.WSB, SATStr.WTAL,
      EvalCnfCmd.OUTPUT, EvalCnfCmd.CLAUSE_TALLY, EvalCnfCmd.CNF_STREAM, EvalCnfCmd.ASSGN]
  have hag := Cmd.eval_agree SATStr.satStrBuild 25 hbuild_uses hagree
  obtain ⟨h0, _, h2, _⟩ := SATStr.satStrBuild_get x []
  have hOUT0 : (SATStr.satStrBuild.eval (certState x)).get OUT = [] :=
    (hag OUT (by decide)).trans h0
  have hINP0 : (SATStr.satStrBuild.eval (certState x)).get INP = encodeCnf (SATStr.cnfOf x) :=
    (hag INP (by decide)).trans h2
  unfold redCmd
  rw [Cmd.eval_seq, Cmd.eval_seq]
  obtain ⟨hp1_out, hp1_inp⟩ := pass1_eval_out _ (SATStr.cnfOf x) hINP0 hOUT0
  have hp2_out := pass2_eval_out _ (SATStr.cnfOf x) _ hp1_inp hp1_out
  rw [hp2_out, ← encodeCnf_append]
  rfl

theorem redCmd_cost : ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ x : List Bool, redCmd.cost (certState x) ≤ budget (encodable.size x) ∧
      encodable.size (redFn x) ≤ budget (encodable.size x) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk redCmd regMask redCmd_chk
  refine ⟨fun n => 2 * (n + K * (n + 1) ^ (D + 1)) + 1, ?_, ?_, fun x => ?_⟩
  · have hpow : inOPoly (fun n => (n + 1) ^ (D + 1)) := by
      refine ⟨D + 1, 2 ^ (D + 1), 1, fun n hn => ?_⟩
      calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
    exact inOPoly_add (inOPoly_mul (inOPoly_const 2)
      (inOPoly_add inOPoly_id (inOPoly_mul (inOPoly_const K) hpow))) (inOPoly_const 1)
  · intro a b hab
    have hp : (a + 1) ^ (D + 1) ≤ (b + 1) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
    have hm : K * (a + 1) ^ (D + 1) ≤ K * (b + 1) ^ (D + 1) := Nat.mul_le_mul_left K hp
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add hab hm)) 1
  · have hsz_in : State.size (certState x) ≤ encodable.size x := by
      show (strBits x).length + 0 ≤ encodable.size x
      rw [strBits_length, Nat.add_zero]
      exact CookLevin.length_le_size x
    have hcost : redCmd.cost (certState x) ≤ K * (encodable.size x + 1) ^ (D + 1) :=
      hb (certState x) (encodable.size x) hsz_in
    have hsz_out : encodable.size (redFn x) ≤ 2 * (redFn x).length :=
      CookLevin.size_le_two_mul_length (redFn x)
    have hlen_out : (redFn x).length ≤ State.size (redCmd.eval (certState x)) := by
      rw [← redCmd_eval_out x]
      show (boolsOf ((redCmd.eval (certState x)).get OUT)).length ≤ _
      have hbl : (boolsOf ((redCmd.eval (certState x)).get OUT)).length =
          ((redCmd.eval (certState x)).get OUT).length := by simp [boolsOf]
      rw [hbl]
      have hget_le : ∀ (st : State) (r : Var), (st.get r).length ≤ State.size st := by
        intro st r
        induction st generalizing r with
        | nil => simp [State.get, State.size]
        | cons a st ih =>
            cases r with
            | zero => simp [State.get, State.size]
            | succ r =>
                have h := ih r
                simp only [State.get, State.size, List.map_cons, List.foldr_cons,
                  List.getElem?_cons_succ] at h ⊢
                omega
      exact hget_le _ OUT
    have hsz_eval : State.size (redCmd.eval (certState x)) ≤
        State.size (certState x) + redCmd.cost (certState x) :=
      cmd_size_eval_le redCmd (certState x)
    dsimp only
    constructor
    · exact le_trans hcost (by omega)
    · exact le_trans hsz_out (by omega)

noncomputable def redWitness : PolyTimeComputableLang redFn where
  c := redCmd
  encodeIn := certState
  decodeOut := fun s => boolsOf (s.get OUT)
  cost_bound := redCmd_cost.choose
  cost_bound_poly := redCmd_cost.choose_spec.1
  cost_bound_mono := redCmd_cost.choose_spec.2.1
  encBound := id
  encBound_poly := inOPoly_id
  encBound_mono := fun _ _ h => h
  encodeIn_size := fun x => by
    show (strBits x).length + 0 ≤ encodable.size x
    rw [strBits_length, Nat.add_zero]
    exact CookLevin.length_le_size x
  computes := redCmd_eval_out
  cost_le := fun x => (redCmd_cost.choose_spec.2.2 x).1
  output_size_le := fun x => (redCmd_cost.choose_spec.2.2 x).2
  enc_bit := fun x => by
    intro r hr
    simp only [certState, List.mem_singleton] at hr
    subst hr
    exact strBits_bit x
  regBound := 25
  usesBelow := redCmd_usesBelow
  width_le := fun _ => by show 1 ≤ 25; omega
  decode_agree := fun x m => by
    have hag : AgreeBelow 25 (certState x ++ List.replicate m []) (certState x) := by
      intro r _
      unfold State.get
      by_cases hr : r < (certState x).length
      · rw [List.getElem?_append_left hr]
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hr)]
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hr)]
        by_cases hm : r - (certState x).length < m
        · simp [hm]
        · rw [List.getElem?_eq_none (by simp only [List.length_replicate]; omega)]
    have h := Cmd.eval_agree redCmd 25 redCmd_usesBelow hag OUT (by decide)
    exact congrArg boolsOf h

theorem redFn_spec (x : List Bool) :
    SATStr.cnfOf (redFn x) = to3Occ (SATStr.cnfOf x) := by
  unfold SATStr.cnfOf redFn
  rw [strBits_boolsOf (encodeCnf_bit _), CnfWellFormed.parseTotal_encodeCnf]
  rfl

end PvsNP.Units.m3_sat_to_3occ_sat

/-- Cook-Levin reduction from SAT to 3-occurrence SAT. -/
theorem PvsNP.Units.m3_sat_to_3occ_sat :
    CookLevin.reducesPoly SATStr
      (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
        SAT (SATStr.cnfOf x)) := by
  obtain ⟨t, M, ht, hM, hT1, hcomp⟩ :=
    PvsNP.Units.m3_sat_to_3occ_sat.redWitness.toMachine (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨PvsNP.Units.m3_sat_to_3occ_sat.redFn, t, M, ht, hM, hT1, hcomp, fun x => ?_⟩
  dsimp only
  rw [PvsNP.Units.m3_sat_to_3occ_sat.redFn_spec x]
  constructor
  · intro hsat
    exact ⟨PvsNP.Units.m3_sat_to_3occ_sat.to3Occ_countP_le_three _,
      (PvsNP.Units.m3_sat_to_3occ_sat.to3Occ_sat_iff _).mp hsat⟩
  · rintro ⟨_, hsat⟩
    exact (PvsNP.Units.m3_sat_to_3occ_sat.to3Occ_sat_iff _).mpr hsat
