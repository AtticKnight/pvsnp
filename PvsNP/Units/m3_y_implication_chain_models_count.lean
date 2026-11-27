import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_implication_chain_models_count

private def chain (n : ℕ) : cnf :=
  (List.range n).map (fun i => [(false, i), (true, i + 1)])

private theorem evalCnf_chain_iff (a : assgn) (n : ℕ) :
    evalCnf a (chain n) = true ↔ ∀ i < n, i ∈ a → i + 1 ∈ a := by
  simp only [chain, evalCnf_clause_iff, List.mem_map, List.mem_range]
  constructor
  · intro h i hi hia
    have hcl := h [(false, i), (true, i + 1)] ⟨i, hi, rfl⟩
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      evalLiteral, evalVar, decide_eq_true_eq, decide_eq_false_iff_not] at hcl
    rcases hcl with hni | hi1
    · exact absurd hia hni
    · exact hi1
  · intro h C hC
    rcases hC with ⟨i, hi, rfl⟩
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      evalLiteral, evalVar, decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases hia : i ∈ a
    · exact Or.inr (h i hi hia)
    · exact Or.inl hia

private theorem flatMap_pair_perm (L : List (List ℕ)) (a : ℕ) :
    (L.flatMap (fun s => [s, a :: s])).Perm (L ++ L.map (a :: ·)) := by
  induction L with
  | nil => simp
  | cons s ts ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]
    refine List.Perm.cons s ?_
    refine (List.Perm.cons (a :: s) ih).trans ?_
    exact (List.perm_middle).symm

private theorem sublists_cons_perm (a : ℕ) (t : List ℕ) :
    (a :: t).sublists.Perm (t.sublists ++ t.sublists.map (a :: ·)) := by
  rw [List.sublists_cons]
  exact flatMap_pair_perm t.sublists a

private theorem sublists_perm_append_singleton (l : List ℕ) (x : ℕ) :
    (l ++ [x]).sublists.Perm (l.sublists ++ l.sublists.map (· ++ [x])) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.cons_append]
    refine (sublists_cons_perm a (t ++ [x])).trans ?_
    refine (ih.append (ih.map (a :: ·))).trans ?_
    rw [List.map_append, List.map_map]
    have heq : ((fun l => a :: l) ∘ (fun l => l ++ [x])) =
        ((fun l => l ++ [x]) ∘ (fun l => a :: l)) := by
      funext s; simp
    rw [heq, ← List.map_map]
    have h1 : (t.sublists ++ t.sublists.map (· ++ [x]) ++
        (t.sublists.map (a :: ·) ++ (t.sublists.map (a :: ·)).map (· ++ [x]))).Perm
        ((t.sublists ++ t.sublists.map (a :: ·)) ++
        (t.sublists ++ t.sublists.map (a :: ·)).map (· ++ [x])) := by
      rw [List.map_append, List.append_assoc, List.append_assoc]
      refine List.Perm.append_left _ ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
    exact h1.trans ((sublists_cons_perm a t).symm.append ((sublists_cons_perm a t).symm.map _))

private theorem filter_nil_sublists (l : List ℕ) :
    (l.sublists.filter (fun a => decide (a = []))).length = 1 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hp := (sublists_cons_perm a t).filter (fun s => decide (s = []))
    rw [hp.length_eq, List.filter_append, List.length_append, ih, List.filter_map]
    have h0 : (t.sublists.filter ((fun s => decide (s = [])) ∘ (a :: ·))).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro s _
      simp
    simp [h0]

private theorem reach_top {a : List ℕ} {n : ℕ}
    (hstep : ∀ i < n, i ∈ a → i + 1 ∈ a) :
    ∀ m ≤ n, ∀ k ≤ m, k ∈ a → m ∈ a := by
  intro m hm
  induction m with
  | zero =>
    intro k hk hka
    have : k = 0 := by omega
    subst this
    exact hka
  | succ m ih =>
    intro k hk hka
    by_cases hkm : k = m + 1
    · subst hkm; exact hka
    · exact hstep m (by omega) (ih (by omega) k (by omega) hka)

private theorem filter_congr_mem {α : Type} {p q : α → Bool} {L : List α}
    (h : ∀ x ∈ L, p x = q x) : L.filter p = L.filter q := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, List.filter_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem evalCnf_no_top (n : ℕ) {a : List ℕ} (ha : a ∈ (List.range (n + 1)).sublists) :
    evalCnf a (chain (n + 1)) = decide (a = []) := by
  apply Bool.eq_iff_iff.2
  rw [evalCnf_chain_iff, decide_eq_true_eq]
  have hsub : List.Sublist a (List.range (n + 1)) := List.mem_sublists.mp ha
  constructor
  · intro hstep
    cases a with
    | nil => rfl
    | cons v vs =>
      have hv_lt : v < n + 1 := List.mem_range.mp (hsub.subset List.mem_cons_self)
      have htop : n + 1 ∈ v :: vs :=
        reach_top hstep (n + 1) (le_refl _) v (Nat.le_of_lt hv_lt) List.mem_cons_self
      have htop_lt : n + 1 < n + 1 := List.mem_range.mp (hsub.subset htop)
      omega
  · rintro rfl i _ hi
    exact absurd hi List.not_mem_nil

private theorem evalCnf_with_top (n : ℕ) (a : List ℕ) :
    evalCnf (a ++ [n + 1]) (chain (n + 1)) = evalCnf a (chain n) := by
  apply Bool.eq_iff_iff.2
  rw [evalCnf_chain_iff, evalCnf_chain_iff]
  constructor
  · intro h i hi hia
    have h1 := h i (by omega) (List.mem_append_left _ hia)
    rw [List.mem_append, List.mem_singleton] at h1
    rcases h1 with hmem | heq
    · exact hmem
    · omega
  · intro h i hi hia
    by_cases hin : i < n
    · rw [List.mem_append, List.mem_singleton] at hia
      rcases hia with hmem | heq
      · exact List.mem_append_left _ (h i hin hmem)
      · omega
    · have hieq : i = n := by omega
      subst hieq
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem main : ∀ n : ℕ,
    ((List.range (n + 1)).sublists.filter (fun a => evalCnf a (chain n))).length = n + 2 := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.range_succ]
    have hperm := (sublists_perm_append_singleton (List.range (n + 1)) (n + 1)).filter
      (fun a => evalCnf a (chain (n + 1)))
    rw [hperm.length_eq, List.filter_append, List.length_append, List.filter_map, List.length_map]
    have h1 : (List.range (n + 1)).sublists.filter (fun a => evalCnf a (chain (n + 1))) =
        (List.range (n + 1)).sublists.filter (fun a => decide (a = [])) :=
      filter_congr_mem (fun a ha => evalCnf_no_top n ha)
    have h2 : (List.range (n + 1)).sublists.filter
          ((fun a => evalCnf a (chain (n + 1))) ∘ (· ++ [n + 1])) =
        (List.range (n + 1)).sublists.filter (fun a => evalCnf a (chain n)) :=
      filter_congr_mem (fun a _ => evalCnf_with_top n a)
    rw [h1, filter_nil_sublists, h2, ih]
    omega

end PvsNP.Units.m3_y_implication_chain_models_count

theorem PvsNP.Units.m3_y_implication_chain_models_count :
    ∀ n : ℕ,
      ((List.range (n + 1)).sublists.filter (fun a =>
        evalCnf a ((List.range n).map (fun i => [(false, i), (true, i + 1)])))).length = n + 2 :=
  PvsNP.Units.m3_y_implication_chain_models_count.main
