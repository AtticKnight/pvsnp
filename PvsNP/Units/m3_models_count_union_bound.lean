import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_clause_falsifiers_count

namespace PvsNP.Units.m3_models_count_union_bound

/-- Filtering by the constantly-true predicate `evalCnf · []` changes nothing. -/
theorem filter_evalCnf_nil (l : List (List ℕ)) :
    l.filter (fun a => evalCnf a []) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp [show evalCnf a [] = true from rfl, ih]

/-- Splitting a list by a boolean predicate and its negation preserves length. -/
theorem length_filter_split (p : List ℕ → Bool) (l : List (List ℕ)) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases hp : p a = true
      · have e1 : (a :: l).filter p = a :: l.filter p := by simp [hp]
        have e2 : (a :: l).filter (fun a => !p a) = l.filter (fun a => !p a) := by simp [hp]
        rw [e1, e2]
        simp only [List.length_cons]
        omega
      · have hpf : p a = false := by
          cases h : p a with
          | false => rfl
          | true => exact absurd h hp
        have e1 : (a :: l).filter p = l.filter p := by simp [hpf]
        have e2 : (a :: l).filter (fun a => !p a) = a :: l.filter (fun a => !p a) := by
          simp [hpf]
        rw [e1, e2]
        simp only [List.length_cons]
        omega

/-- The union bound on the number of models, by induction on the CNF:
every non-model falsifies some clause, and each clause has at most
`2 ^ (n - C.length)` falsifiers among the sublists of `List.range n`. -/
theorem models_count_aux (n : ℕ) : ∀ N : cnf,
    (∀ C ∈ N, (C.map Prod.snd).Nodup ∧ ∀ l ∈ C, l.2 < n) →
    2 ^ n ≤ ((List.range n).sublists.filter (fun a => evalCnf a N)).length +
      (N.map (fun C => 2 ^ (n - C.length))).sum := by
  intro N
  induction N with
  | nil =>
      intro _
      rw [filter_evalCnf_nil]
      simp [List.length_sublists]
  | cons C N ih =>
      intro h
      have hC : (C.map Prod.snd).Nodup ∧ ∀ l ∈ C, l.2 < n :=
        h C List.mem_cons_self
      have hN : ∀ C' ∈ N, (C'.map Prod.snd).Nodup ∧ ∀ l ∈ C', l.2 < n :=
        fun C' hC' => h C' (List.mem_cons_of_mem _ hC')
      have ih' := ih hN
      -- Split the models of `N` according to whether they satisfy `C`.
      have hsplit := length_filter_split (fun a => evalClause a C)
        ((List.range n).sublists.filter (fun a => evalCnf a N))
      simp only [List.filter_filter] at hsplit
      -- The models of `C :: N` are the models of `N` satisfying `C`.
      have hmod : (List.range n).sublists.filter (fun a => evalCnf a (C :: N)) =
          (List.range n).sublists.filter (fun a => evalClause a C && evalCnf a N) := by
        apply List.filter_congr
        intro a _
        simp only [evalCnf, List.all_cons]
      -- The models of `N` falsifying `C` are among the falsifiers of `C`.
      have hle : ((List.range n).sublists.filter
          (fun a => !evalClause a C && evalCnf a N)).length ≤
          ((List.range n).sublists.filter (fun a => !evalClause a C)).length := by
        have hsub : (List.range n).sublists.filter
            (fun a => !evalClause a C && evalCnf a N) =
            ((List.range n).sublists.filter (fun a => !evalClause a C)).filter
              (fun a => evalCnf a N) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro a _
          exact Bool.and_comm _ _
        rw [hsub]
        exact List.Sublist.length_le List.filter_sublist
      have hcount := PvsNP.Units.m3_clause_falsifiers_count n C hC.1 hC.2
      have hsum : ((C :: N).map (fun C => 2 ^ (n - C.length))).sum =
          2 ^ (n - C.length) + (N.map (fun C => 2 ^ (n - C.length))).sum := by
        simp
      rw [hsum]
      have hA : ((List.range n).sublists.filter (fun a => evalCnf a (C :: N))).length +
          ((List.range n).sublists.filter (fun a => !evalClause a C && evalCnf a N)).length =
          ((List.range n).sublists.filter (fun a => evalCnf a N)).length := by
        rw [hmod]
        exact hsplit
      calc 2 ^ n ≤ ((List.range n).sublists.filter (fun a => evalCnf a N)).length +
              (N.map (fun C => 2 ^ (n - C.length))).sum := ih'
        _ = ((List.range n).sublists.filter (fun a => evalCnf a (C :: N))).length +
              ((List.range n).sublists.filter (fun a => !evalClause a C && evalCnf a N)).length +
              (N.map (fun C => 2 ^ (n - C.length))).sum := by rw [hA]
        _ ≤ ((List.range n).sublists.filter (fun a => evalCnf a (C :: N))).length +
              2 ^ (n - C.length) +
              (N.map (fun C => 2 ^ (n - C.length))).sum := by
          apply Nat.add_le_add_right
          apply Nat.add_le_add_left
          rw [← hcount]
          exact hle
        _ = ((List.range n).sublists.filter (fun a => evalCnf a (C :: N))).length +
              (2 ^ (n - C.length) + (N.map (fun C => 2 ^ (n - C.length))).sum) :=
          Nat.add_assoc _ _ _

end PvsNP.Units.m3_models_count_union_bound

/-- At least `2^n − Σ 2^(n−|C|)` of the assignments to `n` variables satisfy a CNF
(the union bound, vendored model). -/
theorem PvsNP.Units.m3_models_count_union_bound :
    ∀ (n : ℕ) (N : cnf), (∀ C ∈ N, (C.map Prod.snd).Nodup ∧ ∀ l ∈ C, l.2 < n) →
    2 ^ n ≤ ((List.range n).sublists.filter (fun a => evalCnf a N)).length +
      (N.map (fun C => 2 ^ (n - C.length))).sum :=
  fun n => PvsNP.Units.m3_models_count_union_bound.models_count_aux n
