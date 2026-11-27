import Mathlib
import PvsNP.Defs
import CookLevin

/-
Closes m3_xor_sum_refutation: a parity (XOR) system in which every variable
occurs an even number of times and an odd number of right-hand sides are true
has no solution. The proof adds the equations two ways: the counts of entries
in an assignment over the pairs of S add up to the count over
S.flatMap Prod.fst, which is even because each variable occurs an even number
of times; the right-hand sides add up to an odd number.
-/

set_option autoImplicit false

namespace PvsNP.Units.m3_xor_sum_refutation

/-- A list in which every value occurs an even number of times has even length:
remove the head together with a second occurrence of it, and induct on a
length bound. -/
theorem even_length_of_even_counts_aux : ∀ (n : ℕ) (G : List var),
    G.length ≤ n → (∀ v, G.count v % 2 = 0) → G.length % 2 = 0 := by
  intro n
  induction n with
  | zero =>
    intro G hlen _
    cases G with
    | nil => simp
    | cons v G' => simp at hlen
  | succ n ih =>
    intro G hlen hev
    cases G with
    | nil => simp
    | cons v G' =>
      have hcv : (v :: G').count v % 2 = 0 := hev v
      rw [List.count_cons] at hcv
      have hvv : (v == v) = true := by simp
      rw [if_pos hvv] at hcv
      have hodd : G'.count v % 2 = 1 := by omega
      have hvG' : v ∈ G' := List.count_pos_iff.mp (by omega)
      have hev2 : ∀ w, (G'.erase v).count w % 2 = 0 := by
        intro w
        rw [List.count_erase]
        by_cases hw : (v == w) = true
        · have hvw : v = w := beq_iff_eq.mp hw
          subst hvw
          rw [if_pos hw]
          omega
        · rw [if_neg hw]
          have hw2 := hev w
          rw [List.count_cons, if_neg hw] at hw2
          omega
      have hlen2 : (G'.erase v).length ≤ n := by
        rw [List.length_erase, if_pos hvG']
        have hle : (v :: G').length ≤ n + 1 := hlen
        simp only [List.length_cons] at hle
        omega
      have h2 := ih (G'.erase v) hlen2 hev2
      have hlen_eq : (v :: G').length = (G'.erase v).length + 2 := by
        rw [List.length_erase, if_pos hvG']
        have hpos : 0 < G'.length := List.length_pos_iff.mpr (by
          intro hnil
          rw [hnil] at hvG'
          exact List.not_mem_nil hvG')
        simp only [List.length_cons]
        omega
      omega

/-- A list in which every value occurs an even number of times has even length. -/
theorem even_length_of_even_counts (G : List var) (hev : ∀ v, G.count v % 2 = 0) :
    G.length % 2 = 0 :=
  even_length_of_even_counts_aux G.length G le_rfl hev

/-- Filtering out every occurrence of a value whose predicate is false leaves
no occurrence of it. -/
theorem count_filter_false (p : var → Bool) (F : List var) (v : var)
    (hv : p v = false) : (F.filter p).count v = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  rw [List.mem_filter] at hmem
  rw [hmem.2] at hv
  exact Bool.noConfusion hv

/-- The total number of assigned entries, mod 2, equals the number of true
right-hand sides, mod 2: each equation fixes the parity of its own count. -/
theorem sum_parity : ∀ (S : List (List var × Bool)) (a : assgn),
    (∀ e ∈ S, decide ((e.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = e.2) →
    (S.map (fun e => (e.1.filter (fun v => decide (v ∈ a))).length)).sum % 2
      = (S.filter (fun e => e.2)).length % 2 := by
  intro S a
  induction S with
  | nil => intro _; simp
  | cons e S ih =>
    intro h
    have he : decide ((e.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = e.2 :=
      h e List.mem_cons_self
    have hS : ∀ e' ∈ S,
        decide ((e'.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = e'.2 :=
      fun e' h' => h e' (List.mem_cons_of_mem _ h')
    have ih' := ih hS
    have hpar : (e.1.filter (fun v => decide (v ∈ a))).length % 2
        = (if e.2 then 1 else 0) := by
      by_cases he2 : e.2 = true
      · rw [he2] at he
        simp only [he2, if_true]
        rw [decide_eq_true_eq] at he
        exact he
      · rw [if_neg he2]
        have hne : ¬ ((e.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) :=
          decide_eq_false_iff_not.mp (he.trans (Bool.eq_false_iff.mpr he2))
        have hlt : (e.1.filter (fun v => decide (v ∈ a))).length % 2 < 2 :=
          Nat.mod_lt _ (by norm_num)
        omega
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases he2 : e.2 = true
    · rw [if_pos he2] at hpar ⊢
      simp only [List.length_cons]
      omega
    · rw [if_neg he2] at hpar ⊢
      omega

/-- The total number of assigned entries is even: it equals the length of the
filtered flat list, in which every value still occurs an even number of times. -/
theorem sum_even : ∀ (S : List (List var × Bool)) (a : assgn),
    (∀ v, (S.flatMap Prod.fst).count v % 2 = 0) →
    (S.map (fun e => (e.1.filter (fun v => decide (v ∈ a))).length)).sum % 2 = 0 := by
  intro S a hEven
  have hN : (S.map (fun e => (e.1.filter (fun v => decide (v ∈ a))).length)).sum
      = ((S.flatMap Prod.fst).filter (fun v => decide (v ∈ a))).length := by
    simp only [List.filter_flatMap, List.length_flatMap]
  rw [hN]
  apply even_length_of_even_counts
  intro v
  by_cases hv : decide (v ∈ a) = true
  · rw [List.count_filter (p := fun v => decide (v ∈ a)) (a := v) hv]
    exact hEven v
  · have h0 := count_filter_false (fun v => decide (v ∈ a)) (S.flatMap Prod.fst) v
      (Bool.eq_false_of_ne_true hv)
    rw [h0]

end PvsNP.Units.m3_xor_sum_refutation

/-- A parity system with every variable occurring evenly and an odd number of
true right-hand sides has no solution. -/
theorem PvsNP.Units.m3_xor_sum_refutation :
    ∀ S : List (List var × Bool),
      (∀ v : var, (S.flatMap Prod.fst).count v % 2 = 0) →
      (S.filter (fun e => e.2)).length % 2 = 1 →
        ¬ ∃ a : assgn, ∀ e ∈ S,
          decide ((e.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = e.2 := by
  intro S hEven hOdd
  rintro ⟨a, ha⟩
  have hA := PvsNP.Units.m3_xor_sum_refutation.sum_parity S a ha
  have hB := PvsNP.Units.m3_xor_sum_refutation.sum_even S a hEven
  omega
