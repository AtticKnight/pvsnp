import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-! The tally language of a cofinite set of numbers is in P: for a finite
    forbidden set `A`, a finite automaton counts all-true prefixes up to
    `A.sup id + 1` (and sinks on a `false`); decided by the settled unit
    `m2_dfa_in_p`. -/

namespace PvsNP.Units.m2_z_tally_cofinite_p

def bound (A : Finset ℕ) : ℕ := A.sup id + 1

abbrev St (A : Finset ℕ) := Option (Fin (bound A + 1))

def step (A : Finset ℕ) : St A → Bool → St A
  | none, _ => none
  | some _, false => none
  | some k, true =>
      if h : k.val + 1 < bound A + 1 then some ⟨k.val + 1, h⟩ else some k

def start (A : Finset ℕ) : St A :=
  some ⟨0, Nat.succ_pos _⟩

def acc (A : Finset ℕ) : St A → Bool
  | none => false
  | some k => if k.val < bound A then decide (k.val ∉ A) else true

theorem foldl_none (A : Finset ℕ) (x : List Bool) :
    x.foldl (step A) none = none := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp [step, ih]

theorem step_false (A : Finset ℕ) (q : St A) : step A q false = none := by
  cases q <;> rfl

theorem run_has_false (A : Finset ℕ) {x : List Bool} (hx : false ∈ x) :
    x.foldl (step A) (start A) = none := by
  obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hx
  rw [List.foldl_append, List.foldl_cons, step_false, foldl_none]

theorem not_mem_of_ge_bound (A : Finset ℕ) {n : ℕ} (h : bound A ≤ n) : n ∉ A := by
  intro hn
  have hle : n ≤ A.sup id := by
    simpa [id] using Finset.le_sup (f := id) hn
  simp only [bound] at h
  omega

theorem run_replicate (A : Finset ℕ) :
    ∀ n : ℕ, (List.replicate n true).foldl (step A) (start A) =
      some ⟨n ⊓ bound A, Nat.lt_succ_of_le (Nat.min_le_right n (bound A))⟩ := by
  intro n
  induction n with
  | zero =>
      simp [start]
  | succ n ih =>
      rw [List.replicate_succ']
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp only [step]
      by_cases hn : n < bound A
      · have hmin : n ⊓ bound A = n := Nat.min_eq_left (le_of_lt hn)
        have hlt : n + 1 < bound A + 1 := Nat.add_lt_add_right hn 1
        simp only [hmin, hlt, ↓reduceDIte]
        have hmin' : (n + 1) ⊓ bound A = n + 1 :=
          Nat.min_eq_left (Nat.succ_le_of_lt hn)
        simp [hmin']
      · have hmin : n ⊓ bound A = bound A := Nat.min_eq_right (le_of_not_gt hn)
        have hdit : ¬ ((n ⊓ bound A) + 1 < bound A + 1) := by
          rw [hmin]; exact Nat.lt_irrefl _
        simp only [hdit, ↓reduceDIte]
        have hmin' : (n + 1) ⊓ bound A = bound A :=
          Nat.min_eq_right (Nat.le_succ_of_le (le_of_not_gt hn))
        simp [hmin, hmin']

theorem eq_replicate_of_not_mem_false {x : List Bool} (h : false ∉ x) :
    x = List.replicate x.length true := by
  refine List.eq_replicate_iff.mpr ⟨rfl, ?_⟩
  intro b hb
  cases b
  · exact (h hb).elim
  · rfl

theorem acc_run (A : Finset ℕ) (x : List Bool) :
    acc A (x.foldl (step A) (start A)) = true ↔
      false ∉ x ∧ x.length ∉ A := by
  by_cases hx : false ∈ x
  · simp [run_has_false A hx, acc, hx]
  · have hxrep := eq_replicate_of_not_mem_false hx
    have hrun := run_replicate A x.length
    rw [← hxrep] at hrun
    rw [hrun, acc]
    by_cases hn : x.length < bound A
    · have hmin : x.length ⊓ bound A = x.length := Nat.min_eq_left (le_of_lt hn)
      simp [hmin, hn, hx]
    · have hmin : x.length ⊓ bound A = bound A := Nat.min_eq_right (le_of_not_gt hn)
      have hge : bound A ≤ x.length := le_of_not_gt hn
      simp [hmin, hx, not_mem_of_ge_bound A hge]

end PvsNP.Units.m2_z_tally_cofinite_p

theorem PvsNP.Units.m2_z_tally_cofinite_p :
    ∀ A : Finset ℕ,
      ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} :
        Language Bool) ∈ PvsNP.P := by
  intro A
  have hset :
      ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool) =
        {x : List Bool | PvsNP.Units.m2_z_tally_cofinite_p.acc A
          (x.foldl (PvsNP.Units.m2_z_tally_cofinite_p.step A)
            (PvsNP.Units.m2_z_tally_cofinite_p.start A)) = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, PvsNP.Units.m2_z_tally_cofinite_p.acc_run]
    constructor
    · rintro ⟨n, hnA, rfl⟩
      refine ⟨?_, by simpa [List.length_replicate] using hnA⟩
      intro hfalse
      simp [List.mem_replicate] at hfalse
    · intro ⟨hfalse, hlen⟩
      refine ⟨x.length, hlen, PvsNP.Units.m2_z_tally_cofinite_p.eq_replicate_of_not_mem_false hfalse⟩
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p
    (PvsNP.Units.m2_z_tally_cofinite_p.St A)
    (PvsNP.Units.m2_z_tally_cofinite_p.step A)
    (PvsNP.Units.m2_z_tally_cofinite_p.start A)
    (PvsNP.Units.m2_z_tally_cofinite_p.acc A)
