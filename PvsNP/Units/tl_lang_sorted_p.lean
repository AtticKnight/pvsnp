import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-!
The sorted lists of booleans (every `false` before every `true`) are in `P` (TM2).
A two-bit automaton decides them: its state records whether a `true` has been seen
and whether a `false` has followed a `true`.  The automaton is the one of the settled
unit `m2_dfa_in_p`, applied to the two-bit state `Bool × Bool`.
-/

namespace PvsNP.Units.tl_lang_sorted_p

/-- The transition of the two-bit automaton.  The first bit records whether a `true`
    has been seen; the second records whether a `false` has followed a `true`. -/
def trans (p : Bool × Bool) (b : Bool) : Bool × Bool :=
  (p.1 || b, p.2 || (p.1 && !b))

/-- Accept when the list was never bad. -/
def accept (p : Bool × Bool) : Bool := !p.2

/-- Whether the list contains a `true`. -/
def hasTrue : List Bool → Bool
  | [] => false
  | b :: rest => b || hasTrue rest

/-- Whether a `false` occurs after a `true`, where the flag `s` says a `true` was
    already seen before the list starts. -/
def bad : Bool → List Bool → Bool
  | _, [] => false
  | s, b :: rest => (s && !b) || bad (s || b) rest

/-- What the automaton computes: the first bit says whether a `true` was seen,
    the second whether a `false` followed a `true`. -/
theorem fold_eq (x : List Bool) (s t : Bool) :
    x.foldl trans (s, t) = (s || hasTrue x, t || bad s x) := by
  induction x generalizing s t with
  | nil => simp [hasTrue, bad]
  | cons b rest ih =>
    show rest.foldl trans (s || b, t || (s && !b))
      = (s || hasTrue (b :: rest), t || bad s (b :: rest))
    rw [ih]
    simp only [hasTrue, bad]
    cases s <;> cases t <;> cases b <;> simp

/-- With a `true` already seen, the list is good exactly when it is all `true`. -/
theorem bad_true (x : List Bool) :
    bad true x = false ↔ ∀ b ∈ x, b = true := by
  induction x with
  | nil =>
    constructor
    · intro _
      intro b hb
      simp at hb
    · intro _
      rfl
  | cons b rest ih =>
    cases b with
    | false =>
      constructor
      · intro h
        simp [bad] at h
      · intro h
        have h2 := h false (List.mem_cons.mpr (Or.inl rfl))
        simp at h2
    | true =>
      have e : bad true (true :: rest) = bad true rest := by simp [bad]
      rw [e]
      constructor
      · intro h c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact ih.mp h c hc
      · intro h
        apply ih.mpr
        intro c hc
        exact h c (List.mem_cons.mpr (Or.inr hc))

/-- A list of all `true`s is sorted. -/
theorem all_true_sorted (x : List Bool) (h : ∀ b ∈ x, b = true) :
    List.SortedLE x := by
  induction x with
  | nil => exact List.sortedLE_nil
  | cons b rest ih =>
    have hb : b = true := h b (List.mem_cons.mpr (Or.inl rfl))
    have hr : ∀ c ∈ rest, c = true :=
      fun c hc => h c (List.mem_cons.mpr (Or.inr hc))
    subst hb
    rw [List.sortedLE_cons]
    exact ⟨fun c hc => by simp [hr c hc], ih hr⟩

/-- With no `true` seen before the list, the list is good exactly when it is sorted. -/
theorem bad_false_sorted (x : List Bool) :
    bad false x = false ↔ List.SortedLE x := by
  induction x with
  | nil =>
    constructor
    · intro _
      exact List.sortedLE_nil
    · intro _
      rfl
  | cons b rest ih =>
    cases b with
    | false =>
      have e : bad false (false :: rest) = bad false rest := by simp [bad]
      rw [e]
      constructor
      · intro h
        rw [List.sortedLE_cons]
        exact ⟨fun c _ => by cases c <;> decide, ih.mp h⟩
      · intro h
        rw [List.sortedLE_cons] at h
        exact ih.mpr h.2
    | true =>
      have e : bad false (true :: rest) = bad true rest := by simp [bad]
      rw [e, bad_true]
      constructor
      · intro h
        rw [List.sortedLE_cons]
        exact ⟨fun c hc => by simp [h c hc], all_true_sorted rest h⟩
      · intro h
        rw [List.sortedLE_cons] at h
        intro c hc
        have hle := h.1 c hc
        cases c with
        | false => exact absurd hle (by decide)
        | true => rfl

/-- The automaton accepts exactly the sorted lists. -/
theorem sorted_iff (x : List Bool) :
    List.SortedLE x ↔ accept (x.foldl trans (false, false)) = true := by
  rw [fold_eq]
  show List.SortedLE x ↔ !bad false x = true
  constructor
  · intro h
    cases hb : bad false x with
    | false => rfl
    | true => exact absurd ((bad_false_sorted x).mpr h) (by simp [hb])
  · intro h
    apply (bad_false_sorted x).mp
    cases hb : bad false x with
    | false => rfl
    | true => simp [hb] at h

end PvsNP.Units.tl_lang_sorted_p

/-- The sorted lists of booleans are in `P` (TM2). -/
theorem PvsNP.Units.tl_lang_sorted_p :
    ({x : List Bool | List.SortedLE x} : Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | List.SortedLE x} : Language Bool)
      = {x : List Bool | PvsNP.Units.tl_lang_sorted_p.accept
          (x.foldl PvsNP.Units.tl_lang_sorted_p.trans (false, false)) = true} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact PvsNP.Units.tl_lang_sorted_p.sorted_iff x
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p (Bool × Bool)
    PvsNP.Units.tl_lang_sorted_p.trans (false, false)
    PvsNP.Units.tl_lang_sorted_p.accept
