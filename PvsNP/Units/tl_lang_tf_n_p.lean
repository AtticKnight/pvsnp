import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_inter
import PvsNP.Units.tl_lang_balanced_p

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_tf_n_p

def trans (p : Bool × Bool) (b : Bool) : Bool × Bool :=
  (p.1 || !b, p.2 || (p.1 && b))

def accept (p : Bool × Bool) : Bool := !p.2

def bad : Bool → List Bool → Bool
  | _, [] => false
  | s, b :: rest => (s && b) || bad (s || !b) rest

theorem fold_snd (x : List Bool) (s t : Bool) :
    (x.foldl trans (s, t)).2 = (t || bad s x) := by
  induction x generalizing s t with
  | nil => simp [bad]
  | cons b rest ih =>
    show (rest.foldl trans (s || !b, t || (s && b))).2 = (t || bad s (b :: rest))
    rw [ih]
    simp [bad, Bool.or_assoc]

theorem bad_true_iff (x : List Bool) :
    bad true x = false ↔ ∃ b : ℕ, x = List.replicate b false := by
  induction x with
  | nil =>
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
  | cons c rest ih =>
    cases c with
    | true =>
      constructor
      · intro h
        simp [bad] at h
      · rintro ⟨b, hb⟩
        cases b with
        | zero => cases hb
        | succ b' => simp [List.replicate_succ] at hb
    | false =>
      have e : bad true (false :: rest) = bad true rest := by simp [bad]
      rw [e]
      constructor
      · intro h
        obtain ⟨b, rfl⟩ := ih.mp h
        exact ⟨b + 1, rfl⟩
      · rintro ⟨b, hb⟩
        cases b with
        | zero => cases hb
        | succ b' =>
          simp only [List.replicate_succ, List.cons.injEq, true_and] at hb
          exact ih.mpr ⟨b', hb⟩

theorem bad_false_iff (x : List Bool) :
    bad false x = false ↔ ∃ a b : ℕ, x = List.replicate a true ++ List.replicate b false := by
  induction x with
  | nil =>
    exact ⟨fun _ => ⟨0, 0, rfl⟩, fun _ => rfl⟩
  | cons c rest ih =>
    cases c with
    | true =>
      have e : bad false (true :: rest) = bad false rest := by simp [bad]
      rw [e]
      constructor
      · intro h
        obtain ⟨a, b, rfl⟩ := ih.mp h
        exact ⟨a + 1, b, rfl⟩
      · rintro ⟨a, b, h⟩
        cases a with
        | zero =>
          cases b with
          | zero => cases h
          | succ b' => simp [List.replicate_succ] at h
        | succ a' =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          exact ih.mpr ⟨a', b, h⟩
    | false =>
      have e : bad false (false :: rest) = bad true rest := by simp [bad]
      rw [e, bad_true_iff]
      constructor
      · intro h
        obtain ⟨b, rfl⟩ := h
        exact ⟨0, b + 1, rfl⟩
      · rintro ⟨a, b, h⟩
        cases a with
        | zero =>
          cases b with
          | zero => cases h
          | succ b' =>
            simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons.injEq, true_and] at h
            exact ⟨b', h⟩
        | succ a' =>
          simp [List.replicate_succ] at h

theorem accept_iff (x : List Bool) :
    accept (x.foldl trans (false, false)) = true ↔
      ∃ a b : ℕ, x = List.replicate a true ++ List.replicate b false := by
  unfold accept
  rw [fold_snd]
  have h : (!(false || bad false x) = true) ↔ bad false x = false := by
    cases bad false x <;> simp
  exact h.trans (bad_false_iff x)

theorem count_rep_true (a b : ℕ) :
    (List.replicate a true ++ List.replicate b false).count true = a := by
  simp [List.count_append, List.count_replicate]

theorem count_rep_false (a b : ℕ) :
    (List.replicate a true ++ List.replicate b false).count false = b := by
  simp [List.count_append, List.count_replicate]

end PvsNP.Units.tl_lang_tf_n_p

theorem PvsNP.Units.tl_lang_tf_n_p :
    ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate n false} : Language Bool) ∈ PvsNP.P := by
  have hdfa :
      ({x : List Bool | PvsNP.Units.tl_lang_tf_n_p.accept
        (x.foldl PvsNP.Units.tl_lang_tf_n_p.trans (false, false)) = true} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_dfa_in_p (Bool × Bool)
      PvsNP.Units.tl_lang_tf_n_p.trans (false, false)
      PvsNP.Units.tl_lang_tf_n_p.accept
  have hinter := PvsNP.Units.m2_p_inter _ _ PvsNP.Units.tl_lang_balanced_p hdfa
  have heq :
      (({x : List Bool | x.count true = x.count false} : Language Bool) ∩
        ({x : List Bool | PvsNP.Units.tl_lang_tf_n_p.accept
          (x.foldl PvsNP.Units.tl_lang_tf_n_p.trans (false, false)) = true} : Language Bool)) =
      ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate n false} : Language Bool) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, PvsNP.Units.tl_lang_tf_n_p.accept_iff]
    constructor
    · rintro ⟨hcnt, a, b, hx⟩
      have ha : a = b := by
        rw [hx, PvsNP.Units.tl_lang_tf_n_p.count_rep_true,
          PvsNP.Units.tl_lang_tf_n_p.count_rep_false] at hcnt
        exact hcnt
      subst ha
      exact ⟨a, hx⟩
    · rintro ⟨n, rfl⟩
      refine ⟨?_, n, n, rfl⟩
      rw [PvsNP.Units.tl_lang_tf_n_p.count_rep_true,
        PvsNP.Units.tl_lang_tf_n_p.count_rep_false]
  rw [← heq]
  exact hinter
