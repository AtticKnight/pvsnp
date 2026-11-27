import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-!
For any fixed word `w : List Bool`, the language of strings containing `w` as a contiguous factor
(`w <:+: x`) is recognized by a finite automaton on `Fin (w.length + 1)` tracking the longest
prefix of `w` that is a suffix of the input read so far (with `w.length` as an absorbing accepting
state). By `PvsNP.Units.m2_dfa_in_p`, this language lies in `PvsNP.P`.
-/

namespace PvsNP.Units.tl_lang_factor_all_p

/-- The longest prefix length `k ≤ w.length` such that `w.take k` is a suffix of `s`. -/
def maxPrefixSuffix (w s : List Bool) : Nat :=
  (List.range (w.length + 1)).foldl
    (fun best k => if decide (w.take k <:+ s) then max best k else best) 0

theorem maxPrefixSuffix_le (w s : List Bool) : maxPrefixSuffix w s ≤ w.length := by
  unfold maxPrefixSuffix
  have h : ∀ (l : List Nat) (init : Nat),
      init ≤ w.length → (∀ k ∈ l, k ≤ w.length) →
      (l.foldl (fun best k => if decide (w.take k <:+ s) then max best k else best) init) ≤
        w.length := by
    intro l
    induction l with
    | nil => intro init hi _; exact hi
    | cons a t ih =>
      intro init hi hl
      rw [List.foldl_cons]
      apply ih
      · split_ifs
        · exact Nat.max_le.mpr ⟨hi, hl a (by simp)⟩
        · exact hi
      · intro k hk
        exact hl k (by simp [hk])
  apply h
  · exact Nat.zero_le _
  · intro k hk
    rw [List.mem_range] at hk
    omega

theorem maxPrefixSuffix_isSuffix (w s : List Bool) :
    w.take (maxPrefixSuffix w s) <:+ s := by
  unfold maxPrefixSuffix
  have h : ∀ (l : List Nat) (init : Nat),
      w.take init <:+ s →
      w.take (l.foldl (fun best k => if decide (w.take k <:+ s) then max best k else best) init) <:+
        s := by
    intro l
    induction l with
    | nil => intro init hi; exact hi
    | cons a t ih =>
      intro init hi
      rw [List.foldl_cons]
      apply ih
      by_cases ha : w.take a <:+ s
      · simp only [ha, decide_true, ↓reduceIte]
        rcases Nat.le_total init a with hle | hle
        · rw [Nat.max_eq_right hle]; exact ha
        · rw [Nat.max_eq_left hle]; exact hi
      · simp [ha, hi]
  apply h
  simp

theorem le_maxPrefixSuffix (w s : List Bool) {k : Nat} (hk : k ≤ w.length)
    (hs : w.take k <:+ s) : k ≤ maxPrefixSuffix w s := by
  unfold maxPrefixSuffix
  have hmem : k ∈ List.range (w.length + 1) := List.mem_range.mpr (by omega)
  have hmono : ∀ (l : List Nat) (init : Nat),
      (k ∈ l ∨ k ≤ init) →
      k ≤ l.foldl (fun best m => if decide (w.take m <:+ s) then max best m else best) init := by
    intro l
    induction l with
    | nil =>
      intro init h
      rcases h with h | h
      · simp at h
      · exact h
    | cons a t ih =>
      intro init h
      rw [List.foldl_cons]
      apply ih
      rcases h with h | h
      · rw [List.mem_cons] at h
        rcases h with rfl | ht
        · right
          simp only [hs, decide_true, ↓reduceIte]
          exact Nat.le_max_right _ _
        · exact Or.inl ht
      · right
        by_cases ha : w.take a <:+ s
        · simp only [ha, decide_true, ↓reduceIte]
          exact Nat.le_trans h (Nat.le_max_left _ _)
        · simp [ha, h]
  exact hmono _ 0 (Or.inl hmem)

/-- Transition function on `Fin (w.length + 1)`. State `w.length` is absorbing. -/
def step (w : List Bool) (q : Fin (w.length + 1)) (b : Bool) : Fin (w.length + 1) :=
  if q.val = w.length then q
  else ⟨maxPrefixSuffix w (w.take q.val ++ [b]), Nat.lt_succ_of_le (maxPrefixSuffix_le w _)⟩

/-- Accepting state: the whole word `w` has been seen. -/
def acc (w : List Bool) (q : Fin (w.length + 1)) : Bool :=
  decide (q.val = w.length)

/-- The prefix of `w` currently matched at the end of the scanned input. -/
def pend (w : List Bool) (q : Fin (w.length + 1)) : List Bool :=
  w.take q.val

private theorem isSuffix_of_isSuffix_le {α : Type*} (u v s : List α)
    (hu : u <:+ s) (hv : v <:+ s) (hlen : u.length ≤ v.length) : u <:+ v := by
  rcases hu with ⟨pu, hpu⟩
  rcases hv with ⟨pv, hpv⟩
  have h : pu ++ u = pv ++ v := hpu.trans hpv.symm
  rw [List.append_eq_append_iff] at h
  rcases h with ⟨d, _, hd⟩ | ⟨d, hp, hd⟩
  · have : v.length ≤ u.length := by
      have := congrArg List.length hd
      simp only [List.length_append] at this
      omega
    have hd0 : d = [] := by
      have := congrArg List.length hd
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hd0
    simp at hd
    exact ⟨[], by simpa using hd⟩
  · exact ⟨d, hd.symm⟩

theorem step_iff (w : List Bool) (q : Fin (w.length + 1)) (b : Bool) (xs : List Bool) :
    w <:+: pend w q ++ (b :: xs) ↔ w <:+: pend w (step w q b) ++ xs := by
  by_cases hq : q.val = w.length
  · simp only [step, hq, ↓reduceIte, pend, List.take_length]
    constructor
    · intro _; exact ⟨[], xs, by simp⟩
    · intro _; exact ⟨[], b :: xs, by simp⟩
  · simp only [step, hq, ↓reduceIte, pend]
    set s := w.take q.val ++ [b]
    set k' := maxPrefixSuffix w s
    have hpend : w.take q.val ++ (b :: xs) = s ++ xs := by
      simp [s, List.append_assoc]
    rw [hpend]
    constructor
    · rintro ⟨p, t, hpt⟩
      have h1 : p ++ (w ++ t) = s ++ xs := by simpa [List.append_assoc] using hpt
      rw [List.append_eq_append_iff] at h1
      rcases h1 with ⟨d, hps, hwt⟩ | ⟨d, hsp, hxs⟩
      · rw [List.append_eq_append_iff] at hwt
        rcases hwt with ⟨v, hd, htv⟩ | ⟨v, hw, hxv⟩
        · have hslen : s.length ≤ w.length := by
            have hqlt : q.val < w.length := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp q.isLt) hq
            simp only [s, List.length_append, List.length_take, List.length_singleton]
            omega
          have hlen2 := congrArg List.length hps
          simp only [hd, List.length_append] at hlen2
          have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hv
          have hsw : w <:+ s := ⟨p, by simpa [hd] using hps.symm⟩
          have hwk : w.length ≤ k' := by
            apply le_maxPrefixSuffix w s (le_refl _)
            simpa using hsw
          have hkeq : k' = w.length := Nat.le_antisymm (maxPrefixSuffix_le w s) hwk
          exact ⟨[], xs, by simp [hkeq]⟩
        · have huv : w.take d.length = d := by
            rw [hw, List.take_left]
          have hdle : d.length ≤ w.length := by
            have := congrArg List.length hw
            simp only [List.length_append] at this
            omega
          have hdsuf : w.take d.length <:+ s := by
            rw [huv]
            exact ⟨p, hps.symm⟩
          have hdk : d.length ≤ k' := le_maxPrefixSuffix w s hdle hdsuf
          have hklen : (w.take k').length = k' :=
            List.length_take_of_le (maxPrefixSuffix_le w s)
          have hdv : d <:+ w.take k' := by
            apply isSuffix_of_isSuffix_le d (w.take k') s ⟨p, hps.symm⟩
              (maxPrefixSuffix_isSuffix w s)
            omega
          rcases hdv with ⟨pref, hpref⟩
          refine ⟨pref, t, ?_⟩
          calc pref ++ w ++ t
              = pref ++ (d ++ v) ++ t := by rw [hw]
            _ = (pref ++ d) ++ (v ++ t) := by simp [List.append_assoc]
            _ = w.take k' ++ xs := by rw [hpref, hxv]
      · refine ⟨w.take k' ++ d, t, ?_⟩
        calc (w.take k' ++ d) ++ w ++ t
            = w.take k' ++ (d ++ (w ++ t)) := by simp [List.append_assoc]
          _ = w.take k' ++ xs := by rw [← hxs]
    · rintro ⟨p, t, hpt⟩
      rcases maxPrefixSuffix_isSuffix w s with ⟨u, hu⟩
      refine ⟨u ++ p, t, ?_⟩
      calc (u ++ p) ++ w ++ t
          = u ++ (p ++ w ++ t) := by simp [List.append_assoc]
        _ = u ++ (w.take k' ++ xs) := by rw [hpt]
        _ = (u ++ w.take k') ++ xs := by simp [List.append_assoc]
        _ = s ++ xs := by rw [hu]

/-- Started in `q`, the automaton accepts `x` iff `w` is a factor of `pend w q ++ x`. -/
theorem run_iff (w x : List Bool) (q : Fin (w.length + 1)) :
    acc w (x.foldl (step w) q) = true ↔ w <:+: pend w q ++ x := by
  induction x generalizing q with
  | nil =>
    simp only [List.foldl_nil, List.append_nil, acc, pend]
    constructor
    · intro hq
      rw [of_decide_eq_true hq, List.take_length]
    · intro ⟨s, t, hst⟩
      have hlen := congrArg List.length hst
      simp only [List.length_append, List.length_take] at hlen
      have hqis := q.isLt
      exact decide_eq_true (by omega)
  | cons b xs ih =>
    rw [List.foldl_cons, ih, ← step_iff]

/-- The language of strings containing `w` as a factor equals the automaton's language. -/
theorem lang_eq (w : List Bool) :
    ({x : List Bool | w <:+: x} : Language Bool) =
      {x : List Bool | acc w (x.foldl (step w) 0) = true} := by
  ext x
  have h := run_iff w x 0
  simp only [pend, Fin.val_zero, List.take_zero, List.nil_append] at h
  exact h.symm

end PvsNP.Units.tl_lang_factor_all_p

/-- For every `w : List Bool`, the language of strings containing `w` as a factor is in `P`. -/
theorem PvsNP.Units.tl_lang_factor_all_p :
    ∀ w : List Bool, ({x : List Bool | w <:+: x} : Language Bool) ∈ PvsNP.P := by
  intro w
  rw [PvsNP.Units.tl_lang_factor_all_p.lang_eq w]
  exact PvsNP.Units.m2_dfa_in_p (Fin (w.length + 1))
    (PvsNP.Units.tl_lang_factor_all_p.step w) 0
    (PvsNP.Units.tl_lang_factor_all_p.acc w)
