import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime

namespace PvsNP.Units.tr_rel_power_of

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem takeWhile_len_add_dropWhile_len (p : Bool → Bool) (s : List Bool) :
    (s.takeWhile p).length + (s.dropWhile p).length = s.length := by
  induction s with
  | nil => simp
  | cons b t ih =>
    cases h : p b with
    | false => simp [h]
    | true => simp [h]; omega

theorem unpairB_len_le (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  simp only [unpairB, List.length_take, List.length_drop]
  have hsplit := takeWhile_len_add_dropWhile_len id s
  have htail : (s.dropWhile id).tail.length ≤ (s.dropWhile id).length := by
    cases s.dropWhile id <;> simp
  omega

theorem encodePair_eq : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨x, y⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

theorem cpt_ifBool (c : List Bool → Bool) (a b : List Bool → List Bool)
    (hc : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool c)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => if c s = true then a s else b s) := by
  have h := cpt_sel (f := fun s => if c s = true then [true] else []) (a := b) (b := a)
    (cpt_bitFlag hc) hb ha
  have hfun : (fun s : List Bool => sel (if c s = true then [true] else []) (b s) (a s)) =
      (fun s : List Bool => if c s = true then a s else b s) := by
    funext s
    cases c s <;> simp [sel]
  rw [hfun] at h
  exact h

theorem cpt_eq_pair (f1 f2 : List Bool → List Bool)
    (h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f1)
    (h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f2) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => decide (f1 s = f2 s)) := by
  have heq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun q : List Bool × List Bool => decide (q.1 = q.2)) := by
    rw [← encodePair_eq]
    exact PvsNP.Units.m2_eq_polytime
  exact cpt_comp (f := fun s => (f1 s, f2 s)) (g := fun q => decide (q.1 = q.2)) (cpt_pair h1 h2) heq

theorem tail_iter_eq_drop (k : ℕ) (l : List Bool) : List.tail^[k] l = l.drop k := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp

def powStep (s : List Bool) : List Bool :=
  let a := (unpairB s).1
  let b := (unpairB s).2
  let d := List.tail^[a.length] b
  if decide (a ++ d = b) = true then pairB a d else s

theorem powStep_len_le (s : List Bool) : (powStep s).length ≤ s.length + 1 := by
  have h0 := unpairB_len_le s
  unfold powStep
  dsimp only
  rw [tail_iter_eq_drop]
  split_ifs
  · simp only [pairB_length, List.length_drop]
    omega
  · omega

theorem cpt_powStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) powStep := by
  have ha := cpt_unpairB1
  have hb := cpt_unpairB2
  have htailLen : ∀ l : List Bool, l.tail.length ≤ l.length := fun l => by cases l <;> simp
  have hd := cpt_iterLen cpt_tail htailLen ha hb
  have hpref := cpt_eq_pair _ _ (cpt_app2 ha hd) hb
  exact cpt_ifBool _ _ _ hpref (cpt_pairB2 ha hd) cpt_id

theorem powStep_iter_nil (n : ℕ) (b : List Bool) :
    powStep^[n] (pairB [] b) = pairB [] b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h1 : powStep (pairB [] b) = pairB [] b := by
      unfold powStep
      simp [unpairB_pairB]
    rw [h1, ih]

theorem powStep_iter_ne_nil (n : ℕ) (a : List Bool) (ha : a ≠ []) :
    ∀ b : List Bool, b.length ≤ n →
      ((unpairB (powStep^[n] (pairB a b))).2 = [] ↔
        ∃ k : ℕ, b = (List.replicate k a).flatten) := by
  induction n with
  | zero =>
    intro b hb
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb0
    simp only [Function.iterate_zero, id_eq, unpairB_pairB, true_iff]
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro b hb
    by_cases hpref : a ++ b.drop a.length = b
    · rw [Function.iterate_succ_apply]
      have hstep : powStep (pairB a b) = pairB a (b.drop a.length) := by
        unfold powStep
        simp only [unpairB_pairB, tail_iter_eq_drop, hpref, decide_true, ↓reduceIte]
      rw [hstep]
      have hapos : 0 < a.length := List.length_pos_of_ne_nil ha
      have hblen : a.length ≤ b.length := by
        have := congrArg List.length hpref
        simp only [List.length_append] at this
        omega
      have hdropLen : (b.drop a.length).length ≤ n := by
        simp only [List.length_drop]
        omega
      rw [ih (b.drop a.length) hdropLen]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        rw [List.replicate_succ, List.flatten_cons, ← hk, hpref]
      · rintro ⟨k, hk⟩
        cases k with
        | zero =>
          simp only [List.replicate_zero, List.flatten_nil] at hk
          subst hk
          simp at hblen
          exact absurd hblen (by omega)
        | succ k' =>
          refine ⟨k', ?_⟩
          rw [List.replicate_succ, List.flatten_cons] at hk
          rw [hk, List.drop_left]
    · have hfix : powStep (pairB a b) = pairB a b := by
        unfold powStep
        simp only [unpairB_pairB, tail_iter_eq_drop, hpref, decide_false,
          Bool.false_eq_true, ↓reduceIte]
      have hiter : ∀ t : ℕ, powStep^[t] (pairB a b) = pairB a b := by
        intro t
        induction t with
        | zero => rfl
        | succ t iht => rw [Function.iterate_succ_apply, hfix, iht]
      rw [hiter (n + 1), unpairB_pairB]
      constructor
      · intro hb0
        subst hb0
        exact ⟨0, rfl⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simpa using hk
        | succ k' =>
          exfalso
          apply hpref
          rw [List.replicate_succ, List.flatten_cons] at hk
          rw [hk, List.drop_left]

def powOfStr (s : List Bool) : Bool :=
  decide ((unpairB (powStep^[(unpairB s).2.length] s)).2 = [])

def powOfFun (p : List Bool × List Bool) : Bool :=
  powOfStr (pairB p.1 p.2)

theorem cpt_powOfFun :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer powOfFun := by
  have hiter := cpt_iterGrow cpt_powStep 1 powStep_len_le cpt_unpairB2 cpt_id
  have hstr : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool powOfStr :=
    cpt_eq_pair _ _ (cpt_unpairB2_1 hiter) (cpt_const [])
  have hpair : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool powOfFun :=
    cpt_comp (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := powOfStr) cpt_pairB hstr
  rw [encodePair_eq]
  exact hpair

theorem power_of_aux :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
        ∀ p : List Bool × List Bool,
          (∃ k : ℕ, p.2 = (List.replicate k p.1).flatten) ↔ f p = true := by
  refine ⟨powOfFun, cpt_powOfFun, fun ⟨a, b⟩ => ?_⟩
  unfold powOfFun powOfStr
  simp only [unpairB_pairB, decide_eq_true_eq]
  by_cases ha : a = []
  · subst ha
    rw [powStep_iter_nil, unpairB_pairB]
    constructor
    · rintro ⟨k, hk⟩
      have hflat : (List.replicate k ([] : List Bool)).flatten = [] := by
        simp
      rw [hk, hflat]
    · intro hb0
      exact ⟨0, hb0⟩
  · exact (powStep_iter_ne_nil b.length a ha b (le_refl _)).symm

end PvsNP.Units.tr_rel_power_of

/-- Whether one binary string is a power of another is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_power_of :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
        ∀ p : List Bool × List Bool,
          (∃ k : ℕ, p.2 = (List.replicate k p.1).flatten) ↔ f p = true :=
  PvsNP.Units.tr_rel_power_of.power_of_aux
