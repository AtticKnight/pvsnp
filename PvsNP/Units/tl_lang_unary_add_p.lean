import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_const_polytime

namespace PvsNP.Units.tl_lang_unary_add_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Run a three-state transducer over the input. -/
def run (δ : Fin 3 → Bool → Fin 3 × Option Bool) : Fin 3 → List Bool → List Bool
  | _, [] => []
  | q, b :: xs => (δ q b).2.toList ++ run δ (δ q b).1 xs

theorem cpt_run (δ : Fin 3 → Bool → Fin 3 × Option Bool) (q₀ : Fin 3) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (run δ q₀) :=
  PvsNP.Units.m2_transducer_polytime (Fin 3) δ (fun _ => none) (run δ)
    (fun q => by simp [run]) (fun q b x => rfl) q₀

/-- State = number of falses seen so far, capped at 2. -/
def nxt : Fin 3 → Bool → Fin 3
  | q, true => q
  | ⟨0, _⟩, false => 1
  | _, false => 2

/-- Emits a `true` for each `true` before the second `false`. -/
def δA (q : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  (nxt q b, if b && decide (q.val < 2) then some true else none)

/-- Emits a `true` for each `true` after the second `false`. -/
def δB (q : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  (nxt q b, if b && decide (q.val = 2) then some true else none)

/-- Emits a `true` for each `false`. -/
def δC (q : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  (nxt q b, if b then none else some true)

theorem cpt_eq_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => decide (f x = g x)) := by
  have hp : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun x : List Bool => (f x, g x)) := cpt_pair hf hg
  exact cpt_comp hp PvsNP.Units.m2_eq_polytime

def shapeOk (x : List Bool) : Bool := decide (run δC 0 x = [true, true])
def sumOk (x : List Bool) : Bool := decide (run δA 0 x = run δB 0 x)
def dec (x : List Bool) : Bool := shapeOk x && sumOk x

theorem cpt_dec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer dec := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer shapeOk :=
    cpt_eq_fun (run δC 0) (fun _ => [true, true]) (cpt_run δC 0)
      (PvsNP.Units.m2_const_polytime [true, true])
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer sumOk :=
    cpt_eq_fun (run δA 0) (run δB 0) (cpt_run δA 0) (cpt_run δB 0)
  exact PvsNP.Units.m2_bool_combine_polytime and shapeOk sumOk h1 h2

theorem run_rep_some (δ : Fin 3 → Bool → Fin 3 × Option Bool) (q : Fin 3) (t : Bool)
    (h : δ q true = (q, some t)) (a : ℕ) (y : List Bool) :
    run δ q (List.replicate a true ++ y) = List.replicate a t ++ run δ q y := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, run, h]
    simp [ih, List.replicate_succ]

theorem run_rep_none (δ : Fin 3 → Bool → Fin 3 × Option Bool) (q : Fin 3)
    (h : δ q true = (q, none)) (a : ℕ) (y : List Bool) :
    run δ q (List.replicate a true ++ y) = run δ q y := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, run, h]
    simp [ih]

theorem runC_eq (q : Fin 3) (x : List Bool) :
    run δC q x = List.replicate (x.count false) true := by
  induction x generalizing q with
  | nil => simp [run]
  | cons b xs ih =>
    cases b
    · simp [run, δC, ih, List.replicate_succ]
    · simp [run, δC, ih]

theorem count_zero (x : List Bool) (h : x.count false = 0) :
    x = List.replicate x.length true := by
  rw [List.eq_replicate_iff]
  refine ⟨rfl, fun b hb => ?_⟩
  cases b
  · exact absurd hb (List.count_eq_zero.mp h)
  · rfl

theorem count_succ (k : ℕ) (x : List Bool) (h : x.count false = k + 1) :
    ∃ a y, x = List.replicate a true ++ false :: y ∧ y.count false = k := by
  induction x with
  | nil => simp at h
  | cons b xs ih =>
    cases b
    · refine ⟨0, xs, by simp, ?_⟩
      simp at h
      exact h
    · have h' : xs.count false = k + 1 := by simpa [List.count_cons] using h
      obtain ⟨a, y, hx, hy⟩ := ih h'
      exact ⟨a + 1, y, by simp [hx, List.replicate_succ], hy⟩

theorem nf (a b c : ℕ) :
    List.replicate a true ++ false :: List.replicate b true ++ false :: List.replicate c true =
      List.replicate a true ++ (false :: (List.replicate b true ++
        (false :: (List.replicate c true ++ [])))) := by
  simp

theorem runA_val (a b c : ℕ) :
    run δA 0 (List.replicate a true ++ (false :: (List.replicate b true ++
        (false :: (List.replicate c true ++ []))))) = List.replicate (a + b) true := by
  rw [run_rep_some δA 0 true rfl, run, show δA 0 false = (1, none) from rfl,
    run_rep_some δA 1 true rfl, run, show δA 1 false = (2, none) from rfl,
    run_rep_none δA 2 rfl]
  simp [run]

theorem runB_val (a b c : ℕ) :
    run δB 0 (List.replicate a true ++ (false :: (List.replicate b true ++
        (false :: (List.replicate c true ++ []))))) = List.replicate c true := by
  rw [run_rep_none δB 0 rfl, run, show δB 0 false = (1, none) from rfl,
    run_rep_none δB 1 rfl, run, show δB 1 false = (2, none) from rfl,
    run_rep_some δB 2 true rfl]
  simp [run]

theorem dec_iff (x : List Bool) :
    dec x = true ↔ ∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++
      false :: List.replicate (a + b) true := by
  constructor
  · intro hdec
    simp only [dec, shapeOk, sumOk, Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨hs, hsum⟩ := hdec
    rw [runC_eq] at hs
    have hc : x.count false = 2 := by
      have := congrArg List.length hs
      simpa using this
    obtain ⟨a, y, hx, hy⟩ := count_succ 1 x hc
    obtain ⟨b, z, hy', hz⟩ := count_succ 0 y hy
    have hz' := count_zero z hz
    set c := z.length
    have hxn : x = List.replicate a true ++ (false :: (List.replicate b true ++
        (false :: (List.replicate c true ++ [])))) := by
      rw [hx, hy', ← hz']; simp
    rw [hxn, runA_val, runB_val] at hsum
    have hlen := congrArg List.length hsum
    simp at hlen
    refine ⟨a, b, ?_⟩
    rw [hxn, nf, ← hlen]
  · rintro ⟨a, b, hx⟩
    rw [nf] at hx
    simp only [dec, shapeOk, sumOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rw [runC_eq, hx]
      simp [List.count_replicate]
    · rw [hx, runA_val, runB_val]

end PvsNP.Units.tl_lang_unary_add_p

open PvsNP.Units.tl_lang_unary_add_p in
theorem PvsNP.Units.tl_lang_unary_add_p :
    ({x : List Bool | ∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++
      false :: List.replicate (a + b) true} : Language Bool) ∈ PvsNP.P :=
  ⟨dec, cpt_dec, fun x => by
    change (∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++
      false :: List.replicate (a + b) true) ↔ dec x = true
    exact (dec_iff x).symm⟩
