import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

namespace PvsNP.Units.tl_lang_first_eq_last_p

/-- DFA transition: remember the first bit seen and the most recent bit. -/
def felStep (q : Option Bool × Option Bool) (b : Bool) : Option Bool × Option Bool :=
  (q.1.or (some b), some b)

theorem foldl_fst (x : List Bool) (q : Option Bool × Option Bool) :
    (x.foldl felStep q).1 = q.1.or x.head? := by
  induction x generalizing q with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    simp only [felStep, List.head?_cons]
    cases q.1 <;> simp

theorem foldl_snd (x : List Bool) (q : Option Bool × Option Bool) :
    (x.foldl felStep q).2 = x.getLast?.or q.2 := by
  induction x generalizing q with
  | nil => simp
  | cons b xs ih =>
    cases xs with
    | nil => simp [felStep]
    | cons c xs' =>
      rw [List.foldl_cons, ih, List.getLast?_cons_cons]
      simp only [felStep]
      cases h : (c :: xs').getLast? with
      | none => simp at h
      | some v => simp

end PvsNP.Units.tl_lang_first_eq_last_p

theorem PvsNP.Units.tl_lang_first_eq_last_p :
    ({x : List Bool | x.head? = x.getLast?} : Language Bool) ∈ PvsNP.P := by
  have h : ({x : List Bool |
        (fun q => q.1 == q.2) (x.foldl PvsNP.Units.tl_lang_first_eq_last_p.felStep (none, none)) = true} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_dfa_in_p (Option Bool × Option Bool)
      PvsNP.Units.tl_lang_first_eq_last_p.felStep (none, none) (fun q => q.1 == q.2)
  have hset : ({x : List Bool | x.head? = x.getLast?} : Language Bool)
      = {x : List Bool |
          ((x.foldl PvsNP.Units.tl_lang_first_eq_last_p.felStep (none, none)).1
            == (x.foldl PvsNP.Units.tl_lang_first_eq_last_p.felStep (none, none)).2) = true} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hd
      rw [beq_iff_eq]
      rw [PvsNP.Units.tl_lang_first_eq_last_p.foldl_fst,
        PvsNP.Units.tl_lang_first_eq_last_p.foldl_snd]
      simpa using hd
    · intro hb
      rw [beq_iff_eq] at hb
      rw [PvsNP.Units.tl_lang_first_eq_last_p.foldl_fst,
        PvsNP.Units.tl_lang_first_eq_last_p.foldl_snd] at hb
      simpa using hb
  rw [hset]
  exact h
