import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.tl_lang_brackets_p
import PvsNP.Units.m2_p_inter

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_dominated_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tl_lang_brackets_p

/-
Closes tl_lang_dominated_p by reusing the counter machine of the settled unit
tl_lang_brackets_p: one pass pushes a mark on each true and pops one on each
false, flagging failure on a pop from an empty stack. The brackets decider
additionally demands an empty stack at the end (balanced words); here only the
flag is read, which is exactly the "every prefix holds no more falses than
trues" condition.
-/

/-- The dominated decider: the brackets machine's ok-flag, stack ignored. -/
def decDom (x : List Bool) : Bool :=
  !((unpairB (stepBrk^[x.length] (pairB [true] (pairB [] x)))).1.isEmpty)

/-- The brackets counter run flags failure exactly when some prefix of the
remaining input already holds more falses than trues (offset by `k`). -/
theorem stepBrk_dom_spec (rem : List Bool) (ok : Bool) (k : ℕ) :
    !((unpairB (stepBrk^[rem.length]
      (pairB (if ok then [true] else []) (pairB (List.replicate k true) rem)))).1.isEmpty) = true ↔
      (ok = true ∧ ∀ y : List Bool, y <+: rem → y.count false ≤ k + y.count true) := by
  induction rem generalizing ok k with
  | nil =>
    simp only [List.length_nil, Function.iterate_zero, id_eq, unpairB_pairB,
      Bool.not_eq_true', List.isEmpty_eq_false_iff, List.isEmpty_iff, List.count_nil,
      Nat.zero_add]
    constructor
    · intro hok
      refine ⟨?_, ?_⟩
      · cases ok <;> simp at hok ⊢
      · intro y hy
        rw [List.prefix_nil] at hy
        subst hy
        simp
    · rintro ⟨rfl, -⟩
      simp
  | cons b tl ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases b
    · rcases k with _ | k'
      · have hone : stepBrk (pairB (if ok then [true] else [])
            (pairB (List.replicate 0 true) (false :: tl))) =
            pairB (if false then [true] else []) (pairB (List.replicate 0 true) tl) := by
          simp [stepBrk, unpairB_pairB]
        rw [hone, ih false 0]
        constructor
        · rintro ⟨hfalse, -⟩
          exact Bool.noConfusion hfalse
        · rintro ⟨-, hpref⟩
          have hbad := hpref [false] ⟨tl, rfl⟩
          simp at hbad
      · have hone : stepBrk (pairB (if ok then [true] else [])
            (pairB (List.replicate (k' + 1) true) (false :: tl))) =
            pairB (if ok then [true] else []) (pairB (List.replicate k' true) tl) := by
          simp [stepBrk, unpairB_pairB, List.replicate_succ]
        rw [hone, ih ok k']
        constructor
        · rintro ⟨hok, hpref⟩
          refine ⟨hok, fun y hy => ?_⟩
          rcases hy with ⟨z, hz⟩
          cases y with
          | nil => simp
          | cons yb yt =>
            injection hz with hyb hyz
            subst hyb
            have hyt : yt <+: tl := ⟨z, hyz⟩
            have hb := hpref yt hyt
            have hyf : (false :: yt).count false = yt.count false + 1 := List.count_cons_self
            have hytc : (false :: yt).count true = yt.count true := by simp
            rw [hyf, hytc]
            omega
        · rintro ⟨hok, hpref⟩
          refine ⟨hok, fun yt hyt => ?_⟩
          rcases hyt with ⟨z, rfl⟩
          have hb := hpref (false :: yt) ⟨z, rfl⟩
          have hyf : (false :: yt).count false = yt.count false + 1 := List.count_cons_self
          have hytc : (false :: yt).count true = yt.count true := by simp
          rw [hyf, hytc] at hb
          omega
    · have hone : stepBrk (pairB (if ok then [true] else [])
          (pairB (List.replicate k true) (true :: tl))) =
          pairB (if ok then [true] else []) (pairB (List.replicate (k + 1) true) tl) := by
        simp [stepBrk, unpairB_pairB, List.replicate_succ]
      rw [hone, ih ok (k + 1)]
      constructor
      · rintro ⟨hok, hpref⟩
        refine ⟨hok, fun y hy => ?_⟩
        rcases hy with ⟨z, hz⟩
        cases y with
        | nil => simp
        | cons yb yt =>
          injection hz with hyb hyz
          subst hyb
          have hyt : yt <+: tl := ⟨z, hyz⟩
          have hb := hpref yt hyt
          have hytc : (true :: yt).count true = yt.count true + 1 := List.count_cons_self
          have hyf : (true :: yt).count false = yt.count false := by simp
          rw [hytc, hyf]
          omega
      · rintro ⟨hok, hpref⟩
        refine ⟨hok, fun yt hyt => ?_⟩
        rcases hyt with ⟨z, rfl⟩
        have hb := hpref (true :: yt) ⟨z, rfl⟩
        have hytc : (true :: yt).count true = yt.count true + 1 := List.count_cons_self
        have hyf : (true :: yt).count false = yt.count false := by simp
        rw [hytc, hyf] at hb
        omega

/-- The dominated decider runs in polynomial time: the iterated brackets
step, then the ok-flag test, negated. -/
theorem cpt_decDom :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decDom := by
  have hIter := PvsNP.Units.m2_iterate_polytime stepBrk 5 cpt_stepBrk stepBrk_length
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [true] (pairB [] x)) :=
    cpt_pairB2 (constList_polyTime [true]) (cpt_pairB2 (constList_polyTime []) cpt_id)
  have hOut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => stepBrk^[x.length] (pairB [true] (pairB [] x))) :=
    cpt_comp (cpt_pair hInit cpt_id) hIter
  have h1 := cpt_comp (g := fun s : List Bool => (unpairB s).1) hOut cpt_unpairB1
  have hOkEmp := cpt_comp h1 cpt_isEmpty
  exact PvsNP.Units.m2_p_inter.polyTimeComputable_not hOkEmp

end PvsNP.Units.tl_lang_dominated_p

/-- The strings every prefix of which holds no more falses than trues are in P (TM2). -/
theorem PvsNP.Units.tl_lang_dominated_p :
    ({x : List Bool | ∀ y : List Bool, y <+: x → y.count false ≤ y.count true} : Language Bool) ∈ PvsNP.P := by
  refine ⟨PvsNP.Units.tl_lang_dominated_p.decDom, PvsNP.Units.tl_lang_dominated_p.cpt_decDom, fun x => ?_⟩
  have h := PvsNP.Units.tl_lang_dominated_p.stepBrk_dom_spec x true 0
  simp only [ite_true, List.replicate_zero, Nat.zero_add, true_and] at h
  exact h.symm
