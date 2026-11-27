import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_bool_combine_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_brackets_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem emp_false_run (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool))) (fun q => some q) false l =
      [false] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [fstRun, ih]

theorem cpt_isEmpty :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => x.isEmpty) :=
  fst_polyTime (fun x : List Bool => x) Computability.encodeBool (fun x : List Bool => x.isEmpty)
    (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
    (fun q => some q) true (fun l => by
      cases l with
      | nil => rfl
      | cons _ _ => simp [fstRun, emp_false_run, Computability.encodeBool])

theorem head_some_run (b : Bool) (l : List Bool) :
    fstRun (fun (q : Option Bool) (c : Bool) =>
      match q with | none => (some c, none) | some v => (some v, none))
      (fun q => some (q.getD false)) (some b) l = [b] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [fstRun, ih]

theorem cpt_headD :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) :=
  fst_polyTime (fun x : List Bool => x) Computability.encodeBool (fun x : List Bool => x.headD false)
    (fun (q : Option Bool) (c : Bool) =>
      match q with | none => (some c, none) | some v => (some v, none))
    (fun q => some (q.getD false)) none (fun l => by
      cases l with
      | nil => rfl
      | cons _ _ => simp [fstRun, head_some_run, Computability.encodeBool])

theorem cpt_cons_true :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => true :: x) := by
  have h := cpt_comp (cpt_pair (constList_polyTime [true]) cpt_id) cpt_append
  have heq : (fun x : List Bool => [true] ++ x) = (fun x : List Bool => true :: x) := by
    funext _; rfl
  rw [← heq]
  exact h

def stepBrk (s : List Bool) : List Bool :=
  let ok := (unpairB s).1
  let stk := (unpairB (unpairB s).2).1
  let rem := (unpairB (unpairB s).2).2
  let okNext :=
    if rem.isEmpty = true then ok
    else if rem.headD false = true then ok
    else if stk.isEmpty = true then [] else ok
  let stkNext :=
    if rem.isEmpty = true then stk
    else if rem.headD false = true then true :: stk
    else stk.tail
  pairB okNext (pairB stkNext rem.tail)

theorem cpt_stepBrk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString stepBrk := by
  have hOk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hSnd : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hStk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).1) hSnd cpt_unpairB1
  have hRem : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).2) hSnd cpt_unpairB2
  have hcRemEmp := cpt_comp hRem cpt_isEmpty
  have hcRemHd := cpt_comp hRem cpt_headD
  have hcStkEmp := cpt_comp hStk cpt_isEmpty
  have hOk3 := PvsNP.Units.m2_ite_polytime _ _ _ hcStkEmp (constList_polyTime []) hOk
  have hOk2 := PvsNP.Units.m2_ite_polytime _ _ _ hcRemHd hOk hOk3
  have hOkNext := PvsNP.Units.m2_ite_polytime _ _ _ hcRemEmp hOk hOk2
  have hStk2 := PvsNP.Units.m2_ite_polytime _ _ _ hcRemHd
    (cpt_comp hStk cpt_cons_true) (cpt_comp hStk cpt_tail)
  have hStkNext := PvsNP.Units.m2_ite_polytime _ _ _ hcRemEmp hStk hStk2
  exact cpt_pairB2 hOkNext (cpt_pairB2 hStkNext (cpt_comp hRem cpt_tail))

theorem stepBrk_length (s : List Bool) : (stepBrk s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  dsimp only [stepBrk]
  cases hr : (unpairB (unpairB s).2).2 with
  | nil =>
    have hrl : (unpairB (unpairB s).2).2.length = 0 := by rw [hr]; rfl
    rw [hrl] at h2
    simp only [List.isEmpty_nil, ite_true, List.tail_nil, pairB_length, List.length_nil] at h1 h2 ⊢
    omega
  | cons b rt =>
    have hrl : (unpairB (unpairB s).2).2.length = rt.length + 1 := by rw [hr, List.length_cons]
    rw [hrl] at h2
    cases b
    · cases hs : (unpairB (unpairB s).2).1 with
      | nil =>
        have hsl2 : (unpairB (unpairB s).2).1.length = 0 := by rw [hs]; rfl
        rw [hsl2] at h2
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
          List.isEmpty_nil, ite_true, List.tail_nil, List.tail_cons,
          pairB_length, List.length_nil] at h1 h2 ⊢
        omega
      | cons sb st =>
        have hsl2 : (unpairB (unpairB s).2).1.length = st.length + 1 := by rw [hs, List.length_cons]
        rw [hsl2] at h2
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
          List.tail_cons, pairB_length] at h1 h2 ⊢
        omega
    · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
        ite_true, List.tail_cons, pairB_length, List.length_cons] at h1 h2 ⊢
      omega

def checkEndState (s : List Bool) : Bool :=
  !(unpairB s).1.isEmpty && (unpairB (unpairB s).2).1.isEmpty

def decBrk (x : List Bool) : Bool :=
  checkEndState (stepBrk^[x.length] (pairB [true] (pairB [] x)))

theorem cpt_decBrk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decBrk := by
  have hIter := PvsNP.Units.m2_iterate_polytime stepBrk 5 cpt_stepBrk stepBrk_length
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [true] (pairB [] x)) :=
    cpt_pairB2 (constList_polyTime [true]) (cpt_pairB2 (constList_polyTime []) cpt_id)
  have hOut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => stepBrk^[x.length] (pairB [true] (pairB [] x))) :=
    cpt_comp (cpt_pair hInit cpt_id) hIter
  have h1 := cpt_comp (g := fun s : List Bool => (unpairB s).1) hOut cpt_unpairB1
  have hOkEmp := cpt_comp h1 cpt_isEmpty
  have h2 := cpt_comp (g := fun s : List Bool => (unpairB s).2) hOut cpt_unpairB2
  have h3 := cpt_comp (g := fun s : List Bool => (unpairB s).1) h2 cpt_unpairB1
  have hStkEmp := cpt_comp h3 cpt_isEmpty
  exact PvsNP.Units.m2_bool_combine_polytime (fun a b => !a && b) _ _ hOkEmp hStkEmp

theorem stepBrk_spec (rem : List Bool) (ok : Bool) (k : ℕ) :
    checkEndState (stepBrk^[rem.length] (pairB (if ok then [true] else []) (pairB (List.replicate k true) rem))) = true ↔
      (ok = true ∧ k + rem.count true = rem.count false ∧
        ∀ y : List Bool, y <+: rem → y.count false ≤ k + y.count true) := by
  induction rem generalizing ok k with
  | nil =>
    simp only [checkEndState, List.length_nil, Function.iterate_zero, id_eq, unpairB_pairB,
      Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.isEmpty_iff,
      List.replicate_eq_nil_iff, List.count_nil, Nat.add_zero]
    constructor
    · rintro ⟨hok, rfl⟩
      refine ⟨?_, rfl, ?_⟩
      · cases ok <;> simp at hok ⊢
      · intro y hy
        rw [List.prefix_nil] at hy
        subst hy
        simp
    · rintro ⟨rfl, rfl, -⟩
      simp
  | cons b tl ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases b
    · rcases k with _ | k'
      · have hone : stepBrk (pairB (if ok then [true] else []) (pairB (List.replicate 0 true) (false :: tl))) =
            pairB (if false then [true] else []) (pairB (List.replicate 0 true) tl) := by
          simp [stepBrk, unpairB_pairB]
        rw [hone, ih false 0]
        constructor
        · rintro ⟨hfalse, -⟩
          exact Bool.noConfusion hfalse
        · rintro ⟨-, -, hpref⟩
          have hbad := hpref [false] ⟨tl, rfl⟩
          simp at hbad
      · have hone : stepBrk (pairB (if ok then [true] else []) (pairB (List.replicate (k' + 1) true) (false :: tl))) =
            pairB (if ok then [true] else []) (pairB (List.replicate k' true) tl) := by
          simp [stepBrk, unpairB_pairB, List.replicate_succ]
        rw [hone, ih ok k']
        have hcf : (false :: tl).count false = tl.count false + 1 := List.count_cons_self
        have hct : (false :: tl).count true = tl.count true := by simp
        rw [hcf, hct]
        constructor
        · rintro ⟨hok, hcnt, hpref⟩
          refine ⟨hok, by omega, fun y hy => ?_⟩
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
        · rintro ⟨hok, hcnt, hpref⟩
          refine ⟨hok, by omega, fun yt hyt => ?_⟩
          rcases hyt with ⟨z, rfl⟩
          have hb := hpref (false :: yt) ⟨z, rfl⟩
          have hyf : (false :: yt).count false = yt.count false + 1 := List.count_cons_self
          have hytc : (false :: yt).count true = yt.count true := by simp
          rw [hyf, hytc] at hb
          omega
    · have hone : stepBrk (pairB (if ok then [true] else []) (pairB (List.replicate k true) (true :: tl))) =
          pairB (if ok then [true] else []) (pairB (List.replicate (k + 1) true) tl) := by
        simp [stepBrk, unpairB_pairB, List.replicate_succ]
      rw [hone, ih ok (k + 1)]
      have hct : (true :: tl).count true = tl.count true + 1 := List.count_cons_self
      have hcf : (true :: tl).count false = tl.count false := by simp
      rw [hct, hcf]
      constructor
      · rintro ⟨hok, hcnt, hpref⟩
        refine ⟨hok, by omega, fun y hy => ?_⟩
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
      · rintro ⟨hok, hcnt, hpref⟩
        refine ⟨hok, by omega, fun yt hyt => ?_⟩
        rcases hyt with ⟨z, rfl⟩
        have hb := hpref (true :: yt) ⟨z, rfl⟩
        have hytc : (true :: yt).count true = yt.count true + 1 := List.count_cons_self
        have hyf : (true :: yt).count false = yt.count false := by simp
        rw [hytc, hyf] at hb
        omega

end PvsNP.Units.tl_lang_brackets_p

theorem PvsNP.Units.tl_lang_brackets_p :
    ({x : List Bool | x.count true = x.count false ∧ ∀ y : List Bool, y <+: x → y.count false ≤ y.count true} : Language Bool) ∈ PvsNP.P := by
  refine ⟨PvsNP.Units.tl_lang_brackets_p.decBrk, PvsNP.Units.tl_lang_brackets_p.cpt_decBrk, fun x => ?_⟩
  have h := PvsNP.Units.tl_lang_brackets_p.stepBrk_spec x true 0
  simp only [ite_true, List.replicate_zero, Nat.zero_add, true_and] at h
  exact h.symm
