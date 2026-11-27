import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_x_balanced_karp_sorted

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def truesUnary (x : List Bool) : List Bool :=
  x.filterMap (fun b : Bool => if b then some true else none)

def falsesUnary (x : List Bool) : List Bool :=
  x.filterMap (fun b : Bool => if b then none else some true)

theorem cpt_truesUnary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString truesUnary :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) (fun _ => rfl)

theorem cpt_falsesUnary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString falsesUnary :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then none else some true) (fun _ => rfl)

theorem truesUnary_eq_replicate (x : List Bool) :
    truesUnary x = List.replicate (x.count true) true := by
  induction x with
  | nil => rfl
  | cons b l ih =>
    cases b
    · change truesUnary l = List.replicate ((false :: l).count true) true
      simp [ih]
    · change true :: truesUnary l = List.replicate ((true :: l).count true) true
      rw [ih, List.count_cons_self, List.replicate_succ]

theorem falsesUnary_eq_replicate (x : List Bool) :
    falsesUnary x = List.replicate (x.count false) true := by
  induction x with
  | nil => rfl
  | cons b l ih =>
    cases b
    · change true :: falsesUnary l = List.replicate ((false :: l).count false) true
      rw [ih, List.count_cons_self, List.replicate_succ]
    · change falsesUnary l = List.replicate ((true :: l).count false) true
      simp [ih]

theorem cpt_balDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (truesUnary x = falsesUnary x)) := by
  have hp : ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodePair
      (fun x : List Bool => (truesUnary x, falsesUnary x)) :=
    cpt_pair cpt_truesUnary cpt_falsesUnary
  exact cpt_comp hp PvsNP.Units.m2_eq_polytime

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | b :: tl => .push () (fun _ => b) (pushList tl)

def chooseTM (y z : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop () (fun _ o => o.getD false)
      (.branch id
        (.load (fun _ => false) (pushList y.reverse))
        (pushList z.reverse))

lemma stepAux_pushList (inst : DecidableEq Unit) (r acc : List Bool) :
    @TM2.stepAux Unit (fun _ => Bool) Unit Bool inst (pushList r) false (fun _ : Unit => acc) =
      ⟨none, false, fun _ => r.reverseAux acc⟩ := by
  induction r generalizing acc with
  | nil => rfl
  | cons b tl ih =>
      simp only [pushList, TM2.stepAux, List.reverseAux_cons]
      have hupd : @Function.update Unit (fun _ => List Bool) inst (fun _ => acc) () (b :: acc) =
          (fun _ => b :: acc) := by
        funext ⟨⟩; simp [Function.update]
      rw [hupd]
      exact ih (b :: acc)

lemma choose_step (y z : List Bool) (b : Bool) :
    (chooseTM y z).step (initList (chooseTM y z) ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀))) =
      some (haltList (chooseTM y z) ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁))) := by
  have hi : initList (chooseTM y z) ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀)) =
      ⟨some (), false, fun _ => [b]⟩ := by
    simp only [initList]; congr 1
  have hh : haltList (chooseTM y z) ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁)) =
      ⟨none, false, fun _ => if b then y else z⟩ := by
    simp only [haltList]; congr 1
  rw [hi, hh]
  have hupd : @Function.update Unit (fun _ => List Bool) (chooseTM y z).decidableEqK
      (fun _ => [b]) () [] = (fun _ => []) := by
    funext ⟨⟩; simp [Function.update]
  cases b with
  | true =>
      simp only [FinTM2.step, chooseTM, TM2.step, TM2.stepAux, List.head?_cons,
        Option.getD_some, id, Bool.cond_true, List.tail_cons, ↓reduceIte]
      have hpush : @TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList y.reverse) false (fun _ : Unit => []) = ⟨none, false, fun _ => y⟩ := by
        simpa [List.reverseAux_eq_append] using stepAux_pushList (chooseTM y z).decidableEqK y.reverse []
      exact congrArg some ((congrArg (@TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList y.reverse) false) hupd).trans hpush)
  | false =>
      simp only [FinTM2.step, chooseTM, TM2.step, TM2.stepAux, List.head?_cons,
        Option.getD_some, id, Bool.cond_false, List.tail_cons, Bool.false_eq_true, ↓reduceIte]
      have hpush : @TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList z.reverse) false (fun _ : Unit => []) = ⟨none, false, fun _ => z⟩ := by
        simpa [List.reverseAux_eq_append] using stepAux_pushList (chooseTM y z).decidableEqK z.reverse []
      exact congrArg some ((congrArg (@TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList z.reverse) false) hupd).trans hpush)

noncomputable def choosePoly (y z : List Bool) :
    TM2ComputableInPolyTime PvsNP.encodeAnswer PvsNP.encodeString
      (fun b : Bool => if b then y else z) where
  tm := chooseTM y z
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b :=
    { steps := 1
      evals_in_steps := by
        have h1 : @List.map Bool ((chooseTM y z).Γ (chooseTM y z).k₀)
            (Equiv.refl Bool).invFun (PvsNP.encodeAnswer b) =
            ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀)) := rfl
        have h2 : @List.map Bool ((chooseTM y z).Γ (chooseTM y z).k₁)
            (Equiv.refl Bool).invFun (if b then y else z) =
            ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁)) := List.map_id _
        exact (congrArg (fun l => (flip bind (chooseTM y z).step)^[1]
            (some (initList (chooseTM y z) l))) h1).trans
          ((choose_step y z b).trans
            (congrArg (fun l => some (haltList (chooseTM y z) l)) h2.symm))
      steps_le_m := by simp }

end PvsNP.Units.m2_x_balanced_karp_sorted

theorem PvsNP.Units.m2_x_balanced_karp_sorted :
    PvsNP.KarpReducible ({x : List Bool | x.count true = x.count false} : Language Bool)
      ({x : List Bool | List.SortedLE x} : Language Bool) := by
  let f : List Bool → Bool := fun x =>
    decide (PvsNP.Units.m2_x_balanced_karp_sorted.truesUnary x =
      PvsNP.Units.m2_x_balanced_karp_sorted.falsesUnary x)
  refine ⟨fun x => if f x then [] else [true, false],
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_x_balanced_karp_sorted.cpt_balDec
      ⟨PvsNP.Units.m2_x_balanced_karp_sorted.choosePoly [] [true, false]⟩,
    fun x => ?_⟩
  have hdec : x.count true = x.count false ↔ f x = true := by
    change x.count true = x.count false ↔
      decide (PvsNP.Units.m2_x_balanced_karp_sorted.truesUnary x =
        PvsNP.Units.m2_x_balanced_karp_sorted.falsesUnary x) = true
    rw [PvsNP.Units.m2_x_balanced_karp_sorted.truesUnary_eq_replicate,
      PvsNP.Units.m2_x_balanced_karp_sorted.falsesUnary_eq_replicate]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      have heq := of_decide_eq_true h
      have hlen := congrArg List.length heq
      simp only [List.length_replicate] at hlen
      exact hlen
  have hy : ([] : List Bool) ∈ ({x : List Bool | List.SortedLE x} : Language Bool) := by
    change List.SortedLE ([] : List Bool)
    decide
  have hz : ([true, false] : List Bool) ∉ ({x : List Bool | List.SortedLE x} : Language Bool) := by
    change ¬ List.SortedLE ([true, false] : List Bool)
    decide
  change x.count true = x.count false ↔
    (if f x then ([] : List Bool) else [true, false]) ∈ ({x : List Bool | List.SortedLE x} : Language Bool)
  rw [hdec]
  cases hfx : f x with
  | false => simp [hz]
  | true => simp [hy]
