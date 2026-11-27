import Mathlib
import PvsNP.Defs
import CookLevin

open Turing

namespace PvsNP.Units.m2_tm_y_dfa_time

variable {Q : Type} [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool)

def dfaStmt : TM2.Stmt (fun _ : Unit => Bool) Unit (Q × Option Bool) :=
  .pop ⟨⟩ (fun v o => (v.1, o))
    (.branch (fun v => v.2.isSome)
      (.load (fun v => (δ v.1 (v.2.getD false), none)) (.goto fun _ => ()))
      (.push ⟨⟩ (fun v => F v.1) (.load (fun _ => (q₀, none)) .halt)))

abbrev dfaTM : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Q × Option Bool
  initialState := (q₀, none)
  m _ := dfaStmt δ q₀ F

theorem dfa_initList (x : List Bool) :
    initList (dfaTM δ q₀ F) x =
      (⟨some (), (q₀, none), Function.update (fun _ => []) ⟨⟩ x⟩ :
        TM2.Cfg (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).Λ (dfaTM δ q₀ F).σ) := by
  unfold initList
  congr 1

theorem dfa_haltList (b : Bool) :
    haltList (dfaTM δ q₀ F) [b] =
      (⟨none, (q₀, none), Function.update (fun _ => []) ⟨⟩ [b]⟩ :
        TM2.Cfg (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).Λ (dfaTM δ q₀ F).σ) := by
  unfold haltList
  congr 1

theorem dfa_step_cons (b : Bool) (l : List Bool) (q : Q) (o : Option Bool) :
    TM2.step (dfaTM δ q₀ F).m
        (⟨some (), (q, o), Function.update (fun _ => []) ⟨⟩ (b :: l)⟩ :
          TM2.Cfg (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).Λ (dfaTM δ q₀ F).σ) =
      some ⟨some (), (δ q b, none), Function.update (fun _ => []) ⟨⟩ l⟩ := by
  simp only [TM2.step, dfaTM, dfaStmt, TM2.stepAux, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some, Function.update_self, Function.update_idem]

theorem dfa_step_nil (q : Q) (o : Option Bool) :
    TM2.step (dfaTM δ q₀ F).m
        (⟨some (), (q, o), Function.update (fun _ => []) ⟨⟩ ([] : List Bool)⟩ :
          TM2.Cfg (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).Λ (dfaTM δ q₀ F).σ) =
      some ⟨none, (q₀, none), Function.update (fun _ => []) ⟨⟩ [F q]⟩ := by
  simp only [TM2.step, dfaTM, dfaStmt, TM2.stepAux, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Function.update_self, Function.update_idem]

theorem dfa_run : ∀ (l : List Bool) (q : Q) (o : Option Bool),
    (flip bind (TM2.step (dfaTM δ q₀ F).m))^[l.length + 1]
        (some (⟨some (), (q, o), Function.update (fun _ => []) ⟨⟩ l⟩ :
          TM2.Cfg (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).Λ (dfaTM δ q₀ F).σ)) =
      some ⟨none, (q₀, none), Function.update (fun _ => []) ⟨⟩ [F (l.foldl δ q)]⟩ := by
  intro l
  induction l with
  | nil =>
    intro q o
    exact dfa_step_nil δ q₀ F q o
  | cons b l ih =>
    intro q o
    rw [List.length_cons]
    refine (Function.iterate_succ_apply _ _ _).trans ?_
    refine (congrArg _ (dfa_step_cons δ q₀ F b l q o)).trans ?_
    rw [ih, List.foldl_cons]

def dfaInEquiv : (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).k₀ ≃ Bool := Equiv.refl Bool

def dfaOutEquiv : (dfaTM δ q₀ F).Γ (dfaTM δ q₀ F).k₁ ≃ Bool := Equiv.refl Bool

noncomputable def dfaComputableInTime :
    @TM2ComputableInTime (List Bool) Bool Bool Bool
      PvsNP.encodeString PvsNP.encodeAnswer (fun x => F (x.foldl δ q₀)) where
  tm := dfaTM δ q₀ F
  inputAlphabet := dfaInEquiv δ q₀ F
  outputAlphabet := dfaOutEquiv δ q₀ F
  time := fun n => n + 1
  outputsFun x :=
    { steps := x.length + 1
      evals_in_steps := by
        have h1 : List.map (dfaInEquiv δ q₀ F).invFun (PvsNP.encodeString x) = x :=
          List.map_id x
        have h2 : List.map (dfaOutEquiv δ q₀ F).invFun (PvsNP.encodeAnswer (F (x.foldl δ q₀)))
            = [F (x.foldl δ q₀)] :=
          List.map_id _
        show (flip bind (TM2.step (dfaTM δ q₀ F).m))^[x.length + 1]
            (some (initList (dfaTM δ q₀ F) (List.map (dfaInEquiv δ q₀ F).invFun (PvsNP.encodeString x)))) =
          some (haltList (dfaTM δ q₀ F) (List.map (dfaOutEquiv δ q₀ F).invFun (PvsNP.encodeAnswer (F (x.foldl δ q₀)))))
        rw [h1, h2, dfa_initList, dfa_haltList]
        exact dfa_run δ q₀ F x q₀ none
      steps_le_m := by
        simp only [PvsNP.encodeString, Computability.encodingList, List.length_map, id_eq]
        exact le_refl _ }

end PvsNP.Units.m2_tm_y_dfa_time

/-- A finite automaton run on the input answers within `2n + 3` steps: a
one-stack TM2 whose state is the DFA state simulates the fold in one step
per input bit plus one final step, so its time function `n + 1` is below
`2n + 3`. -/
theorem PvsNP.Units.m2_tm_y_dfa_time :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool),
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => F (x.foldl δ q₀)),
        ∀ n : ℕ, M.time n ≤ 2 * n + 3 := by
  intro Q _ δ q₀ F
  have htime : ∀ n : ℕ,
      (PvsNP.Units.m2_tm_y_dfa_time.dfaComputableInTime δ q₀ F).time n = n + 1 :=
    fun n => rfl
  exact ⟨PvsNP.Units.m2_tm_y_dfa_time.dfaComputableInTime δ q₀ F, fun n => by
    rw [htime n]; omega⟩
