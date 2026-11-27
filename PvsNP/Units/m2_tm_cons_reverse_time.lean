import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_cons_reverse_time

open Turing

private def revConsTM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := fun () =>
    TM2.Stmt.pop false (fun _ o => o)
      (TM2.Stmt.branch Option.isSome
        (TM2.Stmt.push true (fun o => o.getD false) (TM2.Stmt.goto (fun _ => ())))
        (TM2.Stmt.push true (fun _ => true) TM2.Stmt.halt))

private def mkStk (inp out : List Bool) : Bool → List Bool
  | false => inp
  | true => out

private theorem step_cons (v : Option Bool) (b : Bool) (inp out : List Bool) :
    TM2.step revConsTM.m ⟨some (), v, mkStk (b :: inp) out⟩ =
      some ⟨some (), some b, mkStk inp (b :: out)⟩ := by
  simp only [TM2.step, revConsTM, TM2.stepAux, mkStk, List.head?_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_nil (v : Option Bool) (out : List Bool) :
    TM2.step revConsTM.m ⟨some (), v, mkStk [] out⟩ =
      some ⟨none, none, mkStk [] (true :: out)⟩ := by
  simp only [TM2.step, revConsTM, TM2.stepAux, mkStk, List.head?_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem run_rev : ∀ (inp out : List Bool) (v : Option Bool),
    (flip bind (TM2.step revConsTM.m))^[inp.length + 1] (some ⟨some (), v, mkStk inp out⟩) =
      some ⟨none, none, mkStk [] (true :: (inp.reverse ++ out))⟩
  | [], out, v => by
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip,
      List.reverse_nil, List.nil_append]
    exact step_nil v out
  | b :: inp, out, v => by
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have h1 : flip bind (TM2.step revConsTM.m) (some ⟨some (), v, mkStk (b :: inp) out⟩) =
        some ⟨some (), some b, mkStk inp (b :: out)⟩ := step_cons v b inp out
    rw [h1, run_rev inp (b :: out) (some b)]
    simp [List.reverse_cons, List.append_assoc]

private def revConsComp :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => true :: x.reverse) where
  tm := revConsTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => n + 1
  outputsFun := fun x =>
    { steps := x.length + 1
      steps_le_m := le_rfl
      evals_in_steps := by
        have hinit : initList revConsTM (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x)) =
            ⟨some (), none, mkStk x []⟩ := by
          unfold initList
          congr 1
          funext k
          cases k
          · simp [revConsTM, mkStk, PvsNP.encodeString]; rfl
          · simp [revConsTM, mkStk]
        have hhalt : haltList revConsTM (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString (true :: x.reverse))) =
            ⟨none, none, mkStk [] (true :: x.reverse)⟩ := by
          unfold haltList
          congr 1
          funext k
          cases k
          · simp [revConsTM, mkStk]
          · simp [revConsTM, mkStk, PvsNP.encodeString]; rfl
        rw [hinit, Option.map_some, hhalt]
        have hrun := run_rev x [] none
        simp only [List.append_nil] at hrun
        exact hrun }

theorem cons_reverse_time_main :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => true :: x.reverse),
      ∀ n : ℕ, M.time n ≤ 5 * n + 6 :=
  ⟨revConsComp, fun n => by dsimp [revConsComp]; omega⟩

end PvsNP.Units.m2_tm_cons_reverse_time

theorem PvsNP.Units.m2_tm_cons_reverse_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => true :: x.reverse),
      ∀ n : ℕ, M.time n ≤ 5 * n + 6 :=
  PvsNP.Units.m2_tm_cons_reverse_time.cons_reverse_time_main
