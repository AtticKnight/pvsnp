import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_anti_pal_p

private inductive PalK : Type
  | io | s1 | s2 | s3
deriving DecidableEq

private instance : Fintype PalK :=
  Fintype.ofEquiv (Fin 4)
    { toFun := fun i => match i.1 with | 0 => .io | 1 => .s1 | 2 => .s2 | _ => .s3
      invFun := fun k => match k with | .io => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun k => by cases k <;> rfl }

private inductive PalL : Type
  | dup | rev | cmp | drain
deriving DecidableEq

private instance : Fintype PalL :=
  Fintype.ofEquiv (Fin 4)
    { toFun := fun i => match i.1 with | 0 => .dup | 1 => .rev | 2 => .cmp | _ => .drain
      invFun := fun l => match l with | .dup => 0 | .rev => 1 | .cmp => 2 | .drain => 3
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun l => by cases l <;> rfl }

private abbrev PalS : Type := Option Bool × Option Bool

private def initS : PalS := (none, none)

private def palTM : Turing.FinTM2 where
  K := PalK
  k₀ := .io
  k₁ := .io
  Γ _ := Bool
  Λ := PalL
  main := .dup
  σ := PalS
  initialState := initS
  m l := match l with
    | .dup =>
      .pop .io (fun s o => (o, s.2))
        (.branch (fun s => s.1.isSome)
          (.push .s1 (fun s => s.1.getD false)
            (.push .s2 (fun s => s.1.getD false)
              (.load (fun _ => initS) (.goto (fun _ => .dup)))))
          (.load (fun _ => initS) (.goto (fun _ => .rev))))
    | .rev =>
      .pop .s1 (fun s o => (o, s.2))
        (.branch (fun s => s.1.isSome)
          (.push .s3 (fun s => (! (s.1.getD false)))
            (.load (fun _ => initS) (.goto (fun _ => .rev))))
          (.load (fun _ => initS) (.goto (fun _ => .cmp))))
    | .cmp =>
      .pop .s2 (fun s o => (o, s.2))
        (.pop .s3 (fun s o => (s.1, o))
          (.branch (fun s => decide (s.1 = s.2))
            (.branch (fun s => s.1.isNone)
              (.push .io (fun _ => true) (.load (fun _ => initS) .halt))
              (.load (fun _ => initS) (.goto (fun _ => .cmp))))
            (.load (fun _ => initS) (.goto (fun _ => .drain)))))
    | .drain =>
      .pop .s2 (fun s o => (o, s.2))
        (.pop .s3 (fun s o => (s.1, o))
          (.branch (fun s => s.1.isSome || s.2.isSome)
            (.load (fun _ => initS) (.goto (fun _ => .drain)))
            (.push .io (fun _ => false) (.load (fun _ => initS) .halt))))

private def mkCfg (l : Option PalL) (io s1 s2 s3 : List Bool) : palTM.Cfg where
  l := l
  var := initS
  stk k := match k with
    | .io => io | .s1 => s1 | .s2 => s2 | .s3 => s3

private theorem cfg_ext {c₁ c₂ : palTM.Cfg}
    (h1 : c₁.l = c₂.l) (h2 : c₁.var = c₂.var) (h3 : ∀ k, c₁.stk k = c₂.stk k) :
    c₁ = c₂ := by
  cases c₁; cases c₂
  simp only at h1 h2 h3
  subst h1; subst h2
  congr; funext k; exact h3 k

private theorem step_dup_nil (s1 s2 : List Bool) :
    palTM.step (mkCfg (some .dup) [] s1 s2 []) = some (mkCfg (some .rev) [] s1 s2 []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_dup_cons (b : Bool) (x s1 s2 : List Bool) :
    palTM.step (mkCfg (some .dup) (b :: x) s1 s2 []) =
      some (mkCfg (some .dup) x (b :: s1) (b :: s2) []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_dup :
    ∀ (x s1 s2 : List Bool),
      (flip bind palTM.step)^[x.length + 1] (some (mkCfg (some .dup) x s1 s2 [])) =
        some (mkCfg (some .rev) [] (x.reverse ++ s1) (x.reverse ++ s2) [])
  | [], s1, s2 => by
    change palTM.step (mkCfg (some .dup) [] s1 s2 []) = some (mkCfg (some .rev) [] s1 s2 [])
    exact step_dup_nil s1 s2
  | b :: x, s1, s2 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind palTM.step)^[x.length + 1] (palTM.step (mkCfg (some .dup) (b :: x) s1 s2 [])) = _
    rw [step_dup_cons]
    simpa [List.reverse_cons, List.append_assoc] using eval_dup x (b :: s1) (b :: s2)

private theorem step_rev_nil (s2 s3 : List Bool) :
    palTM.step (mkCfg (some .rev) [] [] s2 s3) = some (mkCfg (some .cmp) [] [] s2 s3) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_rev_cons (b : Bool) (s1 s2 s3 : List Bool) :
    palTM.step (mkCfg (some .rev) [] (b :: s1) s2 s3) =
      some (mkCfg (some .rev) [] s1 s2 ((!b) :: s3)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_rev :
    ∀ (s1 s2 s3 : List Bool),
      (flip bind palTM.step)^[s1.length + 1] (some (mkCfg (some .rev) [] s1 s2 s3)) =
        some (mkCfg (some .cmp) [] [] s2 ((s1.reverse).map not ++ s3))
  | [], s2, s3 => by
    change palTM.step (mkCfg (some .rev) [] [] s2 s3) = some (mkCfg (some .cmp) [] [] s2 s3)
    exact step_rev_nil s2 s3
  | b :: s1, s2, s3 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind palTM.step)^[s1.length + 1] (palTM.step (mkCfg (some .rev) [] (b :: s1) s2 s3)) = _
    rw [step_rev_cons]
    simpa [List.reverse_cons, List.map_append, List.map_cons, List.append_assoc] using eval_rev s1 s2 ((!b) :: s3)

private def drainSteps (s2 s3 : List Bool) : ℕ := max s2.length s3.length + 1

private theorem step_drain_nil :
    palTM.step (mkCfg (some .drain) [] [] [] []) = some (mkCfg none [false] [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_drain_nonnil {s2 s3 : List Bool} (h : ¬ (s2 = [] ∧ s3 = [])) :
    palTM.step (mkCfg (some .drain) [] [] s2 s3) =
      some (mkCfg (some .drain) [] [] s2.tail s3.tail) := by
  cases s2 with
  | nil =>
    cases s3 with
    | nil => exact absurd ⟨rfl, rfl⟩ h
    | cons b s3 =>
      apply congrArg some
      exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | cons a s2 =>
    cases s3 with
    | nil =>
      apply congrArg some
      exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    | cons b s3 =>
      apply congrArg some
      exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_drain_aux :
    ∀ (n : ℕ) (s2 s3 : List Bool), max s2.length s3.length = n →
      (flip bind palTM.step)^[n + 1] (some (mkCfg (some .drain) [] [] s2 s3)) =
        some (mkCfg none [false] [] [] [])
  | 0, s2, s3, h => by
    have hs2 : s2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hs3 : s3 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hs2; subst hs3
    change palTM.step (mkCfg (some .drain) [] [] [] []) = some (mkCfg none [false] [] [] [])
    exact step_drain_nil
  | n + 1, s2, s3, h => by
    have hne : ¬ (s2 = [] ∧ s3 = []) := by
      rintro ⟨rfl, rfl⟩; simp at h
    have htail : max s2.tail.length s3.tail.length = n := by
      cases s2 <;> cases s3 <;> simp at h ⊢ <;> omega
    rw [Function.iterate_succ_apply]
    change (flip bind palTM.step)^[n + 1] (palTM.step (mkCfg (some .drain) [] [] s2 s3)) = _
    rw [step_drain_nonnil hne]
    exact eval_drain_aux n s2.tail s3.tail htail

private theorem eval_drain (s2 s3 : List Bool) :
    (flip bind palTM.step)^[drainSteps s2 s3] (some (mkCfg (some .drain) [] [] s2 s3)) =
      some (mkCfg none [false] [] [] []) :=
  eval_drain_aux (max s2.length s3.length) s2 s3 rfl

private def cmpSteps : List Bool → List Bool → ℕ
  | [], [] => 1
  | a :: s2, b :: s3 => if a = b then cmpSteps s2 s3 + 1 else drainSteps s2 s3 + 1
  | [], _ :: s3 => drainSteps [] s3 + 1
  | _ :: s2, [] => drainSteps s2 [] + 1

private theorem cmpSteps_le :
    ∀ s2 s3 : List Bool, cmpSteps s2 s3 ≤ s2.length + s3.length + 2
  | [], [] => by simp [cmpSteps]
  | a :: s2, b :: s3 => by
    unfold cmpSteps
    split_ifs
    · have ih := cmpSteps_le s2 s3; simp; omega
    · simp [drainSteps]; omega
  | [], _ :: s3 => by simp [cmpSteps, drainSteps]
  | _ :: s2, [] => by simp [cmpSteps, drainSteps]

private theorem step_cmp_nil :
    palTM.step (mkCfg (some .cmp) [] [] [] []) = some (mkCfg none [true] [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cmp_eq (a : Bool) (s2 s3 : List Bool) :
    palTM.step (mkCfg (some .cmp) [] [] (a :: s2) (a :: s3)) =
      some (mkCfg (some .cmp) [] [] s2 s3) := by
  cases a
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cmp_ne {a b : Bool} (h : a ≠ b) (s2 s3 : List Bool) :
    palTM.step (mkCfg (some .cmp) [] [] (a :: s2) (b :: s3)) =
      some (mkCfg (some .drain) [] [] s2 s3) := by
  cases a <;> cases b
  · exact absurd rfl h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · exact absurd rfl h

private theorem step_cmp_nil_cons (b : Bool) (s3 : List Bool) :
    palTM.step (mkCfg (some .cmp) [] [] [] (b :: s3)) =
      some (mkCfg (some .drain) [] [] [] s3) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cmp_cons_nil (a : Bool) (s2 : List Bool) :
    palTM.step (mkCfg (some .cmp) [] [] (a :: s2) []) =
      some (mkCfg (some .drain) [] [] s2 []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_cmp :
    ∀ (s2 s3 : List Bool),
      (flip bind palTM.step)^[cmpSteps s2 s3] (some (mkCfg (some .cmp) [] [] s2 s3)) =
        some (mkCfg none [decide (s2 = s3)] [] [] [])
  | [], [] => by
    change palTM.step (mkCfg (some .cmp) [] [] [] []) = some (mkCfg none [true] [] [] [])
    exact step_cmp_nil
  | a :: s2, b :: s3 => by
    by_cases hab : a = b
    · subst hab
      simp only [cmpSteps, ↓reduceIte]
      rw [Function.iterate_succ_apply]
      change (flip bind palTM.step)^[cmpSteps s2 s3] (palTM.step (mkCfg (some .cmp) [] [] (a :: s2) (a :: s3))) = _
      rw [step_cmp_eq]
      simpa using eval_cmp s2 s3
    · simp only [cmpSteps, hab, ↓reduceIte]
      rw [Function.iterate_succ_apply]
      change (flip bind palTM.step)^[drainSteps s2 s3] (palTM.step (mkCfg (some .cmp) [] [] (a :: s2) (b :: s3))) = _
      rw [step_cmp_ne hab]
      simpa [hab] using eval_drain s2 s3
  | [], b :: s3 => by
    simp only [cmpSteps]
    rw [Function.iterate_succ_apply]
    change (flip bind palTM.step)^[drainSteps [] s3] (palTM.step (mkCfg (some .cmp) [] [] [] (b :: s3))) = _
    rw [step_cmp_nil_cons]
    simpa using eval_drain [] s3
  | a :: s2, [] => by
    simp only [cmpSteps]
    rw [Function.iterate_succ_apply]
    change (flip bind palTM.step)^[drainSteps s2 []] (palTM.step (mkCfg (some .cmp) [] [] (a :: s2) [])) = _
    rw [step_cmp_cons_nil]
    simpa using eval_drain s2 []

private noncomputable def palComputable :
    Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (x.reverse = x.map not)) where
  tm := palTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
  outputsFun x :=
    { steps := cmpSteps x.reverse (x.map not) + ((x.length + 1) + (x.length + 1))
      evals_in_steps := by
        have hdup := eval_dup x [] []
        have hrev := eval_rev x.reverse x.reverse []
        have hcmp := eval_cmp x.reverse (x.map not)
        have hinit : Turing.initList palTM (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x)) =
            mkCfg (some .dup) x [] [] [] := by
          apply cfg_ext
          · rfl
          · rfl
          · intro k
            cases k
            · exact List.map_id x
            · rfl
            · rfl
            · rfl
        have hhalt : Option.map (Turing.haltList palTM)
            (some (List.map (Equiv.refl Bool).invFun (PvsNP.encodeAnswer (decide (x.reverse = x.map not))))) =
            some (mkCfg none [decide (x.reverse = x.map not)] [] [] []) := by
          apply congrArg some
          apply cfg_ext
          · rfl
          · rfl
          · intro k
            cases k <;> rfl
        rw [hinit, hhalt, Function.iterate_add_apply, Function.iterate_add_apply]
        simp only [List.append_nil] at hdup
        rw [hdup]
        simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hrev
        rw [hrev]
        exact hcmp
      steps_le_m := by
        have hk := cmpSteps_le x.reverse (x.map not)
        simp only [PvsNP.encodeString, Computability.encodingList, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        simp only [List.length_reverse, List.length_map] at hk
        omega }

end PvsNP.Units.tl_lang_anti_pal_p

theorem PvsNP.Units.tl_lang_anti_pal_p :
    ({x : List Bool | x.reverse = x.map not} : Language Bool) ∈ PvsNP.P :=
  ⟨fun x => decide (x.reverse = x.map not), ⟨PvsNP.Units.tl_lang_anti_pal_p.palComputable⟩,
    fun _ => by simp only [decide_eq_true_eq]; rfl⟩
