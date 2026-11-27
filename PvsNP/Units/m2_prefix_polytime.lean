import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_prefix_polytime

private inductive PrK : Type
  | inp | r1 | r2 | s1 | s2 | out
deriving DecidableEq

private instance : Fintype PrK :=
  Fintype.ofEquiv (Fin 6)
    { toFun := fun i => match i.1 with
        | 0 => .inp | 1 => .r1 | 2 => .r2 | 3 => .s1 | 4 => .s2 | _ => .out
      invFun := fun k => match k with
        | .inp => 0 | .r1 => 1 | .r2 => 2 | .s1 => 3 | .s2 => 4 | .out => 5
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun k => by cases k <;> rfl }

private inductive PrL : Type
  | split | rev1 | rev2 | cmp | drainT | drainF
deriving DecidableEq

private instance : Fintype PrL :=
  Fintype.ofEquiv (Fin 6)
    { toFun := fun i => match i.1 with
        | 0 => .split | 1 => .rev1 | 2 => .rev2 | 3 => .cmp | 4 => .drainT | _ => .drainF
      invFun := fun l => match l with
        | .split => 0 | .rev1 => 1 | .rev2 => 2 | .cmp => 3 | .drainT => 4 | .drainF => 5
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun l => by cases l <;> rfl }

private abbrev PrΓ : PrK → Type
  | .inp => Bool ⊕ Bool
  | _ => Bool

private abbrev PrS : Type := Option (Bool ⊕ Bool) × Option Bool × Option Bool

private def initS : PrS := (none, none, none)

private def prefTM : Turing.FinTM2 where
  K := PrK
  k₀ := .inp
  k₁ := .out
  Γ := PrΓ
  Λ := PrL
  main := .split
  σ := PrS
  initialState := initS
  m l := match l with
    | .split =>
      .pop .inp (fun _ o => (o, none, none))
        (.branch (fun s => s.1.isSome)
          (.branch (fun s => match s.1 with | some (Sum.inl _) => true | _ => false)
            (.push .r1 (fun s => match s.1 with | some (Sum.inl b) => b | _ => false)
              (.load (fun _ => initS) (.goto (fun _ => .split))))
            (.push .r2 (fun s => match s.1 with | some (Sum.inr b) => b | _ => false)
              (.load (fun _ => initS) (.goto (fun _ => .split)))))
          (.load (fun _ => initS) (.goto (fun _ => .rev1))))
    | .rev1 =>
      .pop .r1 (fun _ o => (none, o, none))
        (.branch (fun s => s.2.1.isSome)
          (.push .s1 (fun s => s.2.1.getD false)
            (.load (fun _ => initS) (.goto (fun _ => .rev1))))
          (.load (fun _ => initS) (.goto (fun _ => .rev2))))
    | .rev2 =>
      .pop .r2 (fun _ o => (none, o, none))
        (.branch (fun s => s.2.1.isSome)
          (.push .s2 (fun s => s.2.1.getD false)
            (.load (fun _ => initS) (.goto (fun _ => .rev2))))
          (.load (fun _ => initS) (.goto (fun _ => .cmp))))
    | .cmp =>
      .pop .s1 (fun _ a => (none, a, none))
        (.pop .s2 (fun s b => (none, s.2.1, b))
          (.branch (fun s => s.2.1.isNone)
            (.branch (fun s => s.2.2.isNone)
              (.push .out (fun _ => true) (.load (fun _ => initS) .halt))
              (.load (fun _ => initS) (.goto (fun _ => .drainT))))
            (.branch (fun s => decide (s.2.1 = s.2.2))
              (.load (fun _ => initS) (.goto (fun _ => .cmp)))
              (.load (fun _ => initS) (.goto (fun _ => .drainF))))))
    | .drainT =>
      .pop .s2 (fun _ b => (none, none, b))
        (.branch (fun s => s.2.2.isSome)
          (.load (fun _ => initS) (.goto (fun _ => .drainT)))
          (.push .out (fun _ => true) (.load (fun _ => initS) .halt)))
    | .drainF =>
      .pop .s1 (fun _ a => (none, a, none))
        (.pop .s2 (fun s b => (none, s.2.1, b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.load (fun _ => initS) (.goto (fun _ => .drainF)))
            (.push .out (fun _ => false) (.load (fun _ => initS) .halt))))

private def mkCfg (l : Option PrL) (inp : List (Bool ⊕ Bool))
    (r1 r2 s1 s2 out : List Bool) : prefTM.Cfg where
  l := l
  var := initS
  stk k := match k with
    | .inp => inp | .r1 => r1 | .r2 => r2 | .s1 => s1 | .s2 => s2 | .out => out

private theorem cfg_ext {c₁ c₂ : prefTM.Cfg}
    (h1 : c₁.l = c₂.l) (h2 : c₁.var = c₂.var) (h3 : ∀ k, c₁.stk k = c₂.stk k) :
    c₁ = c₂ := by
  cases c₁; cases c₂; simp only at h1 h2 h3; subst h1; subst h2; congr; funext k; exact h3 k

private theorem eval_split_inl :
    ∀ (x : List Bool) (rest : List (Bool ⊕ Bool)) (r1 r2 : List Bool),
      (flip bind prefTM.step)^[x.length] (some (mkCfg (some .split) (x.map Sum.inl ++ rest) r1 r2 [] [] [])) =
        some (mkCfg (some .split) rest (x.reverse ++ r1) r2 [] [] [])
  | [], _, _, _ => by simp
  | b :: x, rest, r1, r2 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .split) (Sum.inl b :: (x.map Sum.inl ++ rest)) r1 r2 [] [] []) =
        some (mkCfg (some .split) (x.map Sum.inl ++ rest) (b :: r1) r2 [] [] []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[x.length]
      (prefTM.step (mkCfg (some .split) (Sum.inl b :: (x.map Sum.inl ++ rest)) r1 r2 [] [] [])) = _
    rw [hstep]
    simpa [List.reverse_cons, List.append_assoc] using eval_split_inl x rest (b :: r1) r2

private theorem eval_split_inr :
    ∀ (y r1 r2 : List Bool),
      (flip bind prefTM.step)^[y.length + 1] (some (mkCfg (some .split) (y.map Sum.inr) r1 r2 [] [] [])) =
        some (mkCfg (some .rev1) [] r1 (y.reverse ++ r2) [] [] [])
  | [], r1, r2 => by
    change prefTM.step (mkCfg (some .split) [] r1 r2 [] [] []) = some (mkCfg (some .rev1) [] r1 r2 [] [] [])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | b :: y, r1, r2 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .split) (Sum.inr b :: y.map Sum.inr) r1 r2 [] [] []) =
        some (mkCfg (some .split) (y.map Sum.inr) r1 (b :: r2) [] [] []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[y.length + 1]
      (prefTM.step (mkCfg (some .split) (Sum.inr b :: y.map Sum.inr) r1 r2 [] [] [])) = _
    rw [hstep]
    simpa [List.reverse_cons, List.append_assoc] using eval_split_inr y r1 (b :: r2)

private theorem eval_rev1 :
    ∀ (r1 r2 s1 : List Bool),
      (flip bind prefTM.step)^[r1.length + 1] (some (mkCfg (some .rev1) [] r1 r2 s1 [] [])) =
        some (mkCfg (some .rev2) [] [] r2 (r1.reverse ++ s1) [] [])
  | [], r2, s1 => by
    change prefTM.step (mkCfg (some .rev1) [] [] r2 s1 [] []) = some (mkCfg (some .rev2) [] [] r2 s1 [] [])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | b :: r1, r2, s1 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .rev1) [] (b :: r1) r2 s1 [] []) =
        some (mkCfg (some .rev1) [] r1 r2 (b :: s1) [] []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[r1.length + 1]
      (prefTM.step (mkCfg (some .rev1) [] (b :: r1) r2 s1 [] [])) = _
    rw [hstep]
    simpa [List.reverse_cons, List.append_assoc] using eval_rev1 r1 r2 (b :: s1)

private theorem eval_rev2 :
    ∀ (r2 s1 s2 : List Bool),
      (flip bind prefTM.step)^[r2.length + 1] (some (mkCfg (some .rev2) [] [] r2 s1 s2 [])) =
        some (mkCfg (some .cmp) [] [] [] s1 (r2.reverse ++ s2) [])
  | [], s1, s2 => by
    change prefTM.step (mkCfg (some .rev2) [] [] [] s1 s2 []) = some (mkCfg (some .cmp) [] [] [] s1 s2 [])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | b :: r2, s1, s2 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .rev2) [] [] (b :: r2) s1 s2 []) =
        some (mkCfg (some .rev2) [] [] r2 s1 (b :: s2) []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[r2.length + 1]
      (prefTM.step (mkCfg (some .rev2) [] [] (b :: r2) s1 s2 [])) = _
    rw [hstep]
    simpa [List.reverse_cons, List.append_assoc] using eval_rev2 r2 s1 (b :: s2)

private theorem eval_drainT :
    ∀ s2 : List Bool,
      (flip bind prefTM.step)^[s2.length + 1] (some (mkCfg (some .drainT) [] [] [] [] s2 [])) =
        some (mkCfg none [] [] [] [] [] [true])
  | [] => by
    change prefTM.step (mkCfg (some .drainT) [] [] [] [] [] []) = some (mkCfg none [] [] [] [] [] [true])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | b :: s2 => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .drainT) [] [] [] [] (b :: s2) []) =
        some (mkCfg (some .drainT) [] [] [] [] s2 []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[s2.length + 1]
      (prefTM.step (mkCfg (some .drainT) [] [] [] [] (b :: s2) [])) = _
    rw [hstep]
    exact eval_drainT s2

private def drainFSteps (s1 s2 : List Bool) : ℕ := max s1.length s2.length + 1

private theorem eval_drainF_aux :
    ∀ (n : ℕ) (s1 s2 : List Bool), max s1.length s2.length = n →
      (flip bind prefTM.step)^[n + 1] (some (mkCfg (some .drainF) [] [] [] s1 s2 [])) =
        some (mkCfg none [] [] [] [] [] [false])
  | 0, s1, s2, h => by
    have hs1 : s1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hs2 : s2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hs1; subst hs2
    change prefTM.step (mkCfg (some .drainF) [] [] [] [] [] []) = some (mkCfg none [] [] [] [] [] [false])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | n + 1, s1, s2, h => by
    have htail : max s1.tail.length s2.tail.length = n := by
      cases s1 <;> cases s2 <;> simp at h ⊢ <;> omega
    have hstep : prefTM.step (mkCfg (some .drainF) [] [] [] s1 s2 []) =
        some (mkCfg (some .drainF) [] [] [] s1.tail s2.tail []) := by
      cases s1 with
      | nil =>
        cases s2 with
        | nil => simp at h
        | cons b s2 => apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
      | cons a s1 =>
        cases s2 with
        | nil => apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
        | cons b s2 => apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    rw [Function.iterate_succ_apply]
    change (flip bind prefTM.step)^[n + 1]
      (prefTM.step (mkCfg (some .drainF) [] [] [] s1 s2 [])) = _
    rw [hstep]
    exact eval_drainF_aux n s1.tail s2.tail htail

private theorem eval_drainF (s1 s2 : List Bool) :
    (flip bind prefTM.step)^[drainFSteps s1 s2] (some (mkCfg (some .drainF) [] [] [] s1 s2 [])) =
      some (mkCfg none [] [] [] [] [] [false]) :=
  eval_drainF_aux (max s1.length s2.length) s1 s2 rfl

private def cmpSteps : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: s2 => s2.length + 2
  | a :: s1, b :: s2 => if a = b then cmpSteps s1 s2 + 1 else drainFSteps s1 s2 + 1
  | _ :: s1, [] => drainFSteps s1 [] + 1

private theorem cmpSteps_le :
    ∀ s1 s2 : List Bool, cmpSteps s1 s2 ≤ s1.length + s2.length + 2
  | [], [] => by simp [cmpSteps]
  | [], _ :: s2 => by simp [cmpSteps]
  | a :: s1, b :: s2 => by
    unfold cmpSteps; split_ifs
    · have ih := cmpSteps_le s1 s2; simp; omega
    · simp [drainFSteps]; omega
  | _ :: s1, [] => by simp [cmpSteps, drainFSteps]

private theorem eval_cmp :
    ∀ s1 s2 : List Bool,
      (flip bind prefTM.step)^[cmpSteps s1 s2] (some (mkCfg (some .cmp) [] [] [] s1 s2 [])) =
        some (mkCfg none [] [] [] [] [] [s1.isPrefixOf s2])
  | [], [] => by
    change prefTM.step (mkCfg (some .cmp) [] [] [] [] [] []) = some (mkCfg none [] [] [] [] [] [true])
    apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  | [], b :: s2 => by
    simp only [cmpSteps, List.isPrefixOf]
    rw [Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .cmp) [] [] [] [] (b :: s2) []) =
        some (mkCfg (some .drainT) [] [] [] [] s2 []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[s2.length + 1]
      (prefTM.step (mkCfg (some .cmp) [] [] [] [] (b :: s2) [])) = _
    rw [hstep]
    exact eval_drainT s2
  | a :: s1, b :: s2 => by
    by_cases hab : a = b
    · subst hab
      simp only [cmpSteps, ↓reduceIte, List.isPrefixOf_cons_cons, beq_self_eq_true, Bool.true_and]
      rw [Function.iterate_succ_apply]
      have hstep : prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) (a :: s2) []) =
          some (mkCfg (some .cmp) [] [] [] s1 s2 []) := by
        cases a <;> (apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl))
      change (flip bind prefTM.step)^[cmpSteps s1 s2]
        (prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) (a :: s2) [])) = _
      rw [hstep]
      exact eval_cmp s1 s2
    · simp only [cmpSteps, hab, ↓reduceIte, List.isPrefixOf_cons_cons, beq_eq_false_iff_ne.mpr hab,
        Bool.false_and]
      rw [Function.iterate_succ_apply]
      have hstep : prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) (b :: s2) []) =
          some (mkCfg (some .drainF) [] [] [] s1 s2 []) := by
        cases a <;> cases b
        · exact absurd rfl hab
        · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
        · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
        · exact absurd rfl hab
      change (flip bind prefTM.step)^[drainFSteps s1 s2]
        (prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) (b :: s2) [])) = _
      rw [hstep]
      exact eval_drainF s1 s2
  | a :: s1, [] => by
    simp only [cmpSteps, List.isPrefixOf_cons_nil]
    rw [Function.iterate_succ_apply]
    have hstep : prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) [] []) =
        some (mkCfg (some .drainF) [] [] [] s1 [] []) := by
      apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
    change (flip bind prefTM.step)^[drainFSteps s1 []]
      (prefTM.step (mkCfg (some .cmp) [] [] [] (a :: s1) [] [])) = _
    rw [hstep]
    exact eval_drainF s1 []

private noncomputable def prefComputable :
    Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2) where
  tm := prefTM
  inputAlphabet := Equiv.refl (Bool ⊕ Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 6
  outputsFun p := by
    rcases p with ⟨x, y⟩
    have hinit : Turing.initList prefTM (List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair (x, y))) =
        mkCfg (some .split) (x.map Sum.inl ++ y.map Sum.inr) [] [] [] [] [] := by
      apply cfg_ext
      · rfl
      · rfl
      · intro k; cases k
        · exact List.map_id _
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
    have hhalt : Option.map (Turing.haltList prefTM)
        (some (List.map (Equiv.refl Bool).invFun (PvsNP.encodeAnswer (x.isPrefixOf y)))) =
        some (mkCfg none [] [] [] [] [] [x.isPrefixOf y]) := by
      apply congrArg some
      apply cfg_ext
      · rfl
      · rfl
      · intro k; cases k <;> rfl
    have h1 := eval_split_inl x (y.map Sum.inr) [] []
    have h2 := eval_split_inr y x.reverse []
    have h3 := eval_rev1 x.reverse y.reverse []
    have h4 := eval_rev2 y.reverse x []
    have h5 := eval_cmp x y
    have hk := cmpSteps_le x y
    refine ⟨⟨cmpSteps x y + ((y.length + 1) + ((x.length + 1) + ((y.length + 1) + x.length))), ?_⟩, ?_⟩
    · rw [hinit, hhalt,
        Function.iterate_add_apply (f := flip bind prefTM.step) (cmpSteps x y),
        Function.iterate_add_apply (f := flip bind prefTM.step) (y.length + 1),
        Function.iterate_add_apply (f := flip bind prefTM.step) (x.length + 1),
        Function.iterate_add_apply (f := flip bind prefTM.step) (y.length + 1)]
      simp only [List.append_nil] at h1 h2
      rw [h1, h2]
      simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3 h4
      rw [h3, h4]
      exact h5
    · simp only [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList, id_eq,
        List.length_append, List.length_map, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega

end PvsNP.Units.m2_prefix_polytime

theorem PvsNP.Units.m2_prefix_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2) :=
  ⟨PvsNP.Units.m2_prefix_polytime.prefComputable⟩
