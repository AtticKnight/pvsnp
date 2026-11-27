import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_tm_filtermap_time_aux

open Turing

theorem update3_fst {ι : Type*} [DecidableEq ι] {β : ι → Type*} (E : ∀ i, β i)
    {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd {ι : Type*} [DecidableEq ι] {β : ι → Type*} (E : ∀ i, β i)
    {a b c : ι} (hbc : b ≠ c) (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

abbrev FΓ : Option Bool → Type
  | some false => Bool
  | none => Option Bool
  | some true => Bool

def fmProg (φ : Bool → Option Bool) : Bool → TM2.Stmt FΓ Bool (Option Bool)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (.push (some true) (fun s => (s.bind φ).getD true) (.goto fun _ => true))
          (.goto fun _ => true))
        .halt)

def fm (φ : Bool → Option Bool) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fmProg φ

def fst3 (l : List Bool) (t : List (Option Bool)) (u : List Bool) : ∀ k, List (FΓ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Bool) (t : List (Option Bool)) (u : List Bool) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Bool) (t : List (Option Bool)) (u : List Bool) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Bool) (t : List (Option Bool)) (u : List Bool) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Bool) (t : List (Option Bool)) (u : List Bool) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Bool) (t t' : List (Option Bool)) (u : List Bool) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Bool) (t : List (Option Bool)) (u u' : List Bool) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Bool) :
    (fst3 l [] [] : ∀ k, List (FΓ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Bool) :
    (fst3 [] [] u : ∀ k, List (FΓ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

abbrev FCfg : Type := TM2.Cfg FΓ Bool (Option Bool)

theorem fmA_cons (φ : Bool → Option Bool) (b : Option Bool) (x : Bool)
    (l : List Bool) (t : List (Option Bool)) (u : List Bool) :
    TM2.step (fmProg φ) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (φ : Bool → Option Bool) (b : Option Bool)
    (t : List (Option Bool)) (u : List Bool) :
    TM2.step (fmProg φ) (⟨some false, b, fst3 [] t u⟩ : FCfg) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (φ : Bool → Option Bool) (b : Option Bool) (x : Bool)
    (t : List (Option Bool)) (u : List Bool) :
    TM2.step (fmProg φ) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    simp only [Option.isSome_some, Bool.cond_true,
      Option.toList_some, List.singleton_append]
    rw [fst3_thd, fst3_set_thd]
    simp

theorem fmB_nil (φ : Bool → Option Bool) (b : Option Bool) (u : List Bool) :
    TM2.step (fmProg φ) (⟨some true, b, fst3 [] [] u⟩ : FCfg) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (φ : Bool → Option Bool) (u : List Bool) :
    ∀ (l : List Bool) (t : List (Option Bool)) (b : Option Bool),
      (flip bind (TM2.step (fmProg φ)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (φ : Bool → Option Bool) :
    ∀ (t : List Bool) (u : List Bool) (b : Option Bool),
      (flip bind (TM2.step (fmProg φ)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run (φ : Bool → Option Bool) (l : List Bool) :
    (flip bind (TM2.step (fmProg φ)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ) l)) = some (haltList (fm φ) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

end PvsNP.Units.m2_tm_filtermap_time_aux

theorem PvsNP.Units.m2_tm_filtermap_time : ∀ φ : Bool → Option Bool, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.filterMap φ), ∀ n : ℕ, M.time n ≤ 2 * n + 3 := by
  intro φ
  refine ⟨{
    tm := PvsNP.Units.m2_tm_filtermap_time_aux.fm φ
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 2 * n + 2
    outputsFun := fun x =>
      { steps := (PvsNP.encodeString x).length + 1 + ((PvsNP.encodeString x).length + 1)
        evals_in_steps := by
          have hm : ∀ (l : List Bool), List.map (Equiv.refl Bool).invFun l = l :=
            fun l => by simp
          have hfm := PvsNP.Units.m2_tm_filtermap_time_aux.fm_run φ (PvsNP.encodeString x)
          have henc : PvsNP.encodeString (x.filterMap φ) = (PvsNP.encodeString x).filterMap φ := rfl
          exact (congrArg (fun l => (flip bind (Turing.TM2.step (PvsNP.Units.m2_tm_filtermap_time_aux.fmProg φ)))^[
            (PvsNP.encodeString x).length + 1 + ((PvsNP.encodeString x).length + 1)]
            (some (Turing.initList (PvsNP.Units.m2_tm_filtermap_time_aux.fm φ) l))) (hm (PvsNP.encodeString x))).trans
            (hfm.trans (congrArg (fun l => some (Turing.haltList (PvsNP.Units.m2_tm_filtermap_time_aux.fm φ) l))
              (henc.symm.trans (hm (PvsNP.encodeString (x.filterMap φ))).symm)))
        steps_le_m := by omega } }, ?_⟩
  intro n
  dsimp only
  omega
