import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_flip_one

open Turing

private theorem flip_bind_some {α : Type} (f : α → Option α) (a : α) :
    flip bind f (some a) = f a := rfl

private theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

private theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

private theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

private theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

private theorem update_singleton_nil {ι : Type} [DecidableEq ι] {β : ι → Type}
    (k : ι) (x : β k) :
    Function.update (Function.update (fun _ => [] : ∀ i, List (β i)) k [x]) k [] =
      fun _ => [] := by
  rw [Function.update_idem, Function.update_eq_self_iff.mpr rfl]

private inductive FK (K : Type) : Type
  | pref
  | suf
  | tmp
  | out
  | s1 (k : K)
  deriving DecidableEq

private instance {K : Type} [Fintype K] : Fintype (FK K) :=
  Fintype.ofEquiv (Fin 4 ⊕ K)
    { toFun := fun x => match x with
        | Sum.inl ⟨0, _⟩ => .pref
        | Sum.inl ⟨1, _⟩ => .suf
        | Sum.inl ⟨2, _⟩ => .tmp
        | Sum.inl ⟨_, _⟩ => .out
        | Sum.inr k => .s1 k
      invFun := fun k => match k with
        | .pref => Sum.inl ⟨0, by decide⟩
        | .suf => Sum.inl ⟨1, by decide⟩
        | .tmp => Sum.inl ⟨2, by decide⟩
        | .out => Sum.inl ⟨3, by decide⟩
        | .s1 k => Sum.inr k
      left_inv := fun x => by
        rcases x with i | k
        · fin_cases i <;> rfl
        · rfl
      right_inv := fun k => by cases k <;> rfl }

private inductive FΛ (Λ : Type) : Type
  | check
  | revSuf
  | loadSuf
  | loadPref
  | restPref
  | fin
  | drain
  | run (l : Λ)
  deriving DecidableEq

private instance {Λ : Type} [Fintype Λ] : Fintype (FΛ Λ) :=
  Fintype.ofEquiv (Fin 7 ⊕ Λ)
    { toFun := fun x => match x with
        | Sum.inl ⟨0, _⟩ => .check
        | Sum.inl ⟨1, _⟩ => .revSuf
        | Sum.inl ⟨2, _⟩ => .loadSuf
        | Sum.inl ⟨3, _⟩ => .loadPref
        | Sum.inl ⟨4, _⟩ => .restPref
        | Sum.inl ⟨5, _⟩ => .fin
        | Sum.inl ⟨_, _⟩ => .drain
        | Sum.inr l => .run l
      invFun := fun l => match l with
        | .check => Sum.inl ⟨0, by decide⟩
        | .revSuf => Sum.inl ⟨1, by decide⟩
        | .loadSuf => Sum.inl ⟨2, by decide⟩
        | .loadPref => Sum.inl ⟨3, by decide⟩
        | .restPref => Sum.inl ⟨4, by decide⟩
        | .fin => Sum.inl ⟨5, by decide⟩
        | .drain => Sum.inl ⟨6, by decide⟩
        | .run l => Sum.inr l
      left_inv := fun x => by
        rcases x with i | l
        · fin_cases i <;> rfl
        · rfl
      right_inv := fun l => by cases l <;> rfl }

section FlipMachine

variable (M : FinTM2)

private abbrev FΓ : FK M.K → Type
  | .pref => Bool
  | .suf => Bool
  | .tmp => Bool
  | .out => Bool
  | .s1 k => M.Γ k

private abbrev Fσ : Type := Bool × Bool × Option Bool × M.σ

private abbrev FCfg : Type := TM2.Cfg (FΓ M) (FΛ M.Λ) (Fσ M)

private def mkS (acc cur : Bool) : Fσ M :=
  (acc, cur, none, M.initialState)

variable {M}

private def tr : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FΓ M) (FΛ M.Λ) (Fσ M)
  | .push k f q => .push (.s1 k) (fun s => f s.2.2.2) (tr q)
  | .peek k f q =>
      .peek (.s1 k) (fun s o => (s.1, s.2.1, s.2.2.1, f s.2.2.2 o)) (tr q)
  | .pop k f q =>
      .pop (.s1 k) (fun s o => (s.1, s.2.1, s.2.2.1, f s.2.2.2 o)) (tr q)
  | .load a q =>
      .load (fun s => (s.1, s.2.1, s.2.2.1, a s.2.2.2)) (tr q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.2) (tr q₁) (tr q₂)
  | .goto f => .goto (fun s => .run (f s.2.2.2))
  | .halt => .goto (fun _ => .fin)

variable (M)
variable (inM : Bool → M.Γ M.k₀) (outM : M.Γ M.k₁ → Bool)

private def fProg : FΛ M.Λ → TM2.Stmt (FΓ M) (FΛ M.Λ) (Fσ M)
  | .check =>
    .pop .suf (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.load (fun s => mkS M s.1 (s.2.2.1.getD false)) (.goto fun _ => .revSuf))
        (.load (fun s => mkS M s.1 false) (.goto fun _ => .drain)))
  | .revSuf =>
    .pop .suf (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .tmp (fun s => s.2.2.1.getD false)
          (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .revSuf)))
        (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .loadSuf)))
  | .loadSuf =>
    .pop .tmp (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .suf (fun s => s.2.2.1.getD false)
          (.push (.s1 M.k₀) (fun s => inM (s.2.2.1.getD false))
            (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .loadSuf))))
        (.push (.s1 M.k₀) (fun s => inM (!s.2.1))
          (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .loadPref))))
  | .loadPref =>
    .pop .pref (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .tmp (fun s => s.2.2.1.getD false)
          (.push (.s1 M.k₀) (fun s => inM (s.2.2.1.getD false))
            (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .loadPref))))
        (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .restPref)))
  | .restPref =>
    .pop .tmp (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .pref (fun s => s.2.2.1.getD false)
          (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .restPref)))
        (.load (fun s => mkS M s.1 s.2.1) (.goto fun _ => .run M.main)))
  | .fin =>
    .pop (.s1 M.k₁) (fun s o => (s.1 || (o.map outM).getD false, s.2.1, none, M.initialState))
      (.push .pref (fun s => s.2.1)
        (.load (fun s => mkS M s.1 false) (.goto fun _ => .check)))
  | .drain =>
    .pop .pref (fun s o => (s.1, false, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.load (fun s => mkS M s.1 false) (.goto fun _ => .drain))
        (.push .out (fun s => s.1)
          (.load (fun _ => mkS M false false) .halt)))
  | .run l => tr (M.m l)

private def flipTM : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := FK M.K
    k₀ := .suf
    k₁ := .out
    Γ := FΓ M
    Λ := FΛ M.Λ
    main := .check
    σ := Fσ M
    initialState := mkS M false false
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := fProg M inM outM }

variable {M}

private def fstk (p s t o : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k, List (FΓ M k)
  | .pref => p
  | .suf => s
  | .tmp => t
  | .out => o
  | .s1 k => S k

private theorem fstk_set_pref (p p' s t o : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (fstk p s t o S) .pref p' = fstk p' s t o S := by
  funext k; cases k <;> rfl

private theorem fstk_set_suf (p s s' t o : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (fstk p s t o S) .suf s' = fstk p s' t o S := by
  funext k; cases k <;> rfl

private theorem fstk_set_tmp (p s t t' o : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (fstk p s t o S) .tmp t' = fstk p s t' o S := by
  funext k; cases k <;> rfl

private theorem fstk_set_out (p s t o o' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (fstk p s t o S) .out o' = fstk p s t o' S := by
  funext k; cases k <;> rfl

private theorem fstk_set_s1 (p s t o : List Bool) (S : ∀ k, List (M.Γ k))
    (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk p s t o S) (.s1 k) x =
      fstk p s t o (Function.update S k x) := by
  funext j
  cases j with
  | pref => rfl
  | suf => rfl
  | tmp => rfl
  | out => rfl
  | s1 j =>
    by_cases h : j = k
    · subst h; simp [fstk]
    · simp [fstk, h]

private theorem initList_flipTM (x : List Bool) :
    initList (flipTM M inM outM) x =
      (⟨some .check, mkS M false false,
        fstk [] x [] [] (fun _ => [])⟩ : FCfg M) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

private theorem haltList_flipTM (o : List Bool) :
    haltList (flipTM M inM outM) o =
      (⟨none, mkS M false false,
        fstk [] [] [] o (fun _ => [])⟩ : FCfg M) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

private def emb (acc cur : Bool) (p s : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    FCfg M :=
  ⟨some (c.l.elim .fin .run), (acc, cur, none, c.var),
    fstk p s [] [] c.stk⟩

private theorem simM (acc cur : Bool) (p s : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ)
    (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (tr q) ((acc, cur, none, v) : Fσ M) (fstk p s [] [] S) =
      emb acc cur p s (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_s1] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_s1] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

private theorem stepM (acc cur : Bool) (p s : List Bool) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : TM2.step M.m c = some c') :
    TM2.step (fProg M inM outM) (emb acc cur p s c) =
      some (emb acc cur p s c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simM acc cur p s (M.m l) v S)

private theorem check_cons (acc : Bool) (p : List Bool) (b : Bool) (s : List Bool) :
    flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .check, mkS M acc false,
          fstk p (b :: s) [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .revSuf, mkS M acc b,
        fstk p s [] [] (fun _ => [])⟩ := by
  rw [flip_bind_some]
  simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_suf,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]

private theorem check_nil (acc : Bool) (p : List Bool) :
    flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .check, mkS M acc false,
          fstk p [] [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .drain, mkS M acc false,
        fstk p [] [] [] (fun _ => [])⟩ := by
  rw [flip_bind_some]
  simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_suf,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, mkS]

private theorem run_revSuf (acc cur : Bool) (p : List Bool) :
    ∀ (s t : List Bool),
      (flip bind (TM2.step (fProg M inM outM)))^[s.length + 1]
          (some (⟨some .revSuf, mkS M acc cur,
            fstk p s t [] (fun _ => [])⟩ : FCfg M)) =
        some ⟨some .loadSuf, mkS M acc cur,
          fstk p [] (s.reverse ++ t) [] (fun _ => [])⟩
  | [], t => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_suf, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, mkS]
  | c :: s, t => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .revSuf, mkS M acc cur,
          fstk p (c :: s) t [] (fun _ => [])⟩ : FCfg M)) =
        some ⟨some .revSuf, mkS M acc cur,
          fstk p s (c :: t) [] (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_suf, fstk_set_tmp,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_revSuf acc cur p s (c :: t)]
    simp

private theorem run_loadSuf (acc cur : Bool) (p : List Bool) :
    ∀ (t s : List Bool) (u1 : List (M.Γ M.k₀)),
      (flip bind (TM2.step (fProg M inM outM)))^[t.length + 1]
          (some (⟨some .loadSuf, mkS M acc cur,
            fstk p s t [] (Function.update (fun _ => []) M.k₀ u1)⟩ : FCfg M)) =
        some ⟨some .loadPref, mkS M acc cur,
          fstk p (t.reverse ++ s) [] []
            (Function.update (fun _ => []) M.k₀ (inM (!cur) :: ((t.map inM).reverse ++ u1)))⟩
  | [], s, u1 => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_tmp, fstk_set_s1,
      Function.update_self, Function.update_idem, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil, mkS]
  | c :: t, s, u1 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .loadSuf, mkS M acc cur,
          fstk p s (c :: t) [] (Function.update (fun _ => []) M.k₀ u1)⟩ : FCfg M)) =
        some ⟨some .loadSuf, mkS M acc cur,
          fstk p (c :: s) t [] (Function.update (fun _ => []) M.k₀ (inM c :: u1))⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_tmp, fstk_set_suf, fstk_set_s1,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_loadSuf acc cur p t (c :: s) (inM c :: u1)]
    simp

private theorem run_loadPref (acc cur : Bool) (s : List Bool) :
    ∀ (p t : List Bool) (u1 : List (M.Γ M.k₀)),
      (flip bind (TM2.step (fProg M inM outM)))^[p.length + 1]
          (some (⟨some .loadPref, mkS M acc cur,
            fstk p s t [] (Function.update (fun _ => []) M.k₀ u1)⟩ : FCfg M)) =
        some ⟨some .restPref, mkS M acc cur,
          fstk [] s (p.reverse ++ t) []
            (Function.update (fun _ => []) M.k₀ ((p.map inM).reverse ++ u1))⟩
  | [], t, u1 => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_pref, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil, mkS]
  | c :: p, t, u1 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .loadPref, mkS M acc cur,
          fstk (c :: p) s t [] (Function.update (fun _ => []) M.k₀ u1)⟩ : FCfg M)) =
        some ⟨some .loadPref, mkS M acc cur,
          fstk p s (c :: t) [] (Function.update (fun _ => []) M.k₀ (inM c :: u1))⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_pref, fstk_set_tmp, fstk_set_s1,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_loadPref acc cur s p (c :: t) (inM c :: u1)]
    simp

private theorem run_restPref (acc cur : Bool) (s : List Bool) (S : ∀ k, List (M.Γ k)) :
    ∀ (t p : List Bool),
      (flip bind (TM2.step (fProg M inM outM)))^[t.length + 1]
          (some (⟨some .restPref, mkS M acc cur,
            fstk p s t [] S⟩ : FCfg M)) =
        some ⟨some (.run M.main), mkS M acc cur,
          fstk (t.reverse ++ p) s [] [] S⟩
  | [], p => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_tmp, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, mkS]
  | c :: t, p => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .restPref, mkS M acc cur,
          fstk p s (c :: t) [] S⟩ : FCfg M)) =
        some ⟨some .restPref, mkS M acc cur,
          fstk (c :: p) s t [] S⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_tmp, fstk_set_pref,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_restPref acc cur s S t (c :: p)]
    simp

private theorem fin_step (acc cur : Bool) (p s : List Bool) (a : M.Γ M.k₁) :
    flip bind (TM2.step (fProg M inM outM))
        (some (emb acc cur p s (haltList M [a]))) =
      some ⟨some .check, mkS M (acc || outM a) false,
        fstk (cur :: p) s [] [] (fun _ => [])⟩ := by
  rw [flip_bind_some, haltList_eq M [a]]
  simp only [emb, Option.elim_none, TM2.step, fProg, TM2.stepAux, fstk, fstk_set_s1,
    fstk_set_pref, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
    Option.getD_some, update_singleton_nil, mkS]

private theorem run_drain (acc : Bool) : ∀ p : List Bool,
    (flip bind (TM2.step (fProg M inM outM)))^[p.length + 1]
        (some (⟨some .drain, mkS M acc false,
          fstk p [] [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨none, mkS M false false,
        fstk [] [] [] [acc] (fun _ => [])⟩
  | [] => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_pref, fstk_set_out,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, mkS]
  | b :: p => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (fProg M inM outM))
        (some (⟨some .drain, mkS M acc false,
          fstk (b :: p) [] [] [] (fun _ => [])⟩ : FCfg M)) =
        some ⟨some .drain, mkS M acc false,
          fstk p [] [] [] (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, fProg, TM2.stepAux, fstk, fstk_set_pref,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, mkS]
    rw [hs, run_drain acc p]

private theorem run_one_round (acc : Bool) (u : List Bool) (b : Bool) (v : List Bool)
    (a : M.Γ M.k₁) (s : ℕ)
    (hm : (flip bind (TM2.step M.m))^[s] (some (initList M ((u ++ (!b) :: v).map inM))) =
      some (haltList M [a])) :
    (flip bind (TM2.step (fProg M inM outM)))^[
        1 + (s + ((u.length + 1) + ((u.length + 1) + ((v.length + 1) + ((v.length + 1) + 1)))))]
        (some (⟨some .check, mkS M acc false,
          fstk u.reverse (b :: v) [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .check, mkS M (acc || outM a) false,
        fstk (u ++ [b]).reverse v [] [] (fun _ => [])⟩ := by
  let step := flip bind (TM2.step (fProg M inM outM))
  have hc := check_cons inM outM acc u.reverse b v
  have hrv := run_revSuf inM outM acc b u.reverse v []
  rw [List.append_nil] at hrv
  have hls := run_loadSuf inM outM acc b u.reverse v.reverse [] []
  rw [Function.update_eq_self_iff.mpr rfl, List.length_reverse, List.reverse_reverse,
    List.append_nil, List.append_nil, ← List.map_reverse, List.reverse_reverse] at hls
  have hlp := run_loadPref inM outM acc b v u.reverse [] (inM (!b) :: v.map inM)
  rw [List.length_reverse, List.reverse_reverse, List.append_nil,
    ← List.map_reverse, List.reverse_reverse] at hlp
  have hmap : u.map inM ++ inM (!b) :: v.map inM = (u ++ (!b) :: v).map inM := by simp
  rw [hmap] at hlp
  have hrp := run_restPref inM outM acc b v
    (Function.update (fun _ => []) M.k₀ ((u ++ (!b) :: v).map inM)) u []
  rw [List.append_nil] at hrp
  have hrp' : step^[u.length + 1]
      (some (⟨some .restPref, mkS M acc b,
        fstk [] v u [] (Function.update (fun _ => []) M.k₀ ((u ++ (!b) :: v).map inM))⟩ :
          FCfg M)) =
      some (emb acc b u.reverse v (initList M ((u ++ (!b) :: v).map inM))) := by
    rw [initList_eq M ((u ++ (!b) :: v).map inM)]
    exact hrp
  have hsim := simulate (TM2.step M.m) (TM2.step (fProg M inM outM))
    (emb acc b u.reverse v) (stepM inM outM acc b u.reverse v) s _ _ hm
  have hfin := fin_step inM outM acc b u.reverse v a
  have hrev : b :: u.reverse = (u ++ [b]).reverse := by simp
  rw [hrev] at hfin
  have p1 : step^[(v.length + 1) + 1]
      (some (⟨some .check, mkS M acc false,
        fstk u.reverse (b :: v) [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .loadSuf, mkS M acc b,
        fstk u.reverse [] v.reverse [] (fun _ => [])⟩ := by
    rw [Function.iterate_add_apply step (v.length + 1) 1, Function.iterate_one]
    exact (congrArg (step^[v.length + 1]) hc).trans hrv
  have p2 : step^[(v.length + 1) + ((v.length + 1) + 1)]
      (some (⟨some .check, mkS M acc false,
        fstk u.reverse (b :: v) [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .loadPref, mkS M acc b,
        fstk u.reverse v [] [] (Function.update (fun _ => []) M.k₀ (inM (!b) :: v.map inM))⟩ := by
    rw [Function.iterate_add_apply step (v.length + 1) _, p1, hls]
  have p3 : step^[(u.length + 1) + ((v.length + 1) + ((v.length + 1) + 1))]
      (some (⟨some .check, mkS M acc false,
        fstk u.reverse (b :: v) [] [] (fun _ => [])⟩ : FCfg M)) =
      some ⟨some .restPref, mkS M acc b,
        fstk [] v u [] (Function.update (fun _ => []) M.k₀ ((u ++ (!b) :: v).map inM))⟩ := by
    rw [Function.iterate_add_apply step (u.length + 1) _, p2, hlp]
  have p4 : step^[(u.length + 1) + ((u.length + 1) + ((v.length + 1) + ((v.length + 1) + 1)))]
      (some (⟨some .check, mkS M acc false,
        fstk u.reverse (b :: v) [] [] (fun _ => [])⟩ : FCfg M)) =
      some (emb acc b u.reverse v (initList M ((u ++ (!b) :: v).map inM))) := by
    rw [Function.iterate_add_apply step (u.length + 1) _, p3, hrp']
  rw [Function.iterate_add_apply step 1 _, Function.iterate_add_apply step s _,
    p4, hsim, Function.iterate_one]
  exact hfin

end FlipMachine

private def flipAny (f : List Bool → Bool) : List Bool → List Bool → Bool
  | _, [] => false
  | u, b :: v => f (u ++ (!b) :: v) || flipAny f (u ++ [b]) v

private theorem flipAny_iff (f : List Bool → Bool) : ∀ (v u : List Bool),
    flipAny f u v = true ↔
      ∃ (w₁ w₂ : List Bool) (b : Bool), v = w₁ ++ b :: w₂ ∧ f (u ++ w₁ ++ (!b) :: w₂) = true
  | [], u => by
    simp only [flipAny, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro w₁ w₂ b h
    cases w₁ <;> simp at h
  | b :: v, u => by
    simp only [flipAny, Bool.or_eq_true, flipAny_iff f v (u ++ [b])]
    constructor
    · rintro (h | ⟨w₁, w₂, c, hv, hf⟩)
      · exact ⟨[], v, b, rfl, by simpa using h⟩
      · refine ⟨b :: w₁, w₂, c, by rw [hv]; rfl, ?_⟩
        simpa [List.append_assoc] using hf
    · rintro ⟨w₁, w₂, c, hv, hf⟩
      cases w₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩
        exact Or.inl (by simpa using hf)
      | cons b' w₁' =>
        simp only [List.cons_append, List.cons.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩
        refine Or.inr ⟨w₁', w₂, c, rfl, ?_⟩
        simpa [List.append_assoc] using hf

private theorem run_flips (f : List Bool → Bool)
    (c : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (n : ℕ) :
    ∀ (v u : List Bool) (acc : Bool), u.length + v.length = n →
      ∃ t, t ≤ v.length * (2 * n + 4 + c.time n) + 1 ∧
        (flip bind (TM2.step (fProg c.tm c.inputAlphabet.invFun c.outputAlphabet)))^[t]
            (some (⟨some .check, mkS c.tm acc false,
              fstk u.reverse v [] [] (fun _ => [])⟩ : FCfg c.tm)) =
          some ⟨some .drain, mkS c.tm (acc || flipAny f u v) false,
            fstk (u ++ v).reverse [] [] [] (fun _ => [])⟩ := by
  let step := flip bind (TM2.step (fProg c.tm c.inputAlphabet.invFun c.outputAlphabet))
  intro v
  induction v with
  | nil =>
    intro u acc _
    refine ⟨1, by simp, ?_⟩
    rw [Function.iterate_one]
    simp only [flipAny, Bool.or_false, List.append_nil]
    exact check_nil c.inputAlphabet.invFun c.outputAlphabet acc u.reverse
  | cons b v ih =>
    intro u acc hlen
    have r := c.outputsFun (u ++ (!b) :: v)
    have hround := run_one_round c.inputAlphabet.invFun c.outputAlphabet acc u b v
      (c.outputAlphabet.invFun (f (u ++ (!b) :: v))) r.steps r.evals_in_steps
    have ho : c.outputAlphabet (c.outputAlphabet.invFun (f (u ++ (!b) :: v))) =
        f (u ++ (!b) :: v) := c.outputAlphabet.right_inv _
    rw [ho] at hround
    have hlen' : (u ++ [b]).length + v.length = n := by simp at hlen ⊢; omega
    obtain ⟨t', ht', hrec⟩ := ih (u ++ [b]) (acc || f (u ++ (!b) :: v)) hlen'
    have hflen : (u ++ (!b) :: v).length = n := by simp at hlen ⊢; omega
    have hr_le : r.steps ≤ c.time n := by
      have hrm : r.steps ≤ c.time (u ++ (!b) :: v).length := r.steps_le_m
      rwa [hflen] at hrm
    set t0 := 1 + (r.steps + ((u.length + 1) + ((u.length + 1) +
        ((v.length + 1) + ((v.length + 1) + 1)))))
    have ht0 : t0 ≤ 2 * n + 4 + c.time n := by
      simp only [t0, List.length_cons] at hlen ⊢
      omega
    refine ⟨t' + t0, ?_, ?_⟩
    · have hmul : (b :: v).length * (2 * n + 4 + c.time n) =
          v.length * (2 * n + 4 + c.time n) + (2 * n + 4 + c.time n) := by
        rw [List.length_cons, Nat.add_mul, one_mul]
      omega
    · rw [Function.iterate_add_apply step t' t0, hround, hrec]
      have hcat : u ++ [b] ++ v = u ++ b :: v := by simp
      rw [hcat, flipAny, Bool.or_assoc]

private noncomputable def flipInTime (f : List Bool → Bool)
    (c : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => flipAny f [] x) where
  tm := flipTM c.tm c.inputAlphabet.invFun c.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => (n + 1) * (2 * n + 6 + c.time n)
  outputsFun x := by
    let step := flip bind (TM2.step (fProg c.tm c.inputAlphabet.invFun c.outputAlphabet))
    let hsp := run_flips f c x.length x [] false (by simp)
    let t := Classical.choose hsp
    have ht : t ≤ x.length * (2 * x.length + 4 + c.time x.length) + 1 :=
      (Classical.choose_spec hsp).1
    have hrun := (Classical.choose_spec hsp).2
    simp only [List.reverse_nil, List.nil_append, Bool.false_or] at hrun
    have hdrain := run_drain c.inputAlphabet.invFun c.outputAlphabet
      (flipAny f [] x) x.reverse
    rw [List.length_reverse] at hdrain
    refine ⟨⟨(x.length + 1) + t, ?_⟩, ?_⟩
    · have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
      refine (congrArg (fun l => step^[(x.length + 1) + t]
          (some (initList (flipTM c.tm c.inputAlphabet.invFun c.outputAlphabet) l))) (hm x)).trans
        ((congrArg (fun cfg => step^[(x.length + 1) + t] (some cfg))
            (initList_flipTM c.inputAlphabet.invFun c.outputAlphabet x)).trans
          (Eq.trans ?_ ((congrArg some (haltList_flipTM c.inputAlphabet.invFun c.outputAlphabet
              [flipAny f [] x]).symm).trans
            (congrArg (fun l => some (haltList (flipTM c.tm c.inputAlphabet.invFun
              c.outputAlphabet) l)) (hm [flipAny f [] x]).symm))))
      exact (Function.iterate_add_apply step (x.length + 1) t _).trans
        ((congrArg (step^[x.length + 1]) hrun).trans hdrain)
    · change (x.length + 1) + t ≤ (x.length + 1) * (2 * x.length + 6 + c.time x.length)
      change t ≤ x.length * (2 * x.length + 4 + c.time x.length) + 1 at ht
      have hexp : (x.length + 1) * (2 * x.length + 6 + c.time x.length) =
          x.length * (2 * x.length + 4 + c.time x.length) +
            4 * x.length + 6 + c.time x.length := by ring
      omega

private theorem exp_flip_bound (k n : ℕ) :
    (n + 1) * (2 * n + 6 + (2 ^ (n ^ k) + k)) ≤
      2 ^ (n ^ (2 * k + 20)) + (2 * k + 20) := by
  let K := 2 * k + 20
  rcases n with _ | _ | m
  · have h1 : 2 ^ (0 ^ k) ≤ 2 := by rcases k with _ | k <;> simp
    have h2 : 0 ^ K = 0 := Nat.zero_pow (by omega)
    show 1 * (6 + (2 ^ (0 ^ k) + k)) ≤ 2 ^ (0 ^ K) + K
    rw [h2]
    omega
  · show 2 * (8 + (2 ^ (1 ^ k) + k)) ≤ 2 ^ (1 ^ K) + K
    simp only [one_pow]
    omega
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    let E := max (N ^ k) (N + 1)
    have hE1 : N ^ k ≤ E := le_max_left _ _
    have hE2 : N + 1 ≤ E := le_max_right _ _
    have hp1 : 2 ^ (N ^ k) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hE1
    have hk : k ≤ 2 ^ E := by
      have a : k < 2 ^ k := Nat.lt_two_pow_self
      have b : 2 ^ k ≤ N ^ k := Nat.pow_le_pow_left hN2 k
      have c : N ^ k < 2 ^ (N ^ k) := Nat.lt_two_pow_self
      omega
    have hN1 : N + 1 ≤ 2 ^ E := by
      have a : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
      have b : 2 ^ (N + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hE2
      omega
    have hlin : 2 * N + 6 ≤ 4 * 2 ^ E := by omega
    have hinner : 2 * N + 6 + (2 ^ (N ^ k) + k) ≤ 8 * 2 ^ E := by omega
    have hprod : (N + 1) * (2 * N + 6 + (2 ^ (N ^ k) + k)) ≤ 2 ^ (2 * E + 3) := by
      calc (N + 1) * (2 * N + 6 + (2 ^ (N ^ k) + k))
          ≤ 2 ^ E * (8 * 2 ^ E) := Nat.mul_le_mul hN1 hinner
        _ = 2 ^ (2 * E + 3) := by
            rw [Nat.pow_add, Nat.two_mul, Nat.pow_add]
            ring
    have hEK : 2 * E + 3 ≤ N ^ K := by
      have hb1 : 2 * N ^ k + 3 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k := Nat.one_le_pow k N (by omega)
        have hcb : 8 ≤ N ^ 3 := by
          have : 2 ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN2 3
          omega
        have hmul : 8 * N ^ k ≤ N ^ 3 * N ^ k := Nat.mul_le_mul_right _ hcb
        have hpk : N ^ 3 * N ^ k = N ^ (k + 3) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k + 3) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : 2 * (N + 1) + 3 ≤ N ^ K := by
        have h4 : 2 * N + 5 ≤ N ^ 4 := by
          have hc : N ^ 4 = N * N * (N * N) := by ring
          rw [hc]
          have hsq : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmon : N ^ 4 ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp only [E, max_def]
      split_ifs <;> omega
    have hpowK : 2 ^ (2 * E + 3) ≤ 2 ^ (N ^ K) := Nat.pow_le_pow_right (by omega) hEK
    show (N + 1) * (2 * N + 6 + (2 ^ (N ^ k) + k)) ≤ 2 ^ (N ^ K) + K
    omega

private theorem exp_flip_one (L : Language Bool)
    (h : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L) ↔
        f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨k, f, M, hf, ht⟩ := h
  refine ⟨2 * k + 20, fun x => flipAny f [] x, flipInTime f M, fun x => ?_, fun n => ?_⟩
  · rw [flipAny_iff]
    simp only [List.nil_append, hf]
  · have hmul : (n + 1) * (2 * n + 6 + M.time n) ≤ (n + 1) * (2 * n + 6 + (2 ^ (n ^ k) + k)) :=
      Nat.mul_le_mul_left (n + 1) (by have := ht n; omega)
    exact hmul.trans (exp_flip_bound k n)

end PvsNP.Units.tc_exp_flip_one

theorem PvsNP.Units.tc_exp_flip_one :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L) ↔
            f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_flip_one.exp_flip_one
