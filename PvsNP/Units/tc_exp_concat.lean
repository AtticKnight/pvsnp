import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_concat

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

private inductive CK (K1 K2 : Type) : Type
  | pref
  | suf
  | tmp
  | out
  | s1 (k : K1)
  | s2 (k : K2)
  deriving DecidableEq

private instance {K1 K2 : Type} [Fintype K1] [Fintype K2] : Fintype (CK K1 K2) :=
  Fintype.ofEquiv (Fin 4 ⊕ K1 ⊕ K2)
    { toFun := fun x => match x with
        | Sum.inl ⟨0, _⟩ => .pref
        | Sum.inl ⟨1, _⟩ => .suf
        | Sum.inl ⟨2, _⟩ => .tmp
        | Sum.inl ⟨_, _⟩ => .out
        | Sum.inr (Sum.inl k) => .s1 k
        | Sum.inr (Sum.inr k) => .s2 k
      invFun := fun k => match k with
        | .pref => Sum.inl ⟨0, by decide⟩
        | .suf => Sum.inl ⟨1, by decide⟩
        | .tmp => Sum.inl ⟨2, by decide⟩
        | .out => Sum.inl ⟨3, by decide⟩
        | .s1 k => Sum.inr (Sum.inl k)
        | .s2 k => Sum.inr (Sum.inr k)
      left_inv := fun x => by
        rcases x with i | k | k
        · fin_cases i <;> rfl
        · rfl
        · rfl
      right_inv := fun k => by cases k <;> rfl }

private inductive CΛ (Λ1 Λ2 : Type) : Type
  | load1
  | rest1
  | fin1
  | rev2
  | load2
  | fin2
  | adv
  | drain
  | run1 (l : Λ1)
  | run2 (l : Λ2)
  deriving DecidableEq

private instance {Λ1 Λ2 : Type} [Fintype Λ1] [Fintype Λ2] : Fintype (CΛ Λ1 Λ2) :=
  Fintype.ofEquiv (Fin 8 ⊕ Λ1 ⊕ Λ2)
    { toFun := fun x => match x with
        | Sum.inl ⟨0, _⟩ => .load1
        | Sum.inl ⟨1, _⟩ => .rest1
        | Sum.inl ⟨2, _⟩ => .fin1
        | Sum.inl ⟨3, _⟩ => .rev2
        | Sum.inl ⟨4, _⟩ => .load2
        | Sum.inl ⟨5, _⟩ => .fin2
        | Sum.inl ⟨6, _⟩ => .adv
        | Sum.inl ⟨_, _⟩ => .drain
        | Sum.inr (Sum.inl l) => .run1 l
        | Sum.inr (Sum.inr l) => .run2 l
      invFun := fun l => match l with
        | .load1 => Sum.inl ⟨0, by decide⟩
        | .rest1 => Sum.inl ⟨1, by decide⟩
        | .fin1 => Sum.inl ⟨2, by decide⟩
        | .rev2 => Sum.inl ⟨3, by decide⟩
        | .load2 => Sum.inl ⟨4, by decide⟩
        | .fin2 => Sum.inl ⟨5, by decide⟩
        | .adv => Sum.inl ⟨6, by decide⟩
        | .drain => Sum.inl ⟨7, by decide⟩
        | .run1 l => Sum.inr (Sum.inl l)
        | .run2 l => Sum.inr (Sum.inr l)
      left_inv := fun x => by
        rcases x with i | l | l
        · fin_cases i <;> rfl
        · rfl
        · rfl
      right_inv := fun l => by cases l <;> rfl }

section ConcatMachine

variable (M1 M2 : FinTM2)

private abbrev CΓ : CK M1.K M2.K → Type
  | .pref => Bool
  | .suf => Bool
  | .tmp => Bool
  | .out => Bool
  | .s1 k => M1.Γ k
  | .s2 k => M2.Γ k

private abbrev Cσ : Type := Bool × Bool × Option Bool × M1.σ × M2.σ

private abbrev CCfg : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1.Λ M2.Λ) (Cσ M1 M2)

private def mkS (acc res1 : Bool) : Cσ M1 M2 :=
  (acc, res1, none, M1.initialState, M2.initialState)

variable {M1 M2}

private def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1.Λ M2.Λ) (Cσ M1 M2)
  | .push k f q => .push (.s1 k) (fun s => f s.2.2.2.1) (tr1 q)
  | .peek k f q =>
      .peek (.s1 k) (fun s o => (s.1, s.2.1, s.2.2.1, f s.2.2.2.1 o, s.2.2.2.2)) (tr1 q)
  | .pop k f q =>
      .pop (.s1 k) (fun s o => (s.1, s.2.1, s.2.2.1, f s.2.2.2.1 o, s.2.2.2.2)) (tr1 q)
  | .load a q =>
      .load (fun s => (s.1, s.2.1, s.2.2.1, a s.2.2.2.1, s.2.2.2.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.2.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => .run1 (f s.2.2.2.1))
  | .halt => .goto (fun _ => .fin1)

private def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1.Λ M2.Λ) (Cσ M1 M2)
  | .push k f q => .push (.s2 k) (fun s => f s.2.2.2.2) (tr2 q)
  | .peek k f q =>
      .peek (.s2 k) (fun s o => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, f s.2.2.2.2 o)) (tr2 q)
  | .pop k f q =>
      .pop (.s2 k) (fun s o => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, f s.2.2.2.2 o)) (tr2 q)
  | .load a q =>
      .load (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, a s.2.2.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.2.2) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => .run2 (f s.2.2.2.2))
  | .halt => .goto (fun _ => .fin2)

variable (M1 M2)
variable (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
variable (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)

private def cProg : CΛ M1.Λ M2.Λ → TM2.Stmt (CΓ M1 M2) (CΛ M1.Λ M2.Λ) (Cσ M1 M2)
  | .load1 =>
    .pop .pref (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .tmp (fun s => s.2.2.1.getD false)
          (.push (.s1 M1.k₀) (fun s => in1 (s.2.2.1.getD false))
            (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .load1))))
        (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .rest1)))
  | .rest1 =>
    .pop .tmp (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .pref (fun s => s.2.2.1.getD false)
          (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .rest1)))
        (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .run1 M1.main)))
  | .fin1 =>
    .pop (.s1 M1.k₁) (fun s o => (s.1, (o.map out1).getD false, none, M1.initialState, M2.initialState))
      (.goto fun _ => .rev2)
  | .rev2 =>
    .pop .suf (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .tmp (fun s => s.2.2.1.getD false)
          (.load (fun s => mkS M1 M2 s.1 s.2.1) (.goto fun _ => .rev2)))
        (.load (fun s => mkS M1 M2 s.1 s.2.1) (.goto fun _ => .load2)))
  | .load2 =>
    .pop .tmp (fun s o => (s.1, s.2.1, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .suf (fun s => s.2.2.1.getD false)
          (.push (.s2 M2.k₀) (fun s => in2 (s.2.2.1.getD false))
            (.load (fun s => mkS M1 M2 s.1 s.2.1) (.goto fun _ => .load2))))
        (.load (fun s => mkS M1 M2 s.1 s.2.1) (.goto fun _ => .run2 M2.main)))
  | .fin2 =>
    .pop (.s2 M2.k₁) (fun s o =>
        (s.1 || (s.2.1 && (o.map out2).getD false), false, none, M1.initialState, M2.initialState))
      (.goto fun _ => .adv)
  | .adv =>
    .pop .suf (fun s o => (s.1, false, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.push .pref (fun s => s.2.2.1.getD false)
          (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .load1)))
        (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .drain)))
  | .drain =>
    .pop .pref (fun s o => (s.1, false, o, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.load (fun s => mkS M1 M2 s.1 false) (.goto fun _ => .drain))
        (.push .out (fun s => s.1)
          (.load (fun _ => mkS M1 M2 false false) .halt)))
  | .run1 l => tr1 (M1.m l)
  | .run2 l => tr2 (M2.m l)

private def concatTM : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  { K := CK M1.K M2.K
    k₀ := .suf
    k₁ := .out
    Γ := CΓ M1 M2
    Λ := CΛ M1.Λ M2.Λ
    main := .load1
    σ := Cσ M1 M2
    initialState := mkS M1 M2 false false
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := cProg M1 M2 in1 out1 in2 out2 }

variable {M1 M2}

private def cstk (p s t o : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    ∀ k, List (CΓ M1 M2 k)
  | .pref => p
  | .suf => s
  | .tmp => t
  | .out => o
  | .s1 k => S1 k
  | .s2 k => S2 k

private theorem cstk_set_pref (p p' s t o : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (cstk p s t o S1 S2) .pref p' = cstk p' s t o S1 S2 := by
  funext k; cases k <;> rfl

private theorem cstk_set_suf (p s s' t o : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (cstk p s t o S1 S2) .suf s' = cstk p s' t o S1 S2 := by
  funext k; cases k <;> rfl

private theorem cstk_set_tmp (p s t t' o : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (cstk p s t o S1 S2) .tmp t' = cstk p s t' o S1 S2 := by
  funext k; cases k <;> rfl

private theorem cstk_set_out (p s t o o' : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (cstk p s t o S1 S2) .out o' = cstk p s t o' S1 S2 := by
  funext k; cases k <;> rfl

private theorem cstk_set_s1 (p s t o : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    Function.update (cstk p s t o S1 S2) (.s1 k) x =
      cstk p s t o (Function.update S1 k x) S2 := by
  funext j
  cases j with
  | pref => rfl
  | suf => rfl
  | tmp => rfl
  | out => rfl
  | s2 _ => rfl
  | s1 j =>
    by_cases h : j = k
    · subst h; simp [cstk]
    · simp [cstk, h]

private theorem cstk_set_s2 (p s t o : List Bool) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    Function.update (cstk p s t o S1 S2) (.s2 k) x =
      cstk p s t o S1 (Function.update S2 k x) := by
  funext j
  cases j with
  | pref => rfl
  | suf => rfl
  | tmp => rfl
  | out => rfl
  | s1 _ => rfl
  | s2 j =>
    by_cases h : j = k
    · subst h; simp [cstk]
    · simp [cstk, h]

private theorem initList_concatTM (x : List Bool) :
    initList (concatTM M1 M2 in1 out1 in2 out2) x =
      (⟨some .load1, mkS M1 M2 false false,
        cstk [] x [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

private theorem haltList_concatTM (o : List Bool) :
    haltList (concatTM M1 M2 in1 out1 in2 out2) o =
      (⟨none, mkS M1 M2 false false,
        cstk [] [] [] o (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

private def emb1 (acc res1 : Bool) (p s : List Bool) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    CCfg M1 M2 :=
  ⟨some (c.l.elim .fin1 .run1), (acc, res1, none, c.var, M2.initialState),
    cstk p s [] [] c.stk (fun _ => [])⟩

private def emb2 (acc res1 : Bool) (p s : List Bool) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    CCfg M1 M2 :=
  ⟨some (c.l.elim .fin2 .run2), (acc, res1, none, M1.initialState, c.var),
    cstk p s [] [] (fun _ => []) c.stk⟩

private theorem sim1 (acc res1 : Bool) (p s : List Bool) (q : TM2.Stmt M1.Γ M1.Λ M1.σ)
    (v : M1.σ) (S1 : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((acc, res1, none, v, M2.initialState) : Cσ M1 M2)
        (cstk p s [] [] S1 (fun _ => [])) =
      emb1 acc res1 p s (TM2.stepAux q v S1) := by
  induction q generalizing v S1 with
  | push k f q ih =>
    have := ih v (Function.update S1 k (f v :: S1 k))
    rw [← cstk_set_s1] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S1 k).head?) (Function.update S1 k (S1 k).tail)
    rw [← cstk_set_s1] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S1
    · exact ih₁ v S1
  | goto f => rfl
  | halt => rfl

private theorem sim2 (acc res1 : Bool) (p s : List Bool) (q : TM2.Stmt M2.Γ M2.Λ M2.σ)
    (v : M2.σ) (S2 : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((acc, res1, none, M1.initialState, v) : Cσ M1 M2)
        (cstk p s [] [] (fun _ => []) S2) =
      emb2 acc res1 p s (TM2.stepAux q v S2) := by
  induction q generalizing v S2 with
  | push k f q ih =>
    have := ih v (Function.update S2 k (f v :: S2 k))
    rw [← cstk_set_s2] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S2 k).head?) (Function.update S2 k (S2 k).tail)
    rw [← cstk_set_s2] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S2
    · exact ih₁ v S2
  | goto f => rfl
  | halt => rfl

private theorem step1 (acc res1 : Bool) (p s : List Bool) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (cProg M1 M2 in1 out1 in2 out2) (emb1 acc res1 p s c) =
      some (emb1 acc res1 p s c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 acc res1 p s (M1.m l) v S)

private theorem step2 (acc res1 : Bool) (p s : List Bool) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (cProg M1 M2 in1 out1 in2 out2) (emb2 acc res1 p s c) =
      some (emb2 acc res1 p s c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 acc res1 p s (M2.m l) v S)

private theorem run_load1 (acc : Bool) (s : List Bool) :
    ∀ (p t : List Bool) (u1 : List (M1.Γ M1.k₀)),
      (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[p.length + 1]
          (some (⟨some .load1, mkS M1 M2 acc false,
            cstk p s t [] (Function.update (fun _ => []) M1.k₀ u1) (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some .rest1, mkS M1 M2 acc false,
          cstk [] s (p.reverse ++ t) []
            (Function.update (fun _ => []) M1.k₀ ((p.map in1).reverse ++ u1)) (fun _ => [])⟩
  | [], t, u1 => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_pref, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil, mkS]
  | b :: p, t, u1 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .load1, mkS M1 M2 acc false,
          cstk (b :: p) s t [] (Function.update (fun _ => []) M1.k₀ u1) (fun _ => [])⟩ :
            CCfg M1 M2)) =
        some ⟨some .load1, mkS M1 M2 acc false,
          cstk p s (b :: t) [] (Function.update (fun _ => []) M1.k₀ (in1 b :: u1))
            (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_pref, cstk_set_tmp, cstk_set_s1,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_load1 acc s p (b :: t) (in1 b :: u1)]
    simp

private theorem run_rest1 (acc : Bool) (s : List Bool) (S1 : ∀ k, List (M1.Γ k)) :
    ∀ (t p : List Bool),
      (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[t.length + 1]
          (some (⟨some .rest1, mkS M1 M2 acc false,
            cstk p s t [] S1 (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some (.run1 M1.main), mkS M1 M2 acc false,
          cstk (t.reverse ++ p) s [] [] S1 (fun _ => [])⟩
  | [], p => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_tmp, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, mkS]
  | b :: t, p => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .rest1, mkS M1 M2 acc false,
          cstk p s (b :: t) [] S1 (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some .rest1, mkS M1 M2 acc false,
          cstk (b :: p) s t [] S1 (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_tmp, cstk_set_pref,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_rest1 acc s S1 t (b :: p)]
    simp

private theorem fin1_step (acc : Bool) (p s : List Bool) (a : M1.Γ M1.k₁) :
    flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (emb1 acc false p s (haltList M1 [a]))) =
      some ⟨some .rev2, mkS M1 M2 acc (out1 a),
        cstk p s [] [] (fun _ => []) (fun _ => [])⟩ := by
  rw [flip_bind_some, haltList_eq M1 [a]]
  simp only [emb1, Option.elim_none, TM2.step, cProg, TM2.stepAux, cstk, cstk_set_s1,
    Function.update_self, List.head?_cons, List.tail_cons, Option.map_some, Option.getD_some,
    update_singleton_nil, mkS]

private theorem run_rev2 (acc res1 : Bool) (p : List Bool) :
    ∀ (s t : List Bool),
      (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[s.length + 1]
          (some (⟨some .rev2, mkS M1 M2 acc res1,
            cstk p s t [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some .load2, mkS M1 M2 acc res1,
          cstk p [] (s.reverse ++ t) [] (fun _ => []) (fun _ => [])⟩
  | [], t => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_suf, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, mkS]
  | b :: s, t => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .rev2, mkS M1 M2 acc res1,
          cstk p (b :: s) t [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some .rev2, mkS M1 M2 acc res1,
          cstk p s (b :: t) [] (fun _ => []) (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_suf, cstk_set_tmp,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_rev2 acc res1 p s (b :: t)]
    simp

private theorem run_load2 (acc res1 : Bool) (p : List Bool) :
    ∀ (t s : List Bool) (u2 : List (M2.Γ M2.k₀)),
      (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[t.length + 1]
          (some (⟨some .load2, mkS M1 M2 acc res1,
            cstk p s t [] (fun _ => []) (Function.update (fun _ => []) M2.k₀ u2)⟩ : CCfg M1 M2)) =
        some ⟨some (.run2 M2.main), mkS M1 M2 acc res1,
          cstk p (t.reverse ++ s) [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₀ ((t.map in2).reverse ++ u2))⟩
  | [], s, u2 => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_tmp, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil, mkS]
  | b :: t, s, u2 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .load2, mkS M1 M2 acc res1,
          cstk p s (b :: t) [] (fun _ => []) (Function.update (fun _ => []) M2.k₀ u2)⟩ :
            CCfg M1 M2)) =
        some ⟨some .load2, mkS M1 M2 acc res1,
          cstk p (b :: s) t [] (fun _ => []) (Function.update (fun _ => []) M2.k₀ (in2 b :: u2))⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_tmp, cstk_set_suf, cstk_set_s2,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]
    rw [hs, run_load2 acc res1 p t (b :: s) (in2 b :: u2)]
    simp

private theorem fin2_step (acc res1 : Bool) (p s : List Bool) (a : M2.Γ M2.k₁) :
    flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (emb2 acc res1 p s (haltList M2 [a]))) =
      some ⟨some .adv, mkS M1 M2 (acc || (res1 && out2 a)) false,
        cstk p s [] [] (fun _ => []) (fun _ => [])⟩ := by
  rw [flip_bind_some, haltList_eq M2 [a]]
  simp only [emb2, Option.elim_none, TM2.step, cProg, TM2.stepAux, cstk, cstk_set_s2,
    Function.update_self, List.head?_cons, List.tail_cons, Option.map_some, Option.getD_some,
    update_singleton_nil, mkS]

private theorem adv_cons (acc : Bool) (p : List Bool) (b : Bool) (s : List Bool) :
    flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .adv, mkS M1 M2 acc false,
          cstk p (b :: s) [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some ⟨some .load1, mkS M1 M2 acc false,
        cstk (b :: p) s [] [] (fun _ => []) (fun _ => [])⟩ := by
  rw [flip_bind_some]
  simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_suf, cstk_set_pref,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some, mkS]

private theorem adv_nil (acc : Bool) (p : List Bool) :
    flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .adv, mkS M1 M2 acc false,
          cstk p [] [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some ⟨some .drain, mkS M1 M2 acc false,
        cstk p [] [] [] (fun _ => []) (fun _ => [])⟩ := by
  rw [flip_bind_some]
  simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_suf,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, mkS]

private theorem run_drain (acc : Bool) : ∀ p : List Bool,
    (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[p.length + 1]
        (some (⟨some .drain, mkS M1 M2 acc false,
          cstk p [] [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some ⟨none, mkS M1 M2 false false,
        cstk [] [] [] [acc] (fun _ => []) (fun _ => [])⟩
  | [] => by
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_pref, cstk_set_out,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, mkS]
  | b :: p => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
        (some (⟨some .drain, mkS M1 M2 acc false,
          cstk (b :: p) [] [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
        some ⟨some .drain, mkS M1 M2 acc false,
          cstk p [] [] [] (fun _ => []) (fun _ => [])⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, cProg, TM2.stepAux, cstk, cstk_set_pref,
        List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, mkS]
    rw [hs, run_drain acc p]

private theorem run_one_round (acc : Bool) (u v : List Bool)
    (a1 : M1.Γ M1.k₁) (s1 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 (u.map in1))) =
      some (haltList M1 [a1]))
    (a2 : M2.Γ M2.k₁) (s2 : ℕ)
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (v.map in2))) =
      some (haltList M2 [a2])) :
    (flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2)))^[
        1 + (s2 + ((v.length + 1) + ((v.length + 1) +
          (1 + (s1 + ((u.length + 1) + (u.length + 1)))))))]
        (some (⟨some .load1, mkS M1 M2 acc false,
          cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some ⟨some .adv, mkS M1 M2 (acc || (out1 a1 && out2 a2)) false,
        cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ := by
  let step := flip bind (TM2.step (cProg M1 M2 in1 out1 in2 out2))
  have hl1 := run_load1 in1 out1 in2 out2 acc v u.reverse [] []
  rw [Function.update_eq_self_iff.mpr rfl, List.length_reverse, List.reverse_reverse,
    List.append_nil, List.append_nil, ← List.map_reverse, List.reverse_reverse] at hl1
  have hr1 := run_rest1 in1 out1 in2 out2 acc v (Function.update (fun _ => []) M1.k₀ (u.map in1)) u []
  rw [List.append_nil] at hr1
  have hr1' : step^[u.length + 1]
      (some (⟨some .rest1, mkS M1 M2 acc false,
        cstk [] v u [] (Function.update (fun _ => []) M1.k₀ (u.map in1)) (fun _ => [])⟩ :
          CCfg M1 M2)) =
      some (emb1 acc false u.reverse v (initList M1 (u.map in1))) := by
    rw [initList_eq M1 (u.map in1)]
    exact hr1
  have hm1 := simulate (TM2.step M1.m) (TM2.step (cProg M1 M2 in1 out1 in2 out2))
    (emb1 acc false u.reverse v) (step1 in1 out1 in2 out2 acc false u.reverse v) s1 _ _ h1
  have hf1 := fin1_step in1 out1 in2 out2 acc u.reverse v a1
  have hv2 := run_rev2 in1 out1 in2 out2 acc (out1 a1) u.reverse v []
  rw [List.append_nil] at hv2
  have hl2 := run_load2 in1 out1 in2 out2 acc (out1 a1) u.reverse v.reverse [] []
  rw [Function.update_eq_self_iff.mpr rfl, List.length_reverse, List.reverse_reverse,
    List.append_nil, List.append_nil, ← List.map_reverse, List.reverse_reverse] at hl2
  have hl2' : step^[v.length + 1]
      (some (⟨some .load2, mkS M1 M2 acc (out1 a1),
        cstk u.reverse [] v.reverse [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some (emb2 acc (out1 a1) u.reverse v (initList M2 (v.map in2))) := by
    rw [initList_eq M2 (v.map in2)]
    exact hl2
  have hm2 := simulate (TM2.step M2.m) (TM2.step (cProg M1 M2 in1 out1 in2 out2))
    (emb2 acc (out1 a1) u.reverse v) (step2 in1 out1 in2 out2 acc (out1 a1) u.reverse v) s2 _ _ h2
  have hf2 := fin2_step in1 out1 in2 out2 acc (out1 a1) u.reverse v a2
  have p1 : step^[(u.length + 1) + (u.length + 1)]
      (some (⟨some .load1, mkS M1 M2 acc false,
        cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some (emb1 acc false u.reverse v (initList M1 (u.map in1))) := by
    rw [Function.iterate_add_apply step (u.length + 1) (u.length + 1), hl1, hr1']
  have p2 : step^[1 + (s1 + ((u.length + 1) + (u.length + 1)))]
      (some (⟨some .load1, mkS M1 M2 acc false,
        cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some ⟨some .rev2, mkS M1 M2 acc (out1 a1),
        cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ := by
    rw [Function.iterate_add_apply step 1 _, Function.iterate_add_apply step s1 _,
      p1, hm1, Function.iterate_one]
    exact hf1
  have p3 : step^[(v.length + 1) + ((v.length + 1) + (1 + (s1 + ((u.length + 1) + (u.length + 1)))))]
      (some (⟨some .load1, mkS M1 M2 acc false,
        cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ : CCfg M1 M2)) =
      some (emb2 acc (out1 a1) u.reverse v (initList M2 (v.map in2))) := by
    rw [Function.iterate_add_apply step (v.length + 1) _,
      Function.iterate_add_apply step (v.length + 1) _,
      p2, hv2, hl2']
  rw [Function.iterate_add_apply step 1 _, Function.iterate_add_apply step s2 _,
    p3, hm2, Function.iterate_one]
  exact hf2

end ConcatMachine

private def splitAny (f1 f2 : List Bool → Bool) : List Bool → List Bool → Bool
  | u, [] => f1 u && f2 []
  | u, b :: v => (f1 u && f2 (b :: v)) || splitAny f1 f2 (u ++ [b]) v

private theorem splitAny_iff (f1 f2 : List Bool → Bool) : ∀ (v u : List Bool),
    splitAny f1 f2 u v = true ↔
      ∃ w₁ w₂ : List Bool, v = w₁ ++ w₂ ∧ f1 (u ++ w₁) = true ∧ f2 w₂ = true
  | [], u => by
    simp only [splitAny, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨[], [], rfl, by simpa using h1, h2⟩
    · rintro ⟨w₁, w₂, hnil, h1, h2⟩
      have hw : w₁ = [] ∧ w₂ = [] := List.append_eq_nil_iff.mp hnil.symm
      rcases hw with ⟨rfl, rfl⟩
      exact ⟨by simpa using h1, h2⟩
  | b :: v, u => by
    simp only [splitAny, Bool.or_eq_true, Bool.and_eq_true, splitAny_iff f1 f2 v (u ++ [b])]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨w₁, w₂, hv, h1, h2⟩)
      · exact ⟨[], b :: v, rfl, by simpa using h1, h2⟩
      · refine ⟨b :: w₁, w₂, by rw [hv]; rfl, ?_, h2⟩
        simpa [List.append_assoc] using h1
    · rintro ⟨w₁, w₂, hv, h1, h2⟩
      cases w₁ with
      | nil =>
        simp only [List.nil_append] at hv
        subst hv
        exact Or.inl ⟨by simpa using h1, h2⟩
      | cons b' w₁' =>
        simp only [List.cons_append, List.cons.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩
        refine Or.inr ⟨w₁', w₂, rfl, ?_, h2⟩
        simpa [List.append_assoc] using h1

private theorem run_splits (f1 f2 : List Bool → Bool)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2)
    (n : ℕ) :
    ∀ (v u : List Bool) (acc : Bool), u.length + v.length = n →
      ∃ t, t ≤ (v.length + 1) * (2 * n + 7 +
          (Finset.range (n + 1)).sup c1.time + (Finset.range (n + 1)).sup c2.time) ∧
        (flip bind (TM2.step (cProg c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
            c2.inputAlphabet.invFun c2.outputAlphabet)))^[t]
            (some (⟨some .load1, mkS c1.tm c2.tm acc false,
              cstk u.reverse v [] [] (fun _ => []) (fun _ => [])⟩ : CCfg c1.tm c2.tm)) =
          some ⟨some .drain, mkS c1.tm c2.tm (acc || splitAny f1 f2 u v) false,
            cstk (u ++ v).reverse [] [] [] (fun _ => []) (fun _ => [])⟩ := by
  let step := flip bind (TM2.step (cProg c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet))
  let B1 := (Finset.range (n + 1)).sup c1.time
  let B2 := (Finset.range (n + 1)).sup c2.time
  intro v
  induction v with
  | nil =>
    intro u acc hlen
    have r1 := c1.outputsFun u
    have r2 := c2.outputsFun []
    have hround := run_one_round c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet acc u []
      (c1.outputAlphabet.invFun (f1 u)) r1.steps r1.evals_in_steps
      (c2.outputAlphabet.invFun (f2 [])) r2.steps r2.evals_in_steps
    have ho1 : c1.outputAlphabet (c1.outputAlphabet.invFun (f1 u)) = f1 u :=
      c1.outputAlphabet.right_inv (f1 u)
    have ho2 : c2.outputAlphabet (c2.outputAlphabet.invFun (f2 [])) = f2 [] :=
      c2.outputAlphabet.right_inv (f2 [])
    rw [ho1, ho2] at hround
    have hadv := adv_nil c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet (acc || (f1 u && f2 [])) u.reverse
    have hr1_le : r1.steps ≤ c1.time u.length := r1.steps_le_m
    have hr2_le : r2.steps ≤ c2.time 0 := r2.steps_le_m
    have hb1 : r1.steps ≤ B1 :=
      hr1_le.trans (Finset.le_sup (f := c1.time) (Finset.mem_range.mpr (by simp at hlen; omega)))
    have hb2 : r2.steps ≤ B2 :=
      hr2_le.trans (Finset.le_sup (f := c2.time) (Finset.mem_range.mpr (by omega)))
    refine ⟨1 + (1 + (r2.steps + ((([] : List Bool).length + 1) + ((([] : List Bool).length + 1) +
        (1 + (r1.steps + ((u.length + 1) + (u.length + 1)))))))), ?_, ?_⟩
    · change 1 + (1 + (r2.steps + ((([] : List Bool).length + 1) + ((([] : List Bool).length + 1) +
          (1 + (r1.steps + ((u.length + 1) + (u.length + 1)))))))) ≤
        (([] : List Bool).length + 1) * (2 * n + 7 + B1 + B2)
      simp only [List.length_nil] at hlen ⊢
      omega
    · rw [Function.iterate_add_apply step 1 _, hround, Function.iterate_one]
      simp only [splitAny, List.append_nil]
      exact hadv
  | cons b v ih =>
    intro u acc hlen
    have r1 := c1.outputsFun u
    have r2 := c2.outputsFun (b :: v)
    have hround := run_one_round c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet acc u (b :: v)
      (c1.outputAlphabet.invFun (f1 u)) r1.steps r1.evals_in_steps
      (c2.outputAlphabet.invFun (f2 (b :: v))) r2.steps r2.evals_in_steps
    have ho1 : c1.outputAlphabet (c1.outputAlphabet.invFun (f1 u)) = f1 u :=
      c1.outputAlphabet.right_inv (f1 u)
    have ho2 : c2.outputAlphabet (c2.outputAlphabet.invFun (f2 (b :: v))) = f2 (b :: v) :=
      c2.outputAlphabet.right_inv (f2 (b :: v))
    rw [ho1, ho2] at hround
    have hadv := adv_cons c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet (acc || (f1 u && f2 (b :: v))) u.reverse b v
    have hrev : b :: u.reverse = (u ++ [b]).reverse := by simp
    rw [hrev] at hadv
    have hlen' : (u ++ [b]).length + v.length = n := by simp at hlen ⊢; omega
    obtain ⟨t', ht', hrec⟩ := ih (u ++ [b]) (acc || (f1 u && f2 (b :: v))) hlen'
    have hr1_le : r1.steps ≤ c1.time u.length := r1.steps_le_m
    have hr2_le : r2.steps ≤ c2.time (b :: v).length := r2.steps_le_m
    have hb1 : r1.steps ≤ B1 :=
      hr1_le.trans (Finset.le_sup (f := c1.time) (Finset.mem_range.mpr (by omega)))
    have hb2 : r2.steps ≤ B2 :=
      hr2_le.trans (Finset.le_sup (f := c2.time) (Finset.mem_range.mpr (by omega)))
    set t0 := 1 + (1 + (r2.steps + (((b :: v).length + 1) + (((b :: v).length + 1) +
        (1 + (r1.steps + ((u.length + 1) + (u.length + 1))))))))
    have ht0 : t0 ≤ 2 * n + 7 + B1 + B2 := by
      simp only [t0, List.length_cons] at hlen ⊢
      omega
    refine ⟨t' + t0, ?_, ?_⟩
    · change t' + t0 ≤ ((b :: v).length + 1) * (2 * n + 7 + B1 + B2)
      change t' ≤ (v.length + 1) * (2 * n + 7 + B1 + B2) at ht'
      have hmul : ((b :: v).length + 1) * (2 * n + 7 + B1 + B2) =
          (v.length + 1) * (2 * n + 7 + B1 + B2) + (2 * n + 7 + B1 + B2) := by
        rw [List.length_cons, Nat.add_right_comm, Nat.add_mul, one_mul]
      omega
    · have hstep0 : step^[t0]
          (some (⟨some .load1, mkS c1.tm c2.tm acc false,
            cstk u.reverse (b :: v) [] [] (fun _ => []) (fun _ => [])⟩ : CCfg c1.tm c2.tm)) =
          some ⟨some .load1, mkS c1.tm c2.tm (acc || (f1 u && f2 (b :: v))) false,
            cstk (u ++ [b]).reverse v [] [] (fun _ => []) (fun _ => [])⟩ := by
        dsimp only [t0]
        rw [Function.iterate_add_apply step 1 _, hround, Function.iterate_one]
        exact hadv
      rw [Function.iterate_add_apply step t' t0, hstep0, hrec]
      have hcat : u ++ [b] ++ v = u ++ b :: v := by simp
      rw [hcat, splitAny, Bool.or_assoc]

private noncomputable def concatInTime (f1 f2 : List Bool → Bool)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => splitAny f1 f2 [] x) where
  tm := concatTM c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => (n + 1) * (2 * n + 8 +
    (Finset.range (n + 1)).sup c1.time + (Finset.range (n + 1)).sup c2.time)
  outputsFun x := by
    let step := flip bind (TM2.step (cProg c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet))
    let hsp := run_splits f1 f2 c1 c2 x.length x [] false (by simp)
    let t := Classical.choose hsp
    have ht : t ≤ (x.length + 1) * (2 * x.length + 7 +
        (Finset.range (x.length + 1)).sup c1.time + (Finset.range (x.length + 1)).sup c2.time) :=
      (Classical.choose_spec hsp).1
    have hrun := (Classical.choose_spec hsp).2
    simp only [List.reverse_nil, List.nil_append, Bool.false_or] at hrun
    have hdrain := run_drain c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet (splitAny f1 f2 [] x) x.reverse
    rw [List.length_reverse] at hdrain
    refine ⟨⟨(x.length + 1) + t, ?_⟩, ?_⟩
    · have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
      refine (congrArg (fun l => step^[(x.length + 1) + t]
          (some (initList (concatTM c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
            c2.inputAlphabet.invFun c2.outputAlphabet) l))) (hm x)).trans
        ((congrArg (fun c => step^[(x.length + 1) + t] (some c))
            (initList_concatTM c1.inputAlphabet.invFun c1.outputAlphabet
              c2.inputAlphabet.invFun c2.outputAlphabet x)).trans
          (Eq.trans ?_ ((congrArg some (haltList_concatTM c1.inputAlphabet.invFun c1.outputAlphabet
              c2.inputAlphabet.invFun c2.outputAlphabet [splitAny f1 f2 [] x]).symm).trans
            (congrArg (fun l => some (haltList (concatTM c1.tm c2.tm c1.inputAlphabet.invFun
              c1.outputAlphabet c2.inputAlphabet.invFun c2.outputAlphabet) l))
              (hm [splitAny f1 f2 [] x]).symm))))
      exact (Function.iterate_add_apply step (x.length + 1) t _).trans
        ((congrArg (step^[x.length + 1]) hrun).trans hdrain)
    · set B1 := (Finset.range (x.length + 1)).sup c1.time
      set B2 := (Finset.range (x.length + 1)).sup c2.time
      change (x.length + 1) + t ≤ (x.length + 1) * (2 * x.length + 8 + B1 + B2)
      change t ≤ (x.length + 1) * (2 * x.length + 7 + B1 + B2) at ht
      have hmul : (x.length + 1) * (2 * x.length + 8 + B1 + B2) =
          (x.length + 1) * (2 * x.length + 7 + B1 + B2) + (x.length + 1) := by ring
      omega

private theorem exp_concat_bound (k1 k2 n : ℕ) :
    (n + 1) * (2 * n + 8 + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2)) ≤
      2 ^ (n ^ (2 * k1 + 2 * k2 + 30)) + (2 * k1 + 2 * k2 + 30) := by
  let K := 2 * k1 + 2 * k2 + 30
  rcases n with _ | _ | m
  · have h1 : 2 ^ (0 ^ k1) ≤ 2 := by rcases k1 with _ | k <;> simp
    have h2 : 2 ^ (0 ^ k2) ≤ 2 := by rcases k2 with _ | k <;> simp
    have h3 : 0 ^ K = 0 := Nat.zero_pow (by omega)
    show 1 * (8 + (2 ^ (0 ^ k1) + k1) + (2 ^ (0 ^ k2) + k2)) ≤ 2 ^ (0 ^ K) + K
    rw [h3]
    omega
  · show 2 * (10 + (2 ^ (1 ^ k1) + k1) + (2 ^ (1 ^ k2) + k2)) ≤ 2 ^ (1 ^ K) + K
    simp only [one_pow]
    omega
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    let E := max (N ^ k1) (max (N ^ k2) (N + 1))
    have hE1 : N ^ k1 ≤ E := le_max_left _ _
    have hE2 : N ^ k2 ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hE3 : N + 1 ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hp1 : 2 ^ (N ^ k1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hE1
    have hp2 : 2 ^ (N ^ k2) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hE2
    have hk1 : k1 ≤ 2 ^ E := by
      have a : k1 < 2 ^ k1 := Nat.lt_two_pow_self
      have b : 2 ^ k1 ≤ N ^ k1 := Nat.pow_le_pow_left hN2 k1
      have c : N ^ k1 < 2 ^ (N ^ k1) := Nat.lt_two_pow_self
      omega
    have hk2 : k2 ≤ 2 ^ E := by
      have a : k2 < 2 ^ k2 := Nat.lt_two_pow_self
      have b : 2 ^ k2 ≤ N ^ k2 := Nat.pow_le_pow_left hN2 k2
      have c : N ^ k2 < 2 ^ (N ^ k2) := Nat.lt_two_pow_self
      omega
    have hN1 : N + 1 ≤ 2 ^ E := by
      have a : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
      have b : 2 ^ (N + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hE3
      omega
    have hlin : 2 * N + 8 ≤ 4 * 2 ^ E := by omega
    have hinner : 2 * N + 8 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) ≤ 8 * 2 ^ E := by omega
    have hprod : (N + 1) * (2 * N + 8 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2)) ≤
        2 ^ (2 * E + 3) := by
      calc (N + 1) * (2 * N + 8 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2))
          ≤ 2 ^ E * (8 * 2 ^ E) := Nat.mul_le_mul hN1 hinner
        _ = 2 ^ (2 * E + 3) := by
            rw [Nat.pow_add, Nat.two_mul, Nat.pow_add]
            ring
    have hEK : 2 * E + 3 ≤ N ^ K := by
      have hb1 : 2 * N ^ k1 + 3 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k1 := Nat.one_le_pow k1 N (by omega)
        have hcb : 8 ≤ N ^ 3 := by
          have : 2 ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN2 3
          omega
        have hmul : 8 * N ^ k1 ≤ N ^ 3 * N ^ k1 := Nat.mul_le_mul_right _ hcb
        have hpk : N ^ 3 * N ^ k1 = N ^ (k1 + 3) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k1 + 3) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : 2 * N ^ k2 + 3 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k2 := Nat.one_le_pow k2 N (by omega)
        have hcb : 8 ≤ N ^ 3 := by
          have : 2 ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN2 3
          omega
        have hmul : 8 * N ^ k2 ≤ N ^ 3 * N ^ k2 := Nat.mul_le_mul_right _ hcb
        have hpk : N ^ 3 * N ^ k2 = N ^ (k2 + 3) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k2 + 3) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb3 : 2 * (N + 1) + 3 ≤ N ^ K := by
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
    show (N + 1) * (2 * N + 8 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2)) ≤ 2 ^ (N ^ K) + K
    omega

private theorem exp_concat (L₁ L₂ : Language Bool)
    (h1 : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)
    (h2 : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧ v ∈ L₂) ↔ f x = true) ∧
        ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨k1, f1, M1, hf1, ht1⟩ := h1
  obtain ⟨k2, f2, M2, hf2, ht2⟩ := h2
  refine ⟨2 * k1 + 2 * k2 + 30, fun x => splitAny f1 f2 [] x,
    concatInTime f1 f2 M1 M2, fun x => ?_, fun n => ?_⟩
  · rw [splitAny_iff]
    simp only [List.nil_append, hf1, hf2]
  · have hsup1 : (Finset.range (n + 1)).sup M1.time ≤ 2 ^ (n ^ k1) + k1 := by
      refine Finset.sup_le fun m hm => ?_
      have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
      exact (ht1 m).trans (Nat.add_le_add_right
        (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hmn k1)) k1)
    have hsup2 : (Finset.range (n + 1)).sup M2.time ≤ 2 ^ (n ^ k2) + k2 := by
      refine Finset.sup_le fun m hm => ?_
      have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
      exact (ht2 m).trans (Nat.add_le_add_right
        (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hmn k2)) k2)
    have hmul : (n + 1) * (2 * n + 8 +
        (Finset.range (n + 1)).sup M1.time + (Finset.range (n + 1)).sup M2.time) ≤
        (n + 1) * (2 * n + 8 + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2)) :=
      Nat.mul_le_mul_left (n + 1) (by omega)
    exact hmul.trans (exp_concat_bound k1 k2 n)

end PvsNP.Units.tc_exp_concat

theorem PvsNP.Units.tc_exp_concat :
    ∀ L₁ L₂ : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧ v ∈ L₂) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_concat.exp_concat
