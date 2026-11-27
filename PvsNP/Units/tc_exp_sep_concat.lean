import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_sep_concat_aux

open Turing

lemma iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma simulate {α β : Type} (f : α → Option α) (g : β → Option β) (emb : α → β)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : α), (flip bind f)^[n] (some a) = some b →
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

inductive LocalK : Type
  | inp | uRev | revTmp
  deriving DecidableEq

instance : Fintype LocalK where
  elems := { LocalK.inp, LocalK.uRev, LocalK.revTmp }
  complete x := by cases x <;> simp

section sepMachine

variable (M1 M2 : FinTM2)

abbrev SK : Type := LocalK ⊕ M1.K ⊕ M2.K

abbrev SΓ : SK M1 M2 → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl k) => M1.Γ k
  | Sum.inr (Sum.inr k) => M2.Γ k

abbrev SΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Fin 10

abbrev Sσ : Type := M1.σ × M2.σ × Option Bool × Bool

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (SΓ M1 M2) (SΛ M1 M2) (Sσ M1 M2)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr 3))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (SΓ M1 M2) (SΛ M1 M2) (Sσ M1 M2)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr 6))

variable (M1 M2)

def prog (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) :
    SΛ M1 M2 → TM2.Stmt (SΓ M1 M2) (SΛ M1 M2) (Sσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr ⟨0, _⟩) =>
      .pop (Sum.inl LocalK.inp) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.branch (fun s => s.2.2.1.getD false)
            (.push (Sum.inl LocalK.uRev) (fun _ => true)
              (.goto fun _ => Sum.inr (Sum.inr 0)))
            (.goto fun _ => Sum.inr (Sum.inr 1)))
          (.goto fun _ => Sum.inr (Sum.inr 8)))
  | Sum.inr (Sum.inr ⟨1, _⟩) =>
      .pop (Sum.inl LocalK.uRev) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inl LocalK.revTmp) (fun s => s.2.2.1.getD false)
            (.push (Sum.inr (Sum.inl M1.k₀)) (fun s => in1 (s.2.2.1.getD false))
              (.goto fun _ => Sum.inr (Sum.inr 1))))
          (.goto fun _ => Sum.inr (Sum.inr 2)))
  | Sum.inr (Sum.inr ⟨2, _⟩) =>
      .pop (Sum.inl LocalK.revTmp) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inl LocalK.uRev) (fun s => s.2.2.1.getD false)
            (.goto fun _ => Sum.inr (Sum.inr 2)))
          (.goto fun _ => Sum.inl M1.main))
  | Sum.inr (Sum.inr ⟨3, _⟩) =>
      .pop (Sum.inr (Sum.inl M1.k₁))
        (fun s o => (M1.initialState, s.2.1, o.map out1, s.2.2.2))
        (.branch (fun s => s.2.2.1.getD false)
          (.goto fun _ => Sum.inr (Sum.inr 4))
          (.push (Sum.inl LocalK.uRev) (fun _ => false)
            (.goto fun _ => Sum.inr (Sum.inr 0))))
  | Sum.inr (Sum.inr ⟨4, _⟩) =>
      .pop (Sum.inl LocalK.inp) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inl LocalK.revTmp) (fun s => s.2.2.1.getD false)
            (.goto fun _ => Sum.inr (Sum.inr 4)))
          (.goto fun _ => Sum.inr (Sum.inr 5)))
  | Sum.inr (Sum.inr ⟨5, _⟩) =>
      .pop (Sum.inl LocalK.revTmp) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inl LocalK.inp) (fun s => s.2.2.1.getD false)
            (.push (Sum.inr (Sum.inr M2.k₀)) (fun s => in2 (s.2.2.1.getD false))
              (.goto fun _ => Sum.inr (Sum.inr 5))))
          (.goto fun _ => Sum.inr (Sum.inl M2.main)))
  | Sum.inr (Sum.inr ⟨6, _⟩) =>
      .pop (Sum.inr (Sum.inr M2.k₁))
        (fun s o => (M1.initialState, M2.initialState, o.map out2, s.2.2.2))
        (.branch (fun s => s.2.2.1.getD false)
          (.load (fun s => (s.1, s.2.1, none, true))
            (.goto fun _ => Sum.inr (Sum.inr 7)))
          (.push (Sum.inl LocalK.uRev) (fun _ => false)
            (.goto fun _ => Sum.inr (Sum.inr 0))))
  | Sum.inr (Sum.inr ⟨7, _⟩) =>
      .pop (Sum.inl LocalK.inp) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.goto fun _ => Sum.inr (Sum.inr 7))
          (.goto fun _ => Sum.inr (Sum.inr 8)))
  | Sum.inr (Sum.inr ⟨8, _⟩) =>
      .pop (Sum.inl LocalK.uRev) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.goto fun _ => Sum.inr (Sum.inr 8))
          (.goto fun _ => Sum.inr (Sum.inr 9)))
  | Sum.inr (Sum.inr ⟨9, _⟩) =>
      .push (Sum.inl LocalK.inp) (fun s => s.2.2.2)
        (.load (fun _ => (M1.initialState, M2.initialState, none, false)) .halt)

abbrev sepTM (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) : FinTM2 :=
  { K := SK M1 M2
    k₀ := Sum.inl LocalK.inp
    k₁ := Sum.inl LocalK.inp
    Γ := SΓ M1 M2
    Λ := SΛ M1 M2
    main := Sum.inr (Sum.inr 0)
    σ := Sσ M1 M2
    initialState := (M1.initialState, M2.initialState, none, false)
    kFin := @instFintypeSum _ _ inferInstance (@instFintypeSum _ _ M1.kFin M2.kFin)
    ΛFin := @instFintypeSum _ _ M1.ΛFin (@instFintypeSum _ _ M2.ΛFin inferInstance)
    σFin := @instFintypeProd _ _ M1.σFin (@instFintypeProd _ _ M2.σFin inferInstance)
    m := prog M1 M2 in1 out1 in2 out2 }

variable {M1 M2}

def embStk (a u r : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    ∀ k, List (SΓ M1 M2 k)
  | Sum.inl LocalK.inp => a
  | Sum.inl LocalK.uRev => u
  | Sum.inl LocalK.revTmp => r
  | Sum.inr (Sum.inl k) => S1 k
  | Sum.inr (Sum.inr k) => S2 k

lemma embStk_upd_inp (a a' u r : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (embStk a u r S1 S2) (Sum.inl LocalK.inp) a' = embStk a' u r S1 S2 := by
  funext j
  rcases j with (_ | _ | _) | j | j <;> simp [embStk]

lemma embStk_upd_uRev (a u u' r : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (embStk a u r S1 S2) (Sum.inl LocalK.uRev) u' = embStk a u' r S1 S2 := by
  funext j
  rcases j with (_ | _ | _) | j | j <;> simp [embStk]

lemma embStk_upd_revTmp (a u r r' : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (embStk a u r S1 S2) (Sum.inl LocalK.revTmp) r' = embStk a u r' S1 S2 := by
  funext j
  rcases j with (_ | _ | _) | j | j <;> simp [embStk]

lemma embStk_upd1 (a u r : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (k : M1.K) (xs : List (M1.Γ k)) :
    Function.update (embStk a u r S1 S2) (Sum.inr (Sum.inl k)) xs =
      embStk a u r (Function.update S1 k xs) S2 := by
  funext j
  rcases j with (_ | _ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · by_cases h : j = k
    · subst h; simp [embStk]
    · simp [embStk, h]
  · simp [embStk]

lemma embStk_upd2 (a u r : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (k : M2.K) (xs : List (M2.Γ k)) :
    Function.update (embStk a u r S1 S2) (Sum.inr (Sum.inr k)) xs =
      embStk a u r S1 (Function.update S2 k xs) := by
  funext j
  rcases j with (_ | _ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · by_cases h : j = k
    · subst h; simp [embStk]
    · simp [embStk, h]

def emb1 (a u : List Bool) (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (c : TM2.Cfg M1.Γ M1.Λ M1.σ) : TM2.Cfg (SΓ M1 M2) (SΛ M1 M2) (Sσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr 3)) Sum.inl), (c.var, w), embStk a u [] c.stk S2⟩

def emb2 (a u : List Bool) (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (c : TM2.Cfg M2.Γ M2.Λ M2.σ) : TM2.Cfg (SΓ M1 M2) (SΛ M1 M2) (Sσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr 6)) (fun l => Sum.inr (Sum.inl l))),
    (u1, c.var, t, b1), embStk a u [] S1 c.stk⟩

lemma sim1 (a u : List Bool) (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ) (S1 : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Sσ M1 M2) (embStk a u [] S1 S2) =
      emb1 a u w S2 (TM2.stepAux q v S1) := by
  induction q generalizing v S1 with
  | push k f q ih =>
      simp only [tr1, TM2.stepAux]
      rw [embStk_upd1]
      exact ih v (Function.update S1 k (f v :: S1 k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      simp only [tr1, TM2.stepAux]
      rw [embStk_upd1]
      exact ih (f v (S1 k).head?) (Function.update S1 k (S1 k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [tr1, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

lemma sim2 (a u : List Bool) (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ) (S2 : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u1, v, t, b1) : Sσ M1 M2) (embStk a u [] S1 S2) =
      emb2 a u u1 t b1 S1 (TM2.stepAux q v S2) := by
  induction q generalizing v S2 with
  | push k f q ih =>
      simp only [tr2, TM2.stepAux]
      rw [embStk_upd2]
      exact ih v (Function.update S2 k (f v :: S2 k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      simp only [tr2, TM2.stepAux]
      rw [embStk_upd2]
      exact ih (f v (S2 k).head?) (Function.update S2 k (S2 k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [tr2, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

lemma step1 (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a u : List Bool) (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ) (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 in1 out1 in2 out2) (emb1 a u w S2 c) = some (emb1 a u w S2 c') := by
  rcases c with ⟨_ | l, v, S1⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, prog, emb1, Option.elim_some]
    rw [sim1]
    simp only [TM2.step] at h
    exact congrArg some (congrArg (emb1 a u w S2) (Option.some.inj h))

lemma step2 (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a u : List Bool) (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ) (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 in1 out1 in2 out2) (emb2 a u u1 t b1 S1 c) =
      some (emb2 a u u1 t b1 S1 c') := by
  rcases c with ⟨_ | l, v, S2⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, prog, emb2, Option.elim_some]
    rw [sim2]
    simp only [TM2.step] at h
    exact congrArg some (congrArg (emb2 a u u1 t b1 S1) (Option.some.inj h))

lemma initList_stk_eq (M : FinTM2) (xs : List (M.Γ M.k₀)) :
    (initList M xs).stk = Function.update (fun _ => []) M.k₀ xs := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

lemma haltList_stk_eq (M : FinTM2) (xs : List (M.Γ M.k₁)) :
    (haltList M xs).stk = Function.update (fun _ => []) M.k₁ xs := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

lemma initList_eq_embStk (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) (x : List Bool) :
    initList (sepTM M1 M2 in1 out1 in2 out2) x =
      ⟨some (Sum.inr (Sum.inr 0)), (M1.initialState, M2.initialState, none, false),
        embStk x [] [] (fun _ => []) (fun _ => [])⟩ := by
  simp only [initList, sepTM]
  congr 1
  funext j
  rcases j with (_ | _ | _) | j | j <;> simp [embStk]

lemma haltList_eq_embStk (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) (y : List Bool) :
    haltList (sepTM M1 M2 in1 out1 in2 out2) y =
      ⟨none, (M1.initialState, M2.initialState, none, false),
        embStk y [] [] (fun _ => []) (fun _ => [])⟩ := by
  simp only [haltList, sepTM]
  congr 1
  funext j
  rcases j with (_ | _ | _) | j | j <;> simp [embStk]

lemma loop_copyU1 (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a u r acc : List Bool) (t : Option Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[u.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 1)), (M1.initialState, M2.initialState, t, false),
        embStk a u r (Function.update (fun _ => []) M1.k₀ (acc.map in1)) (fun _ => [])⟩) =
    some ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, none, false),
      embStk a [] (u.reverse ++ r)
        (Function.update (fun _ => []) M1.k₀ ((u.reverse ++ acc).map in1)) (fun _ => [])⟩ := by
  induction u generalizing r acc t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, List.reverse_nil, List.nil_append, embStk_upd_uRev]
  | cons b u ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 1)), (M1.initialState, M2.initialState, t, false),
              embStk a (b :: u) r (Function.update (fun _ => []) M1.k₀ (acc.map in1)) (fun _ => [])⟩ =
          some ⟨some (Sum.inr (Sum.inr 1)), (M1.initialState, M2.initialState, some b, false),
            embStk a u (b :: r)
              (Function.update (fun _ => []) M1.k₀ ((b :: acc).map in1)) (fun _ => [])⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, Option.getD_some, List.tail_cons, embStk_upd_uRev, embStk_upd_revTmp,
          embStk_upd1, Function.update_self, Function.update_idem, List.map_cons]
      rw [hstep, List.reverse_cons, List.append_assoc, List.append_assoc]
      exact ih (b :: r) (b :: acc) (some b)

lemma loop_restoreU (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a r u : List Bool) (acc : List (M1.Γ M1.k₀)) (t : Option Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[r.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, t, false),
        embStk a u r (Function.update (fun _ => []) M1.k₀ acc) (fun _ => [])⟩) =
    some ⟨some (Sum.inl M1.main), (M1.initialState, M2.initialState, none, false),
      embStk a (r.reverse ++ u) [] (Function.update (fun _ => []) M1.k₀ acc) (fun _ => [])⟩ := by
  induction r generalizing u t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, List.reverse_nil, List.nil_append, embStk_upd_revTmp]
  | cons b r ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, t, false),
              embStk a u (b :: r) (Function.update (fun _ => []) M1.k₀ acc) (fun _ => [])⟩ =
          some ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, some b, false),
            embStk a (b :: u) r (Function.update (fun _ => []) M1.k₀ acc) (fun _ => [])⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, Option.getD_some, List.tail_cons, embStk_upd_revTmp, embStk_upd_uRev]
      rw [hstep, List.reverse_cons, List.append_assoc]
      exact ih (b :: u) (some b)

lemma loop_copyV1 (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a u r : List Bool) (t : Option Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[a.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 4)), (M1.initialState, M2.initialState, t, false),
        embStk a u r (fun _ => []) (fun _ => [])⟩) =
    some ⟨some (Sum.inr (Sum.inr 5)), (M1.initialState, M2.initialState, none, false),
      embStk [] u (a.reverse ++ r) (fun _ => []) (fun _ => [])⟩ := by
  induction a generalizing r t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, List.reverse_nil, List.nil_append, embStk_upd_inp]
  | cons b a ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 4)), (M1.initialState, M2.initialState, t, false),
              embStk (b :: a) u r (fun _ => []) (fun _ => [])⟩ =
          some ⟨some (Sum.inr (Sum.inr 4)), (M1.initialState, M2.initialState, some b, false),
            embStk a u (b :: r) (fun _ => []) (fun _ => [])⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, Option.getD_some, List.tail_cons, embStk_upd_inp, embStk_upd_revTmp]
      rw [hstep, List.reverse_cons, List.append_assoc]
      exact ih (b :: r) (some b)

lemma loop_copyV2 (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (r a u acc : List Bool) (t : Option Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[r.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 5)), (M1.initialState, M2.initialState, t, false),
        embStk a u r (fun _ => []) (Function.update (fun _ => []) M2.k₀ (acc.map in2))⟩) =
    some ⟨some (Sum.inr (Sum.inl M2.main)), (M1.initialState, M2.initialState, none, false),
      embStk (r.reverse ++ a) u [] (fun _ => [])
        (Function.update (fun _ => []) M2.k₀ ((r.reverse ++ acc).map in2))⟩ := by
  induction r generalizing a acc t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, List.reverse_nil, List.nil_append, embStk_upd_revTmp]
  | cons b r ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 5)), (M1.initialState, M2.initialState, t, false),
              embStk a u (b :: r) (fun _ => []) (Function.update (fun _ => []) M2.k₀ (acc.map in2))⟩ =
          some ⟨some (Sum.inr (Sum.inr 5)), (M1.initialState, M2.initialState, some b, false),
            embStk (b :: a) u r (fun _ => [])
              (Function.update (fun _ => []) M2.k₀ ((b :: acc).map in2))⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, Option.getD_some, List.tail_cons, embStk_upd_revTmp, embStk_upd_inp,
          embStk_upd2, Function.update_self, Function.update_idem, List.map_cons]
      rw [hstep, List.reverse_cons, List.append_assoc, List.append_assoc]
      exact ih (b :: a) (b :: acc) (some b)

lemma loop_clearInp (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (a u : List Bool) (t : Option Bool) (res : Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[a.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 7)), (M1.initialState, M2.initialState, t, res),
        embStk a u [] (fun _ => []) (fun _ => [])⟩) =
    some ⟨some (Sum.inr (Sum.inr 8)), (M1.initialState, M2.initialState, none, res),
      embStk [] u [] (fun _ => []) (fun _ => [])⟩ := by
  induction a generalizing t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, embStk_upd_inp]
  | cons b a ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 7)), (M1.initialState, M2.initialState, t, res),
              embStk (b :: a) u [] (fun _ => []) (fun _ => [])⟩ =
          some ⟨some (Sum.inr (Sum.inr 7)), (M1.initialState, M2.initialState, some b, res),
            embStk a u [] (fun _ => []) (fun _ => [])⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, List.tail_cons, embStk_upd_inp]
      rw [hstep]
      exact ih (some b)

lemma loop_clearU (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)
    (u : List Bool) (t : Option Bool) (res : Bool) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[u.length + 1]
      (some ⟨some (Sum.inr (Sum.inr 8)), (M1.initialState, M2.initialState, t, res),
        embStk [] u [] (fun _ => []) (fun _ => [])⟩) =
    some ⟨some (Sum.inr (Sum.inr 9)), (M1.initialState, M2.initialState, none, res),
      embStk [] [] [] (fun _ => []) (fun _ => [])⟩ := by
  induction u generalizing t with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
        List.tail_nil, embStk_upd_uRev]
  | cons b u ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, flip, bind, Option.bind_some]
      have hstep :
          TM2.step (prog M1 M2 in1 out1 in2 out2)
            ⟨some (Sum.inr (Sum.inr 8)), (M1.initialState, M2.initialState, t, res),
              embStk [] (b :: u) [] (fun _ => []) (fun _ => [])⟩ =
          some ⟨some (Sum.inr (Sum.inr 8)), (M1.initialState, M2.initialState, some b, res),
            embStk [] u [] (fun _ => []) (fun _ => [])⟩ := by
        simp only [TM2.step, prog, TM2.stepAux, embStk, List.head?_cons, Option.isSome_some,
          Bool.cond_true, List.tail_cons, embStk_upd_uRev]
      rw [hstep]
      exact ih (some b)

def sepConcatAux (f1 f2 : List Bool → Bool) (uRev : List Bool) : List Bool → Bool
  | [] => false
  | false :: rest => (f1 uRev.reverse && f2 rest) || sepConcatAux f1 f2 (false :: uRev) rest
  | true :: rest => sepConcatAux f1 f2 (true :: uRev) rest

theorem sepConcatAux_iff (f1 f2 : List Bool → Bool) (uRev v : List Bool) :
    sepConcatAux f1 f2 uRev v = true ↔
      ∃ u' v' : List Bool, v = u' ++ false :: v' ∧
        f1 (uRev.reverse ++ u') = true ∧ f2 v' = true := by
  induction v generalizing uRev with
  | nil =>
      simp [sepConcatAux]
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [sepConcatAux, Bool.or_eq_true, Bool.and_eq_true, ih]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨u', v', hrest, h1, h2⟩)
            · exact ⟨[], rest, rfl, by simpa using h1, h2⟩
            · refine ⟨false :: u', v', by simp [hrest], ?_, h2⟩
              simpa [List.reverse_cons, List.append_assoc] using h1
          · rintro ⟨u', v', heq, h1, h2⟩
            cases u' with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at heq
                left
                exact ⟨by simpa using h1, by simpa [heq.2] using h2⟩
            | cons c u'' =>
                simp only [List.cons_append, List.cons.injEq] at heq
                right
                refine ⟨u'', v', heq.2, ?_, h2⟩
                have hc : c = false := heq.1.symm
                subst hc
                simpa [List.reverse_cons, List.append_assoc] using h1
      | true =>
          simp only [sepConcatAux, ih]
          constructor
          · rintro ⟨u', v', hrest, h1, h2⟩
            refine ⟨true :: u', v', by simp [hrest], ?_, h2⟩
            simpa [List.reverse_cons, List.append_assoc] using h1
          · rintro ⟨u', v', heq, h1, h2⟩
            cases u' with
            | nil =>
                simp at heq
            | cons c u'' =>
                simp only [List.cons_append, List.cons.injEq] at heq
                have hc : c = true := heq.1.symm
                subst hc
                refine ⟨u'', v', heq.2, ?_, h2⟩
                simpa [List.reverse_cons, List.append_assoc] using h1

lemma sep_run (f1 f2 : List Bool → Bool) (k1 k2 : ℕ)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2)
    (ht1 : ∀ n : ℕ, c1.time n ≤ 2 ^ (n ^ k1) + k1)
    (ht2 : ∀ n : ℕ, c2.time n ≤ 2 ^ (n ^ k2) + k2)
    (v uRev : List Bool) (t : Option Bool) :
    ∃ steps : ℕ,
      (flip bind (TM2.step (prog c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
          c2.inputAlphabet.invFun c2.outputAlphabet)))^[steps]
        (some ⟨some (Sum.inr (Sum.inr 0)),
          (c1.tm.initialState, c2.tm.initialState, t, false),
          embStk v uRev [] (fun _ => []) (fun _ => [])⟩) =
      some ⟨none, (c1.tm.initialState, c2.tm.initialState, none, false),
        embStk [sepConcatAux f1 f2 uRev v] [] [] (fun _ => []) (fun _ => [])⟩ ∧
      steps ≤ (v.length + 1) * (2 * (v.length + uRev.length) +
        (2 ^ ((v.length + uRev.length) ^ k1) + k1) +
        (2 ^ ((v.length + uRev.length) ^ k2) + k2) + 12) := by
  let P := prog c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet
  induction v generalizing uRev t with
  | nil =>
      have p0 : (flip bind (TM2.step P))^[1]
          (some ⟨some (Sum.inr (Sum.inr 0)), (c1.tm.initialState, c2.tm.initialState, t, false),
            embStk [] uRev [] (fun _ => []) (fun _ => [])⟩) =
          some ⟨some (Sum.inr (Sum.inr 8)), (c1.tm.initialState, c2.tm.initialState, none, false),
            embStk [] uRev [] (fun _ => []) (fun _ => [])⟩ := by
        simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog, TM2.stepAux,
          embStk, List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, embStk_upd_inp]
      have p8 := loop_clearU c1.inputAlphabet.invFun c1.outputAlphabet
        c2.inputAlphabet.invFun c2.outputAlphabet uRev none false
      have p9 : (flip bind (TM2.step P))^[1]
          (some ⟨some (Sum.inr (Sum.inr 9)), (c1.tm.initialState, c2.tm.initialState, none, false),
            embStk [] [] [] (fun _ => []) (fun _ => [])⟩) =
          some ⟨none, (c1.tm.initialState, c2.tm.initialState, none, false),
            embStk [false] [] [] (fun _ => []) (fun _ => [])⟩ := by
        simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog, TM2.stepAux,
          embStk, embStk_upd_inp]
      refine ⟨1 + (uRev.length + 1) + 1, ?_, ?_⟩
      · rw [Function.iterate_add_apply, Function.iterate_add_apply, p0, p8, p9]
        rfl
      · have hp1 : 1 ≤ 2 ^ (uRev.length ^ k1) := Nat.one_le_two_pow
        have hp2 : 1 ≤ 2 ^ (uRev.length ^ k2) := Nat.one_le_two_pow
        simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
  | cons b rest ih =>
      cases b with
      | true =>
          have p0 : (flip bind (TM2.step P))^[1]
              (some ⟨some (Sum.inr (Sum.inr 0)), (c1.tm.initialState, c2.tm.initialState, t, false),
                embStk (true :: rest) uRev [] (fun _ => []) (fun _ => [])⟩) =
              some ⟨some (Sum.inr (Sum.inr 0)), (c1.tm.initialState, c2.tm.initialState, some true, false),
                embStk rest (true :: uRev) [] (fun _ => []) (fun _ => [])⟩ := by
            simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog, TM2.stepAux,
              embStk, List.head?_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
              List.tail_cons, embStk_upd_inp, embStk_upd_uRev]
          obtain ⟨s_rec, h_rec, hb_rec⟩ := ih (true :: uRev) (some true)
          refine ⟨s_rec + 1, ?_, ?_⟩
          · rw [Function.iterate_add_apply, p0, h_rec]
            rfl
          · have hlen : rest.length + (true :: uRev).length = (true :: rest).length + uRev.length := by
              simp; omega
            rw [hlen] at hb_rec
            simp only [List.length_cons] at hb_rec ⊢
            have hp1 : 1 ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k1) := Nat.one_le_two_pow
            have hp2 : 1 ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k2) := Nat.one_le_two_pow
            nlinarith
      | false =>
          have p0 : (flip bind (TM2.step P))^[1]
              (some ⟨some (Sum.inr (Sum.inr 0)), (c1.tm.initialState, c2.tm.initialState, t, false),
                embStk (false :: rest) uRev [] (fun _ => []) (fun _ => [])⟩) =
              some ⟨some (Sum.inr (Sum.inr 1)), (c1.tm.initialState, c2.tm.initialState, some false, false),
                embStk rest uRev [] (fun _ => []) (fun _ => [])⟩ := by
            simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog, TM2.stepAux,
              embStk, List.head?_cons, Option.isSome_some, Bool.cond_true, Bool.cond_false, Option.getD_some,
              List.tail_cons, embStk_upd_inp]
          have p1 := loop_copyU1 c1.inputAlphabet.invFun c1.outputAlphabet
            c2.inputAlphabet.invFun c2.outputAlphabet rest uRev [] [] (some false)
          simp only [List.append_nil, List.map_nil, Function.update_eq_self] at p1
          have p2 := loop_restoreU c1.inputAlphabet.invFun c1.outputAlphabet
            c2.inputAlphabet.invFun c2.outputAlphabet rest uRev.reverse []
            (uRev.reverse.map c1.inputAlphabet.invFun) none
          simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at p2
          have r1 := c1.outputsFun uRev.reverse
          have h1' := simulate (TM2.step c1.tm.m) (TM2.step P)
            (emb1 rest uRev (c2.tm.initialState, none, false) (fun _ => []))
            (step1 c1.inputAlphabet.invFun c1.outputAlphabet
              c2.inputAlphabet.invFun c2.outputAlphabet rest uRev
              (c2.tm.initialState, none, false) (fun _ => []))
            r1.steps _ _ r1.evals_in_steps
          have he1_in :
              emb1 rest uRev (c2.tm.initialState, none, false) (fun _ => [])
                (initList c1.tm (List.map c1.inputAlphabet.invFun (PvsNP.encodeString uRev.reverse))) =
              ⟨some (Sum.inl c1.tm.main), (c1.tm.initialState, c2.tm.initialState, none, false),
                embStk rest uRev []
                  (Function.update (fun _ => []) c1.tm.k₀ (uRev.reverse.map c1.inputAlphabet.invFun))
                  (fun _ => [])⟩ := by
            unfold emb1
            rw [initList_stk_eq]
            rfl
          have he1_out :
              emb1 rest uRev (c2.tm.initialState, none, false) (fun _ => [])
                (haltList c1.tm (List.map c1.outputAlphabet.invFun (PvsNP.encodeAnswer (f1 uRev.reverse)))) =
              ⟨some (Sum.inr (Sum.inr 3)), (c1.tm.initialState, c2.tm.initialState, none, false),
                embStk rest uRev []
                  (Function.update (fun _ => []) c1.tm.k₁ [c1.outputAlphabet.invFun (f1 uRev.reverse)])
                  (fun _ => [])⟩ := by
            unfold emb1
            rw [haltList_stk_eq]
            rfl
          rw [he1_in, he1_out] at h1'
          have hr1_le : r1.steps ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1 := by
            have hle_t := r1.steps_le_m.trans (ht1 (PvsNP.encodeString uRev.reverse).length)
            have hlen : (PvsNP.encodeString uRev.reverse).length = uRev.length := by
              change uRev.reverse.length = uRev.length
              simp
            have hpow : (PvsNP.encodeString uRev.reverse).length ^ k1 ≤
                (rest.length + 1 + uRev.length) ^ k1 :=
              Nat.pow_le_pow_left (by omega) k1
            have hexp : 2 ^ ((PvsNP.encodeString uRev.reverse).length ^ k1) ≤
                2 ^ ((rest.length + 1 + uRev.length) ^ k1) :=
              Nat.pow_le_pow_right (by omega) hpow
            omega
          cases hf1 : f1 uRev.reverse with
          | false =>
              have h_o1 : c1.outputAlphabet (c1.outputAlphabet.invFun false) = false :=
                c1.outputAlphabet.right_inv false
              have p3 : (flip bind (TM2.step P))^[1]
                  (some ⟨some (Sum.inr (Sum.inr 3)),
                    (c1.tm.initialState, c2.tm.initialState, none, false),
                    embStk rest uRev []
                      (Function.update (fun _ => []) c1.tm.k₁ [c1.outputAlphabet.invFun false])
                      (fun _ => [])⟩) =
                  some ⟨some (Sum.inr (Sum.inr 0)),
                    (c1.tm.initialState, c2.tm.initialState, some false, false),
                    embStk rest (false :: uRev) [] (fun _ => []) (fun _ => [])⟩ := by
                simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog,
                  TM2.stepAux, embStk, Function.update_self, List.head?_cons, Option.map_some,
                  h_o1, Option.getD_some, Bool.cond_false, List.tail_cons,
                  embStk_upd1, Function.update_idem, Function.update_eq_self, embStk_upd_uRev]
              simp only [hf1] at h1'
              obtain ⟨s_rec, h_rec, hb_rec⟩ := ih (false :: uRev) (some false)
              refine ⟨s_rec + (1 + r1.steps + (uRev.length + 1) + (uRev.length + 1) + 1), ?_, ?_⟩
              · rw [Function.iterate_add_apply, Function.iterate_add_apply,
                  Function.iterate_add_apply, Function.iterate_add_apply,
                  Function.iterate_add_apply, p0, p1, p2, h1', p3, h_rec]
                simp [sepConcatAux, hf1]
              · have hlen : rest.length + (false :: uRev).length = (false :: rest).length + uRev.length := by
                  simp; omega
                rw [hlen] at hb_rec
                simp only [List.length_cons] at hb_rec ⊢
                have hp2 : 1 ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k2) := Nat.one_le_two_pow
                have hmul : (rest.length + 1) * (2 * (rest.length + 1 + uRev.length) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) +
                    (2 * (rest.length + 1 + uRev.length) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) =
                    (rest.length + 1 + 1) * (2 * (rest.length + 1 + uRev.length) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                    (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) := by
                  ring
                omega
          | true =>
              have h_o1 : c1.outputAlphabet (c1.outputAlphabet.invFun true) = true :=
                c1.outputAlphabet.right_inv true
              have p3 : (flip bind (TM2.step P))^[1]
                  (some ⟨some (Sum.inr (Sum.inr 3)),
                    (c1.tm.initialState, c2.tm.initialState, none, false),
                    embStk rest uRev []
                      (Function.update (fun _ => []) c1.tm.k₁ [c1.outputAlphabet.invFun true])
                      (fun _ => [])⟩) =
                  some ⟨some (Sum.inr (Sum.inr 4)),
                    (c1.tm.initialState, c2.tm.initialState, some true, false),
                    embStk rest uRev [] (fun _ => []) (fun _ => [])⟩ := by
                simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog,
                  TM2.stepAux, embStk, Function.update_self, List.head?_cons, Option.map_some,
                  h_o1, Option.getD_some, Bool.cond_true, List.tail_cons,
                  embStk_upd1, Function.update_idem, Function.update_eq_self]
              simp only [hf1] at h1'
              have p4 := loop_copyV1 c1.inputAlphabet.invFun c1.outputAlphabet
                c2.inputAlphabet.invFun c2.outputAlphabet rest uRev [] (some true)
              simp only [List.append_nil] at p4
              have p5 := loop_copyV2 c1.inputAlphabet.invFun c1.outputAlphabet
                c2.inputAlphabet.invFun c2.outputAlphabet rest.reverse [] uRev [] none
              simp only [List.reverse_reverse, List.append_nil, List.map_nil, Function.update_eq_self,
                List.length_reverse] at p5
              have r2 := c2.outputsFun rest
              have h2' := simulate (TM2.step c2.tm.m) (TM2.step P)
                (emb2 rest uRev c1.tm.initialState none false (fun _ => []))
                (step2 c1.inputAlphabet.invFun c1.outputAlphabet
                  c2.inputAlphabet.invFun c2.outputAlphabet rest uRev
                  c1.tm.initialState none false (fun _ => []))
                r2.steps _ _ r2.evals_in_steps
              have he2_in :
                  emb2 rest uRev c1.tm.initialState none false (fun _ => [])
                    (initList c2.tm (List.map c2.inputAlphabet.invFun (PvsNP.encodeString rest))) =
                  ⟨some (Sum.inr (Sum.inl c2.tm.main)),
                    (c1.tm.initialState, c2.tm.initialState, none, false),
                    embStk rest uRev [] (fun _ => [])
                      (Function.update (fun _ => []) c2.tm.k₀ (rest.map c2.inputAlphabet.invFun))⟩ := by
                unfold emb2
                rw [initList_stk_eq]
                rfl
              have he2_out :
                  emb2 rest uRev c1.tm.initialState none false (fun _ => [])
                    (haltList c2.tm (List.map c2.outputAlphabet.invFun (PvsNP.encodeAnswer (f2 rest)))) =
                  ⟨some (Sum.inr (Sum.inr 6)),
                    (c1.tm.initialState, c2.tm.initialState, none, false),
                    embStk rest uRev [] (fun _ => [])
                      (Function.update (fun _ => []) c2.tm.k₁ [c2.outputAlphabet.invFun (f2 rest)])⟩ := by
                unfold emb2
                rw [haltList_stk_eq]
                rfl
              rw [he2_in, he2_out] at h2'
              have hr2_le : r2.steps ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2 := by
                have hle_t := r2.steps_le_m.trans (ht2 rest.length)
                have hpow : rest.length ^ k2 ≤ (rest.length + 1 + uRev.length) ^ k2 :=
                  Nat.pow_le_pow_left (by omega) k2
                have hexp : 2 ^ (rest.length ^ k2) ≤ 2 ^ ((rest.length + 1 + uRev.length) ^ k2) :=
                  Nat.pow_le_pow_right (by omega) hpow
                omega
              cases hf2 : f2 rest with
              | false =>
                  have h_o2 : c2.outputAlphabet (c2.outputAlphabet.invFun false) = false :=
                    c2.outputAlphabet.right_inv false
                  have p6 : (flip bind (TM2.step P))^[1]
                      (some ⟨some (Sum.inr (Sum.inr 6)),
                        (c1.tm.initialState, c2.tm.initialState, none, false),
                        embStk rest uRev [] (fun _ => [])
                          (Function.update (fun _ => []) c2.tm.k₁ [c2.outputAlphabet.invFun false])⟩) =
                      some ⟨some (Sum.inr (Sum.inr 0)),
                        (c1.tm.initialState, c2.tm.initialState, some false, false),
                        embStk rest (false :: uRev) [] (fun _ => []) (fun _ => [])⟩ := by
                    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog,
                      TM2.stepAux, embStk, Function.update_self, List.head?_cons, Option.map_some,
                      h_o2, Option.getD_some, Bool.cond_false, List.tail_cons,
                      embStk_upd2, Function.update_idem, Function.update_eq_self, embStk_upd_uRev]
                  simp only [hf2] at h2'
                  obtain ⟨s_rec, h_rec, hb_rec⟩ := ih (false :: uRev) (some false)
                  refine ⟨s_rec + (1 + r2.steps + (rest.length + 1) + (rest.length + 1) + 1 +
                      r1.steps + (uRev.length + 1) + (uRev.length + 1) + 1), ?_, ?_⟩
                  · rw [Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply,
                      p0, p1, p2, h1', p3, p4, p5, h2', p6, h_rec]
                    simp [sepConcatAux, hf1, hf2]
                  · have hlen : rest.length + (false :: uRev).length = (false :: rest).length + uRev.length := by
                      simp; omega
                    rw [hlen] at hb_rec
                    simp only [List.length_cons] at hb_rec ⊢
                    have hmul : (rest.length + 1) * (2 * (rest.length + 1 + uRev.length) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) +
                        (2 * (rest.length + 1 + uRev.length) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) =
                        (rest.length + 1 + 1) * (2 * (rest.length + 1 + uRev.length) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) := by
                      ring
                    omega
              | true =>
                  have h_o2 : c2.outputAlphabet (c2.outputAlphabet.invFun true) = true :=
                    c2.outputAlphabet.right_inv true
                  have p6 : (flip bind (TM2.step P))^[1]
                      (some ⟨some (Sum.inr (Sum.inr 6)),
                        (c1.tm.initialState, c2.tm.initialState, none, false),
                        embStk rest uRev [] (fun _ => [])
                          (Function.update (fun _ => []) c2.tm.k₁ [c2.outputAlphabet.invFun true])⟩) =
                      some ⟨some (Sum.inr (Sum.inr 7)),
                        (c1.tm.initialState, c2.tm.initialState, none, true),
                        embStk rest uRev [] (fun _ => []) (fun _ => [])⟩ := by
                    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog,
                      TM2.stepAux, embStk, Function.update_self, List.head?_cons, Option.map_some,
                      h_o2, Option.getD_some, Bool.cond_true, List.tail_cons,
                      embStk_upd2, Function.update_idem, Function.update_eq_self]
                  simp only [hf2] at h2'
                  have p7 := loop_clearInp c1.inputAlphabet.invFun c1.outputAlphabet
                    c2.inputAlphabet.invFun c2.outputAlphabet rest uRev none true
                  have p8 := loop_clearU c1.inputAlphabet.invFun c1.outputAlphabet
                    c2.inputAlphabet.invFun c2.outputAlphabet uRev none true
                  have p9 : (flip bind (TM2.step P))^[1]
                      (some ⟨some (Sum.inr (Sum.inr 9)),
                        (c1.tm.initialState, c2.tm.initialState, none, true),
                        embStk [] [] [] (fun _ => []) (fun _ => [])⟩) =
                      some ⟨none, (c1.tm.initialState, c2.tm.initialState, none, false),
                        embStk [true] [] [] (fun _ => []) (fun _ => [])⟩ := by
                    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, P, prog,
                      TM2.stepAux, embStk, embStk_upd_inp]
                  refine ⟨1 + (uRev.length + 1) + (rest.length + 1) + 1 + r2.steps +
                      (rest.length + 1) + (rest.length + 1) + 1 + r1.steps +
                      (uRev.length + 1) + (uRev.length + 1) + 1, ?_, ?_⟩
                  · rw [Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply, Function.iterate_add_apply,
                      Function.iterate_add_apply,
                      p0, p1, p2, h1', p3, p4, p5, h2', p6, p7, p8, p9]
                    simp [sepConcatAux, hf1, hf2]
                  · simp only [List.length_cons]
                    have hle1 : 2 * (rest.length + 1 + uRev.length) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12 ≤
                        (rest.length + 1 + 1) * (2 * (rest.length + 1 + uRev.length) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k1) + k1) +
                        (2 ^ ((rest.length + 1 + uRev.length) ^ k2) + k2) + 12) :=
                      Nat.le_mul_of_pos_left _ (by omega)
                    have hle2 : 4 * (rest.length + uRev.length) + 12 ≤
                        2 * (rest.length + 1 + uRev.length) + 12 +
                        2 * (rest.length + 1 + uRev.length) := by omega
                    nlinarith

end sepMachine

noncomputable def sepInTime (f1 f2 : List Bool → Bool) (k1 k2 : ℕ)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2)
    (ht1 : ∀ n : ℕ, c1.time n ≤ 2 ^ (n ^ k1) + k1)
    (ht2 : ∀ n : ℕ, c2.time n ≤ 2 ^ (n ^ k2) + k2) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (sepConcatAux f1 f2 []) where
  tm := sepTM c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => (n + 1) * (2 * n + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2) + 12)
  outputsFun x := by
    have hex := sep_run f1 f2 k1 k2 c1 c2 ht1 ht2 x [] none
    let steps := Classical.choose hex
    have hspec := Classical.choose_spec hex
    refine ⟨⟨steps, ?_⟩, ?_⟩
    · have hid : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := List.map_id x
      have hid2 : List.map (Equiv.refl Bool).invFun (PvsNP.encodeAnswer (sepConcatAux f1 f2 [] x)) =
          [sepConcatAux f1 f2 [] x] := rfl
      rw [hid, hid2, Option.map_some, initList_eq_embStk, haltList_eq_embStk]
      exact hspec.1
    · have hbound := hspec.2
      simp only [List.length_nil, Nat.add_zero] at hbound
      exact hbound

theorem sep_exp_bound (k1 k2 n : ℕ) :
    (n + 1) * (2 * n + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2) + 12) ≤
      2 ^ (n ^ (2 * k1 + 2 * k2 + 40)) + (2 * k1 + 2 * k2 + 40) := by
  rcases n with _ | _ | m
  · have h1 : 2 ^ (0 ^ k1) ≤ 2 := by rcases k1 with _ | k <;> simp
    have h2 : 2 ^ (0 ^ k2) ≤ 2 := by rcases k2 with _ | k <;> simp
    have h3 : 0 ^ (2 * k1 + 2 * k2 + 40) = 0 := Nat.zero_pow (by omega)
    rw [h3]
    omega
  · simp only [Nat.zero_add, one_pow]
    omega
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    let K := 2 * k1 + 2 * k2 + 40
    let E := max (N ^ k1) (max (N ^ k2) (N + 1))
    have he1 : 2 ^ (N ^ k1) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have he2 : 2 ^ (N ^ k2) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_right _ _))
    have hN1_lt : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
    have hN1_le_E : N + 1 ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hN1_pow : 2 ^ (N + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hN1_le_E
    have hk1_le : k1 ≤ 2 ^ E := by
      have hk1_pow : k1 ≤ 2 ^ (N ^ k1) := by
        cases k1 with
        | zero => simp
        | succ k' =>
          have h1 : k' + 1 ≤ 2 ^ (k' + 1) := le_of_lt Nat.lt_two_pow_self
          have h2 : 2 ^ (k' + 1) ≤ N ^ (k' + 1) := Nat.pow_le_pow_left hN2 (k' + 1)
          have h3 : N ^ (k' + 1) ≤ 2 ^ (N ^ (k' + 1)) := le_of_lt Nat.lt_two_pow_self
          omega
      omega
    have hk2_le : k2 ≤ 2 ^ E := by
      have hk2_pow : k2 ≤ 2 ^ (N ^ k2) := by
        cases k2 with
        | zero => simp
        | succ k' =>
          have h1 : k' + 1 ≤ 2 ^ (k' + 1) := le_of_lt Nat.lt_two_pow_self
          have h2 : 2 ^ (k' + 1) ≤ N ^ (k' + 1) := Nat.pow_le_pow_left hN2 (k' + 1)
          have h3 : N ^ (k' + 1) ≤ 2 ^ (N ^ (k' + 1)) := le_of_lt Nat.lt_two_pow_self
          omega
      omega
    have hE_pos : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    have hinner : 2 * N + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) + 12 ≤ 2 ^ (E + 5) := by
      have hpow : 2 ^ (E + 5) = 32 * 2 ^ E := by ring
      omega
    have houter : N + 1 ≤ 2 ^ E := by omega
    have hprod : (N + 1) * (2 * N + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) + 12) ≤ 2 ^ (2 * E + 5) := by
      have hmul : (N + 1) * (2 * N + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) + 12) ≤ 2 ^ E * 2 ^ (E + 5) :=
        Nat.mul_le_mul houter hinner
      have hpow : 2 ^ E * 2 ^ (E + 5) = 2 ^ (2 * E + 5) := by
        rw [← pow_add]
        ring_nf
      omega
    have hEK : 2 * E + 5 ≤ N ^ K := by
      have hb1 : 2 * N ^ k1 + 5 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k1 := Nat.one_le_pow k1 N (by omega)
        have hcube : 8 ≤ N ^ 3 := by
          have hc : N ^ 3 = N * (N * N) := by ring
          rw [hc]
          have h4 : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmul : 8 * N ^ k1 ≤ N ^ 3 * N ^ k1 := Nat.mul_le_mul_right _ hcube
        have hpk : N ^ 3 * N ^ k1 = N ^ (k1 + 3) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k1 + 3) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : 2 * N ^ k2 + 5 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k2 := Nat.one_le_pow k2 N (by omega)
        have hcube : 8 ≤ N ^ 3 := by
          have hc : N ^ 3 = N * (N * N) := by ring
          rw [hc]
          have h4 : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmul : 8 * N ^ k2 ≤ N ^ 3 * N ^ k2 := Nat.mul_le_mul_right _ hcube
        have hpk : N ^ 3 * N ^ k2 = N ^ (k2 + 3) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k2 + 3) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb3 : 2 * (N + 1) + 5 ≤ N ^ K := by
        have h4 : 2 * N + 7 ≤ N ^ 4 := by
          have hc : N ^ 4 = N * N * (N * N) := by ring
          rw [hc]
          have hsq : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmon : N ^ 4 ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp only [E, max_def]
      split_ifs <;> omega
    have hpowK : 2 ^ (2 * E + 5) ≤ 2 ^ (N ^ K) := Nat.pow_le_pow_right (by omega) hEK
    change (N + 1) * (2 * N + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) + 12) ≤ 2 ^ (N ^ K) + K
    omega

end PvsNP.Units.tc_exp_sep_concat_aux

theorem PvsNP.Units.tc_exp_sep_concat : ∀ L₁ L₂ : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ u v : List Bool, x = u ++ false :: v ∧ u ∈ L₁ ∧ v ∈ L₂) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L₁ L₂ ⟨k1, f1, M1, hf1, ht1⟩ ⟨k2, f2, M2, hf2, ht2⟩
  refine ⟨2 * k1 + 2 * k2 + 40, PvsNP.Units.tc_exp_sep_concat_aux.sepConcatAux f1 f2 [],
    PvsNP.Units.tc_exp_sep_concat_aux.sepInTime f1 f2 k1 k2 M1 M2 ht1 ht2, fun x => ?_, fun n => ?_⟩
  · rw [PvsNP.Units.tc_exp_sep_concat_aux.sepConcatAux_iff]
    simp only [List.reverse_nil, List.nil_append, hf1, hf2]
  · exact PvsNP.Units.tc_exp_sep_concat_aux.sep_exp_bound k1 k2 n
