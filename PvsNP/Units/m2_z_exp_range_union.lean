import Mathlib
import PvsNP.Defs
import CookLevin

/-
Copied and adapted from settled campaign units in github.com/makedotfun/pvsnp:
  PvsNP/Units/m2_p_trivial.lean (constTM and iterInit for the constant-false decider),
  PvsNP/Units/m2_p_union.lean (unionTM and union_run), and
  PvsNP/Units/m2_exp_union.lean (orInTime and exp_add_bound),
placed inside namespace PvsNP.Units.m2_z_exp_range_union to prove closure of exponential
time under bounded indexed unions by induction on m.
-/

namespace PvsNP.Units.m2_z_exp_range_union

open Turing

def constTM (c : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun _ => TM2.Stmt.pop () (fun _ o => o.isSome)
    (TM2.Stmt.branch id (TM2.Stmt.goto fun _ => ())
      (TM2.Stmt.push () (fun _ => c) TM2.Stmt.halt))

def cfgAt (c : Bool) (v : Bool) (l : List Bool) : (constTM c).Cfg :=
  ⟨some (), v, fun _ => l⟩

def cfgDone (c : Bool) : (constTM c).Cfg :=
  ⟨none, false, fun _ => [c]⟩

theorem step_cons (c v b : Bool) (l : List Bool) :
    (constTM c).step (cfgAt c v (b :: l)) = some (cfgAt c true l) :=
  rfl

theorem step_nil (c v : Bool) :
    (constTM c).step (cfgAt c v []) = some (cfgDone c) :=
  rfl

theorem iter (c : Bool) : ∀ (l : List Bool) (v : Bool),
    (flip bind (constTM c).step)^[l.length + 1] (some (cfgAt c v l)) = some (cfgDone c)
  | [], v => by
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
      exact step_nil c v
  | b :: l, v => by
      rw [List.length_cons, Function.iterate_succ_apply]
      show (flip bind (constTM c).step)^[l.length + 1] ((constTM c).step (cfgAt c v (b :: l))) = _
      rw [step_cons]
      exact iter c l true

theorem initList_eq (c : Bool) (s : List Bool) : initList (constTM c) s = cfgAt c false s :=
  rfl

theorem haltList_eq (c : Bool) : haltList (constTM c) [c] = cfgDone c :=
  rfl

theorem iterInit (c : Bool) (s : List Bool) :
    (flip bind (constTM c).step)^[s.length + 1] (some (initList (constTM c) s)) =
      some (haltList (constTM c) [c]) := by
  rw [initList_eq, haltList_eq]
  exact iter c s false

def constFalseInTime : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun _ : List Bool => false) where
  tm := constTM false
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => n + 1
  outputsFun x :=
    { steps := x.length + 1
      evals_in_steps := by
        have h := iterInit false (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x))
        rw [List.length_map] at h
        exact h
      steps_le_m := le_rfl }

theorem exp_bot :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ (⊥ : Language Bool) ↔ f x = true) ∧
        ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  refine ⟨1, fun _ => false, constFalseInTime, fun x => ?_, fun n => ?_⟩
  · exact ⟨fun h => False.elim h, fun h => Bool.noConfusion h⟩
  · change n + 1 ≤ 2 ^ (n ^ 1) + 1
    have h : n < 2 ^ n := Nat.lt_two_pow_self
    simp only [pow_one]
    omega

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

section unionMachine

variable (M1 M2 : FinTM2)

abbrev UK : Type := Bool ⊕ M1.K ⊕ M2.K

abbrev UΓ : UK M1 M2 → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl k) => M1.Γ k
  | Sum.inr (Sum.inr k) => M2.Γ k

abbrev UΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Fin 4

abbrev Uσ : Type := M1.σ × M2.σ × Option Bool × Bool

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr 2))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr 3))

variable (M1 M2)

def prog (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) :
    UΛ M1 M2 → TM2.Stmt (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr ⟨0, _⟩) =>
      .pop (Sum.inl false) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inl true) (fun s => s.2.2.1.getD false)
            (.goto fun _ => Sum.inr (Sum.inr 0)))
          (.goto fun _ => Sum.inr (Sum.inr 1)))
  | Sum.inr (Sum.inr ⟨1, _⟩) =>
      .pop (Sum.inl true) (fun s o => (s.1, s.2.1, o, s.2.2.2))
        (.branch (fun s => s.2.2.1.isSome)
          (.push (Sum.inr (Sum.inl M1.k₀)) (fun s => in1 (s.2.2.1.getD false))
            (.push (Sum.inr (Sum.inr M2.k₀)) (fun s => in2 (s.2.2.1.getD false))
              (.goto fun _ => Sum.inr (Sum.inr 1))))
          (.goto fun _ => Sum.inl M1.main))
  | Sum.inr (Sum.inr ⟨2, _⟩) =>
      .pop (Sum.inr (Sum.inl M1.k₁))
        (fun s o => (M1.initialState, s.2.1, none, (o.map out1).getD false))
        (.goto fun _ => Sum.inr (Sum.inl M2.main))
  | Sum.inr (Sum.inr ⟨3, _⟩) =>
      .pop (Sum.inr (Sum.inr M2.k₁))
        (fun s o => (M1.initialState, M2.initialState, o.map out2, s.2.2.2))
        (.push (Sum.inl false) (fun s => s.2.2.2 || s.2.2.1.getD false)
          (.load (fun _ => (M1.initialState, M2.initialState, none, false)) .halt))

abbrev unionTM (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
    (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool) : FinTM2 :=
  { K := UK M1 M2
    k₀ := Sum.inl false
    k₁ := Sum.inl false
    Γ := UΓ M1 M2
    Λ := UΛ M1 M2
    main := Sum.inr (Sum.inr 0)
    σ := Uσ M1 M2
    initialState := (M1.initialState, M2.initialState, none, false)
    kFin := @instFintypeSum _ _ inferInstance (@instFintypeSum _ _ M1.kFin M2.kFin)
    ΛFin := @instFintypeSum _ _ M1.ΛFin (@instFintypeSum _ _ M2.ΛFin inferInstance)
    σFin := @instFintypeProd _ _ M1.σFin (@instFintypeProd _ _ M2.σFin inferInstance)
    m := prog M1 M2 in1 out1 in2 out2 }

variable {M1 M2}

def embStk (a b : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    ∀ k, List (UΓ M1 M2 k)
  | Sum.inl false => a
  | Sum.inl true => b
  | Sum.inr (Sum.inl k) => S1 k
  | Sum.inr (Sum.inr k) => S2 k

lemma embStk_upd_in (a a' b : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (embStk a b S1 S2) (Sum.inl false) a' = embStk a' b S1 S2 := by
  funext j
  rcases j with (_ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]

lemma embStk_upd_tmp (a b b' : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) :
    Function.update (embStk a b S1 S2) (Sum.inl true) b' = embStk a b' S1 S2 := by
  funext j
  rcases j with (_ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]

lemma embStk_upd1 (a b : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (k : M1.K) (xs : List (M1.Γ k)) :
    Function.update (embStk a b S1 S2) (Sum.inr (Sum.inl k)) xs =
      embStk a b (Function.update S1 k xs) S2 := by
  funext j
  rcases j with (_ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · by_cases h : j = k
    · subst h
      simp [embStk]
    · simp [embStk, h]
  · simp [embStk]

lemma embStk_upd2 (a b : List Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (k : M2.K) (xs : List (M2.Γ k)) :
    Function.update (embStk a b S1 S2) (Sum.inr (Sum.inr k)) xs =
      embStk a b S1 (Function.update S2 k xs) := by
  funext j
  rcases j with (_ | _) | j | j
  · simp [embStk]
  · simp [embStk]
  · simp [embStk]
  · by_cases h : j = k
    · subst h
      simp [embStk]
    · simp [embStk, h]

def emb1 (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (c : TM2.Cfg M1.Γ M1.Λ M1.σ) : TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr 2)) Sum.inl), (c.var, w), embStk [] [] c.stk S2⟩

def emb2 (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (c : TM2.Cfg M2.Γ M2.Λ M2.σ) : TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr 3)) (fun l => Sum.inr (Sum.inl l))),
    (u1, c.var, t, b1), embStk [] [] S1 c.stk⟩

lemma sim1 (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ) (S1 : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Uσ M1 M2) (embStk [] [] S1 S2) =
      emb1 w S2 (TM2.stepAux q v S1) := by
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
      cases f v
      · exact ih₂ v S1
      · exact ih₁ v S1
  | goto f => rfl
  | halt => rfl

lemma sim2 (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ) (S2 : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u1, v, t, b1) : Uσ M1 M2) (embStk [] [] S1 S2) =
      emb2 u1 t b1 S1 (TM2.stepAux q v S2) := by
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
      cases f v
      · exact ih₂ v S2
      · exact ih₁ v S2
  | goto f => rfl
  | halt => rfl

variable (in1 : Bool → M1.Γ M1.k₀) (out1 : M1.Γ M1.k₁ → Bool)
  (in2 : Bool → M2.Γ M2.k₀) (out2 : M2.Γ M2.k₁ → Bool)

lemma step1 (w : M2.σ × Option Bool × Bool) (S2 : ∀ k, List (M2.Γ k))
    (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ) (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 in1 out1 in2 out2) (emb1 w S2 c) = some (emb1 w S2 c') := by
  obtain ⟨l, v, S1⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step, Option.some.injEq] at h
      subst h
      show some (TM2.stepAux (tr1 (M1.m l)) (v, w) (embStk [] [] S1 S2)) = _
      rw [sim1]

lemma step2 (u1 : M1.σ) (t : Option Bool) (b1 : Bool) (S1 : ∀ k, List (M1.Γ k))
    (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ) (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 in1 out1 in2 out2) (emb2 u1 t b1 S1 c) =
      some (emb2 u1 t b1 S1 c') := by
  obtain ⟨l, v, S2⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step, Option.some.injEq] at h
      subst h
      show some (TM2.stepAux (tr2 (M2.m l)) (u1, v, t, b1) (embStk [] [] S1 S2)) = _
      rw [sim2]

variable (M1 M2)

lemma copyA_run (u1 : M1.σ) (u2 : M2.σ) (b1 : Bool) :
    ∀ (l r : List Bool) (t : Option Bool),
      (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[l.length + 1]
        (some ⟨some (Sum.inr (Sum.inr 0)), (u1, u2, t, b1),
          embStk l r (fun _ => []) (fun _ => [])⟩) =
      some ⟨some (Sum.inr (Sum.inr 1)), (u1, u2, none, b1),
        embStk [] (l.reverse ++ r) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
      intro r t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd_in]
  | cons a l ih =>
      intro r t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2))
          (some ⟨some (Sum.inr (Sum.inr 0)), (u1, u2, t, b1),
            embStk (a :: l) r (fun _ => []) (fun _ => [])⟩) =
          some ⟨some (Sum.inr (Sum.inr 0)), (u1, u2, some a, b1),
            embStk l (a :: r) (fun _ => []) (fun _ => [])⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
          embStk_upd_in, embStk_upd_tmp]
      rw [hs]
      simpa [List.reverse_cons, List.append_assoc] using ih (a :: r) (some a)

lemma copyB_run (u1 : M1.σ) (u2 : M2.σ) (b1 : Bool) :
    ∀ (l : List Bool) (s1 : List (M1.Γ M1.k₀)) (s2 : List (M2.Γ M2.k₀)) (t : Option Bool),
      (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[l.length + 1]
        (some ⟨some (Sum.inr (Sum.inr 1)), (u1, u2, t, b1),
          embStk [] l (Function.update (fun _ => []) M1.k₀ s1)
            (Function.update (fun _ => []) M2.k₀ s2)⟩) =
      some ⟨some (Sum.inl M1.main), (u1, u2, none, b1),
        embStk [] []
          (Function.update (fun _ => []) M1.k₀ (l.reverse.map in1 ++ s1))
          (Function.update (fun _ => []) M2.k₀ (l.reverse.map in2 ++ s2))⟩ := by
  intro l
  induction l with
  | nil =>
      intro s1 s2 t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.map_nil, List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux,
        embStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd_tmp]
  | cons a l ih =>
      intro s1 s2 t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2))
          (some ⟨some (Sum.inr (Sum.inr 1)), (u1, u2, t, b1),
            embStk [] (a :: l) (Function.update (fun _ => []) M1.k₀ s1)
              (Function.update (fun _ => []) M2.k₀ s2)⟩) =
          some ⟨some (Sum.inr (Sum.inr 1)), (u1, u2, some a, b1),
            embStk [] l (Function.update (fun _ => []) M1.k₀ (in1 a :: s1))
              (Function.update (fun _ => []) M2.k₀ (in2 a :: s2))⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
          embStk_upd_tmp, embStk_upd1, embStk_upd2, Function.update_self, Function.update_idem]
      rw [hs]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (in1 a :: s1) (in2 a :: s2) (some a)

lemma initList_eq_embStk (x : List Bool) :
    (initList (unionTM M1 M2 in1 out1 in2 out2) x : TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)) =
      ⟨some (Sum.inr (Sum.inr 0)), (M1.initialState, M2.initialState, none, false),
        embStk x [] (fun _ => []) (fun _ => [])⟩ := by
  unfold initList unionTM
  congr 1
  funext j
  rcases j with (_ | _) | j | j <;> simp [embStk]

lemma haltList_eq_embStk (y : List Bool) :
    (haltList (unionTM M1 M2 in1 out1 in2 out2) y : TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)) =
      ⟨none, (M1.initialState, M2.initialState, none, false),
        embStk y [] (fun _ => []) (fun _ => [])⟩ := by
  unfold haltList unionTM
  congr 1
  funext j
  rcases j with (_ | _) | j | j <;> simp [embStk]

lemma initList_stk_eq (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  unfold initList
  by_cases h : k = M.k₀
  · subst h; simp
  · simp [h]

lemma haltList_stk_eq (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = Function.update (fun _ => []) M.k₁ s := by
  funext k
  unfold haltList
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [h]

lemma union_run (x : List Bool) (y1 : M1.Γ M1.k₁) (y2 : M2.Γ M2.k₁) (n1 n2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[n1] (some (initList M1 (x.map in1))) =
      some (haltList M1 [y1]))
    (h2 : (flip bind (TM2.step M2.m))^[n2] (some (initList M2 (x.map in2))) =
      some (haltList M2 [y2])) :
    (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[
        1 + (n2 + (1 + (n1 + ((x.length + 1) + (x.length + 1)))))]
      (some (initList (unionTM M1 M2 in1 out1 in2 out2) x :
        TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2))) =
    some (haltList (unionTM M1 M2 in1 out1 in2 out2) [out1 y1 || out2 y2] :
      TM2.Cfg (UΓ M1 M2) (UΛ M1 M2) (Uσ M1 M2)) := by
  have pA := copyA_run M1 M2 in1 out1 in2 out2 M1.initialState M2.initialState false x [] none
  simp only [List.append_nil] at pA
  have pB := copyB_run M1 M2 in1 out1 in2 out2 M1.initialState M2.initialState false x.reverse [] []
    none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
    Function.update_eq_self] at pB
  have h1' := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 in1 out1 in2 out2))
    (emb1 (M2.initialState, none, false) (Function.update (fun _ => []) M2.k₀ (x.map in2)))
    (step1 in1 out1 in2 out2 _ _) n1 _ _ h1
  have he1_in : emb1 (M2.initialState, none, false)
      (Function.update (fun _ => []) M2.k₀ (x.map in2)) (initList M1 (x.map in1)) =
      ⟨some (Sum.inl M1.main), (M1.initialState, M2.initialState, none, false),
        embStk [] [] (Function.update (fun _ => []) M1.k₀ (x.map in1))
          (Function.update (fun _ => []) M2.k₀ (x.map in2))⟩ := by
    unfold emb1
    rw [initList_stk_eq]
    rfl
  have he1_out : emb1 (M2.initialState, none, false)
      (Function.update (fun _ => []) M2.k₀ (x.map in2)) (haltList M1 [y1]) =
      ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, none, false),
        embStk [] [] (Function.update (fun _ => []) M1.k₁ [y1])
          (Function.update (fun _ => []) M2.k₀ (x.map in2))⟩ := by
    unfold emb1
    rw [haltList_stk_eq]
    rfl
  rw [he1_in, he1_out] at h1'
  have pAfter1 : (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[1]
      (some ⟨some (Sum.inr (Sum.inr 2)), (M1.initialState, M2.initialState, none, false),
        embStk [] [] (Function.update (fun _ => []) M1.k₁ [y1])
          (Function.update (fun _ => []) M2.k₀ (x.map in2))⟩) =
      some ⟨some (Sum.inr (Sum.inl M2.main)),
        (M1.initialState, M2.initialState, none, out1 y1),
        embStk [] [] (fun _ => []) (Function.update (fun _ => []) M2.k₀ (x.map in2))⟩ := by
    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux,
      embStk, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
      Option.getD_some, embStk_upd1, Function.update_idem, Function.update_eq_self]
  have h2' := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 in1 out1 in2 out2))
    (emb2 M1.initialState none (out1 y1) (fun _ => []))
    (step2 in1 out1 in2 out2 _ _ _ _) n2 _ _ h2
  have he2_in : emb2 M1.initialState none (out1 y1) (fun _ => []) (initList M2 (x.map in2)) =
      ⟨some (Sum.inr (Sum.inl M2.main)),
        (M1.initialState, M2.initialState, none, out1 y1),
        embStk [] [] (fun _ => []) (Function.update (fun _ => []) M2.k₀ (x.map in2))⟩ := by
    unfold emb2
    rw [initList_stk_eq]
    rfl
  have he2_out : emb2 M1.initialState none (out1 y1) (fun _ => []) (haltList M2 [y2]) =
      ⟨some (Sum.inr (Sum.inr 3)),
        (M1.initialState, M2.initialState, none, out1 y1),
        embStk [] [] (fun _ => []) (Function.update (fun _ => []) M2.k₁ [y2])⟩ := by
    unfold emb2
    rw [haltList_stk_eq]
    rfl
  rw [he2_in, he2_out] at h2'
  have pFin : (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[1]
      (some ⟨some (Sum.inr (Sum.inr 3)),
        (M1.initialState, M2.initialState, none, out1 y1),
        embStk [] [] (fun _ => []) (Function.update (fun _ => []) M2.k₁ [y2])⟩) =
      some ⟨none, (M1.initialState, M2.initialState, none, false),
        embStk [out1 y1 || out2 y2] [] (fun _ => []) (fun _ => [])⟩ := by
    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux,
      embStk, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
      Option.getD_some, embStk_upd2, Function.update_idem, Function.update_eq_self, embStk_upd_in]
  have hmid :
      (flip bind (TM2.step (prog M1 M2 in1 out1 in2 out2)))^[
          1 + (n2 + (1 + (n1 + ((x.length + 1) + (x.length + 1)))))]
        (some ⟨some (Sum.inr (Sum.inr 0)), (M1.initialState, M2.initialState, none, false),
          embStk x [] (fun _ => []) (fun _ => [])⟩) =
      some ⟨none, (M1.initialState, M2.initialState, none, false),
        embStk [out1 y1 || out2 y2] [] (fun _ => []) (fun _ => [])⟩ := by
    rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_add_apply,
      pA, pB, h1', pAfter1, h2', pFin]
  rw [← initList_eq_embStk M1 M2 in1 out1 in2 out2 x,
    ← haltList_eq_embStk M1 M2 in1 out1 in2 out2 [out1 y1 || out2 y2]] at hmid
  exact hmid

end unionMachine

def orInTime (f1 f2 : List Bool → Bool)
    (c1 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f1)
    (c2 : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f2) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (fun x => f1 x || f2 x) where
  tm := unionTM c1.tm c2.tm c1.inputAlphabet.invFun c1.outputAlphabet
    c2.inputAlphabet.invFun c2.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => 2 * n + 4 + c1.time n + c2.time n
  outputsFun x := by
    have r1 := c1.outputsFun x
    have r2 := c2.outputsFun x
    have hrun := union_run c1.tm c2.tm
      c1.inputAlphabet.invFun c1.outputAlphabet
      c2.inputAlphabet.invFun c2.outputAlphabet x
      (c1.outputAlphabet.invFun (f1 x)) (c2.outputAlphabet.invFun (f2 x))
      r1.steps r2.steps r1.evals_in_steps r2.evals_in_steps
    have ho1 : c1.outputAlphabet (c1.outputAlphabet.invFun (f1 x)) = f1 x :=
      c1.outputAlphabet.right_inv (f1 x)
    have ho2 : c2.outputAlphabet (c2.outputAlphabet.invFun (f2 x)) = f2 x :=
      c2.outputAlphabet.right_inv (f2 x)
    rw [ho1, ho2] at hrun
    refine ⟨⟨1 + (r2.steps + (1 + (r1.steps + ((x.length + 1) + (x.length + 1))))), ?_⟩, ?_⟩
    · have hid : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := List.map_id x
      rw [hid]
      exact hrun
    · have b1 := r1.steps_le_m
      have b2 := r2.steps_le_m
      change 1 + (r2.steps + (1 + (r1.steps + ((x.length + 1) + (x.length + 1))))) ≤
        2 * (PvsNP.encodeString x).length + 4 +
          c1.time (PvsNP.encodeString x).length +
          c2.time (PvsNP.encodeString x).length
      have hlen : (PvsNP.encodeString x).length = x.length := rfl
      omega

theorem exp_add_bound (k1 k2 n : ℕ) :
    2 * n + 4 + (2 ^ (n ^ k1) + k1) + (2 ^ (n ^ k2) + k2) ≤
      2 ^ (n ^ (k1 + k2 + 10)) + (k1 + k2 + 10) := by
  rcases n with _ | _ | m
  · have h1 : 2 ^ (0 ^ k1) ≤ 2 := by rcases k1 with _ | k <;> simp
    have h2 : 2 ^ (0 ^ k2) ≤ 2 := by rcases k2 with _ | k <;> simp
    have h3 : 0 ^ (k1 + k2 + 10) = 0 := Nat.zero_pow (by omega)
    rw [h3]
    omega
  · simp only [Nat.zero_add, one_pow]
    omega
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    let K := k1 + k2 + 10
    let E := max (N ^ k1) (max (N ^ k2) (N + 1))
    have he1 : 2 ^ (N ^ k1) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have he2 : 2 ^ (N ^ k2) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_right _ _))
    have he3 : 2 * N + 4 ≤ 2 * 2 ^ E := by
      have hlt : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
      have hle : N + 1 ≤ E := (le_max_right _ _).trans (le_max_right _ _)
      have hp : 2 ^ (N + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) hle
      omega
    have hsum : 2 * N + 4 + 2 ^ (N ^ k1) + 2 ^ (N ^ k2) ≤ 2 ^ (E + 2) := by
      have hpow : 2 ^ (E + 2) = 4 * 2 ^ E := by ring
      omega
    have hEK : E + 2 ≤ N ^ K := by
      have hb1 : N ^ k1 + 2 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k1 := Nat.one_le_pow k1 N (by omega)
        have hsq : 4 ≤ N ^ 2 := by nlinarith
        have hmul : 4 * N ^ k1 ≤ N ^ 2 * N ^ k1 := Nat.mul_le_mul_right _ hsq
        have hpk : N ^ 2 * N ^ k1 = N ^ (k1 + 2) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k1 + 2) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : N ^ k2 + 2 ≤ N ^ K := by
        have hpos : 1 ≤ N ^ k2 := Nat.one_le_pow k2 N (by omega)
        have hsq : 4 ≤ N ^ 2 := by nlinarith
        have hmul : 4 * N ^ k2 ≤ N ^ 2 * N ^ k2 := Nat.mul_le_mul_right _ hsq
        have hpk : N ^ 2 * N ^ k2 = N ^ (k2 + 2) := by rw [Nat.pow_add, Nat.mul_comm]
        have hmon : N ^ (k2 + 2) ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb3 : (N + 1) + 2 ≤ N ^ K := by
        have hcube : N + 3 ≤ N ^ 3 := by
          have hc : N ^ 3 = N * (N * N) := by ring
          rw [hc]
          have h4 : 4 ≤ N * N := Nat.mul_le_mul hN2 hN2
          nlinarith
        have hmon : N ^ 3 ≤ N ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp only [E, max_def]
      split_ifs <;> omega
    have hpowK : 2 ^ (E + 2) ≤ 2 ^ (N ^ K) := Nat.pow_le_pow_right (by omega) hEK
    change 2 * N + 4 + (2 ^ (N ^ k1) + k1) + (2 ^ (N ^ k2) + k2) ≤ 2 ^ (N ^ K) + K
    have hKdef : K = k1 + k2 + 10 := rfl
    omega


theorem exp_union (L₁ L₂ : Language Bool)
    (h1 : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)
    (h2 : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ⊔ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rcases h1 with ⟨k1, f1, M1, hf1, ht1⟩
  rcases h2 with ⟨k2, f2, M2, hf2, ht2⟩
  refine ⟨k1 + k2 + 10, fun x => f1 x || f2 x, orInTime f1 f2 M1 M2, fun x => ?_, fun n => ?_⟩
  · change x ∈ L₁ ∨ x ∈ L₂ ↔ (f1 x || f2 x) = true
    rw [hf1 x, hf2 x, Bool.or_eq_true]
  · have b1 := ht1 n
    have b2 := ht2 n
    have bound := exp_add_bound k1 k2 n
    show 2 * n + 4 + M1.time n + M2.time n ≤ 2 ^ (n ^ (k1 + k2 + 10)) + (k1 + k2 + 10)
    omega

end PvsNP.Units.m2_z_exp_range_union

theorem PvsNP.Units.m2_z_exp_range_union :
    ∀ (F : ℕ → Language Bool) (m : ℕ),
      (∀ i < m, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ F i ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  intro F m
  induction m with
  | zero =>
    intro _
    obtain ⟨k, f, M, hf, ht⟩ := PvsNP.Units.m2_z_exp_range_union.exp_bot
    refine ⟨k, f, M, fun x => ?_, ht⟩
    have hx : x ∈ ({x : List Bool | ∃ i < 0, x ∈ F i} : Language Bool) ↔ x ∈ (⊥ : Language Bool) := by
      change (∃ i < 0, x ∈ F i) ↔ False
      simp
    exact hx.trans (hf x)
  | succ m ih =>
    intro hF
    have hm := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have hlast := hF m (Nat.lt_succ_self m)
    obtain ⟨k, f, M, hf, ht⟩ := PvsNP.Units.m2_z_exp_range_union.exp_union _ _ hm hlast
    refine ⟨k, f, M, fun x => ?_, ht⟩
    have hx : x ∈ ({x : List Bool | ∃ i < m + 1, x ∈ F i} : Language Bool) ↔
        x ∈ (({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ⊔ F m) := by
      change (∃ i < m + 1, x ∈ F i) ↔ (∃ i < m, x ∈ F i) ∨ x ∈ F m
      constructor
      · rintro ⟨i, hi, hxi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl ⟨i, hlt, hxi⟩
        · exact Or.inr hxi
      · rintro (⟨i, hi, hxi⟩ | hxi)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hxi⟩
        · exact ⟨m, Nat.lt_succ_self m, hxi⟩
    exact hx.trans (hf x)
