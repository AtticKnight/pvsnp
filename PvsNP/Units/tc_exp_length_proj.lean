import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_length_proj_aux

open Turing

/-! ### Helper lemmas for step iteration and submachine simulation -/

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

/-! ### Binary counter (LSB-first) and enumeration of fixed-length bitstrings -/

def val : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * val bs

def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, m => (m % 2 == 1) :: bits n (m / 2)

def inc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (inc bs).map (false :: ·)

lemma bits_length (n m : ℕ) : (bits n m).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => simp [bits, ih]

lemma bits_zero (n : ℕ) : bits n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bits, List.replicate_succ, ih]

lemma val_lt (y : List Bool) : val y < 2 ^ y.length := by
  induction y with
  | nil => simp [val]
  | cons b bs ih =>
      simp only [val, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

lemma bits_val (y : List Bool) : bits y.length (val y) = y := by
  induction y with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.length_cons, bits, val]
      cases b with
      | false =>
          simp [ih]
      | true =>
          have h1 : (1 + 2 * val bs) % 2 = 1 := by omega
          have h2 : (1 + 2 * val bs) / 2 = val bs := by omega
          simp [h1, h2, ih]

lemma inc_bits_some (n m : ℕ) (h : m + 1 < 2 ^ n) :
    inc (bits n m) = some (bits n (m + 1)) := by
  induction n generalizing m with
  | zero => simp at h
  | succ n ih =>
      simp only [bits]
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · have h1 : (m + 1) % 2 = 1 := by omega
        have h2 : (m + 1) / 2 = m / 2 := by omega
        simp [hm, h1, h2, inc]
      · have h1 : (m + 1) % 2 = 0 := by omega
        have h2 : (m + 1) / 2 = m / 2 + 1 := by omega
        have hlt : m / 2 + 1 < 2 ^ n := by
          rw [pow_succ] at h
          omega
        simp [hm, h1, h2, inc, ih (m / 2) hlt]

lemma inc_bits_none (n m : ℕ) (h : m + 1 = 2 ^ n) :
    inc (bits n m) = none := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
      have hm : m % 2 = 1 := by
        rw [pow_succ] at h
        omega
      have hd : m / 2 + 1 = 2 ^ n := by
        rw [pow_succ] at h
        omega
      simp [bits, hm, inc, ih (m / 2) hd]

def evalRange (f : List Bool → Bool) (n : ℕ) : ℕ → ℕ → Bool → Bool
  | 0, _, acc => acc
  | rem + 1, m, acc => evalRange f n rem (m + 1) (acc || f (bits n m))

lemma evalRange_eq_true (f : List Bool → Bool) (n rem m : ℕ) (acc : Bool) :
    evalRange f n rem m acc = true ↔
      acc = true ∨ ∃ j, m ≤ j ∧ j < m + rem ∧ f (bits n j) = true := by
  induction rem generalizing m acc with
  | zero =>
      simp only [evalRange, Nat.add_zero]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨j, h1, h2, _⟩)
        · exact h
        · omega
  | succ rem ih =>
      simp only [evalRange]
      rw [ih (m + 1) (acc || f (bits n m)), Bool.or_eq_true]
      constructor
      · rintro ((ha | hf) | ⟨j, h1, h2, hj⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨m, le_rfl, by omega, hf⟩
        · exact Or.inr ⟨j, by omega, by omega, hj⟩
      · rintro (ha | ⟨j, h1, h2, hj⟩)
        · exact Or.inl (Or.inl ha)
        · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact Or.inl (Or.inr hj)
          · exact Or.inr ⟨j, by omega, by omega, hj⟩

def lengthProjFun (f : List Bool → Bool) (x : List Bool) : Bool :=
  evalRange f x.length (2 ^ x.length) 0 false

lemma lengthProjFun_spec (f : List Bool → Bool) (x : List Bool) :
    lengthProjFun f x = true ↔ ∃ y : List Bool, y.length = x.length ∧ f y = true := by
  unfold lengthProjFun
  rw [evalRange_eq_true]
  constructor
  · rintro (h | ⟨j, _, _, hj⟩)
    · exact absurd h (by decide)
    · exact ⟨bits x.length j, bits_length x.length j, hj⟩
  · rintro ⟨y, hlen, hy⟩
    refine Or.inr ⟨val y, Nat.zero_le _, ?_, ?_⟩
    · rw [Nat.zero_add, ← hlen]
      exact val_lt y
    · rw [← hlen, bits_val]
      exact hy

/-! ### FinTM2 enumerating all strings of length `x.length` and running `M` -/

section projMachine

variable (M : FinTM2)

abbrev PK : Type := Fin 3 ⊕ M.K

abbrev PΓ : PK M → Type
  | Sum.inl _ => Bool
  | Sum.inr k => M.Γ k

abbrev PΛ : Type := M.Λ ⊕ Fin 7

abbrev Pσ : Type := M.σ × Option Bool × Bool

variable {M}

def trM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (PΓ M) (PΛ M) (Pσ M)
  | .push k f q => .push (Sum.inr k) (fun s => f s.1) (trM q)
  | .peek k f q => .peek (Sum.inr k) (fun s o => (f s.1 o, s.2)) (trM q)
  | .pop k f q => .pop (Sum.inr k) (fun s o => (f s.1 o, s.2)) (trM q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trM q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trM q₁) (trM q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr 3)

variable (M)

def prog (inM : Bool → M.Γ M.k₀) (outM : M.Γ M.k₁ → Bool) :
    PΛ M → TM2.Stmt (PΓ M) (PΛ M) (Pσ M)
  | Sum.inl l => trM (M.m l)
  | Sum.inr ⟨0, _⟩ =>
      .pop (Sum.inl 0) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.push (Sum.inl 1) (fun _ => false)
            (.goto fun _ => Sum.inr 0))
          (.goto fun _ => Sum.inr 1))
  | Sum.inr ⟨1, _⟩ =>
      .pop (Sum.inl 1) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.push (Sum.inl 2) (fun s => s.2.1.getD false)
            (.goto fun _ => Sum.inr 1))
          (.goto fun _ => Sum.inr 2))
  | Sum.inr ⟨2, _⟩ =>
      .pop (Sum.inl 2) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.push (Sum.inl 1) (fun s => s.2.1.getD false)
            (.push (Sum.inr M.k₀) (fun s => inM (s.2.1.getD false))
              (.goto fun _ => Sum.inr 2)))
          (.goto fun _ => Sum.inl M.main))
  | Sum.inr ⟨3, _⟩ =>
      .pop (Sum.inr M.k₁) (fun s o => (M.initialState, none, s.2.2 || (o.map outM).getD false))
        (.goto fun _ => Sum.inr 4)
  | Sum.inr ⟨4, _⟩ =>
      .pop (Sum.inl 1) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.branch (fun s => s.2.1.getD false)
            (.push (Sum.inl 2) (fun _ => false)
              (.goto fun _ => Sum.inr 4))
            (.push (Sum.inl 1) (fun _ => true)
              (.goto fun _ => Sum.inr 5)))
          (.goto fun _ => Sum.inr 6))
  | Sum.inr ⟨5, _⟩ =>
      .pop (Sum.inl 2) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.push (Sum.inl 1) (fun s => s.2.1.getD false)
            (.goto fun _ => Sum.inr 5))
          (.goto fun _ => Sum.inr 1))
  | Sum.inr ⟨6, _⟩ =>
      .pop (Sum.inl 2) (fun s o => (s.1, o, s.2.2))
        (.branch (fun s => s.2.1.isSome)
          (.goto fun _ => Sum.inr 6)
          (.push (Sum.inl 0) (fun s => s.2.2)
            (.load (fun _ => (M.initialState, none, false)) .halt)))

abbrev projTM (inM : Bool → M.Γ M.k₀) (outM : M.Γ M.k₁ → Bool) : FinTM2 :=
  { K := PK M
    k₀ := Sum.inl 0
    k₁ := Sum.inl 0
    Γ := PΓ M
    Λ := PΛ M
    main := Sum.inr 0
    σ := Pσ M
    initialState := (M.initialState, none, false)
    kFin := @instFintypeSum _ _ inferInstance M.kFin
    ΛFin := @instFintypeSum _ _ M.ΛFin inferInstance
    σFin := @instFintypeProd _ _ M.σFin inferInstance
    m := prog M inM outM }

variable {M}

def embStk (s0 cur tmp : List Bool) (SM : ∀ k, List (M.Γ k)) : ∀ k, List (PΓ M k)
  | Sum.inl ⟨0, _⟩ => s0
  | Sum.inl ⟨1, _⟩ => cur
  | Sum.inl ⟨2, _⟩ => tmp
  | Sum.inr k => SM k

lemma embStk_upd0 (s0 s0' cur tmp : List Bool) (SM : ∀ k, List (M.Γ k)) :
    Function.update (embStk s0 cur tmp SM) (Sum.inl 0) s0' = embStk s0' cur tmp SM := by
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · simp [embStk]

lemma embStk_upd1 (s0 cur cur' tmp : List Bool) (SM : ∀ k, List (M.Γ k)) :
    Function.update (embStk s0 cur tmp SM) (Sum.inl 1) cur' = embStk s0 cur' tmp SM := by
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · simp [embStk]

lemma embStk_upd2 (s0 cur tmp tmp' : List Bool) (SM : ∀ k, List (M.Γ k)) :
    Function.update (embStk s0 cur tmp SM) (Sum.inl 2) tmp' = embStk s0 cur tmp' SM := by
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · simp [embStk]

lemma embStk_updM (s0 cur tmp : List Bool) (SM : ∀ k, List (M.Γ k))
    (k : M.K) (xs : List (M.Γ k)) :
    Function.update (embStk s0 cur tmp SM) (Sum.inr k) xs =
      embStk s0 cur tmp (Function.update SM k xs) := by
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · by_cases h : j = k
    · subst h; simp [embStk]
    · simp [embStk, h]

def embM (cur : List Bool) (w : Option Bool × Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (PΓ M) (PΛ M) (Pσ M) :=
  ⟨some (c.l.elim (Sum.inr 3) Sum.inl), (c.var, w), embStk [] cur [] c.stk⟩

lemma simM (cur : List Bool) (w : Option Bool × Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (SM : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trM q) ((v, w) : Pσ M) (embStk [] cur [] SM) =
      embM cur w (TM2.stepAux q v SM) := by
  induction q generalizing v SM with
  | push k f q ih =>
      simp only [trM, TM2.stepAux]
      rw [embStk_updM]
      exact ih v (Function.update SM k (f v :: SM k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      simp only [trM, TM2.stepAux]
      rw [embStk_updM]
      exact ih (f v (SM k).head?) (Function.update SM k (SM k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [trM, TM2.stepAux]
      cases f v
      · exact ih₂ v SM
      · exact ih₁ v SM
  | goto f => rfl
  | halt => rfl

variable (inM : Bool → M.Γ M.k₀) (outM : M.Γ M.k₁ → Bool)

lemma stepM (cur : List Bool) (w : Option Bool × Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (prog M inM outM) (embM cur w c) = some (embM cur w c') := by
  obtain ⟨l, v, SM⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step, Option.some.injEq] at h
      subst h
      show some (TM2.stepAux (trM (M.m l)) (v, w) (embStk [] cur [] SM)) = _
      rw [simM]

variable (M)

lemma init_run (u : M.σ) (acc : Bool) :
    ∀ (x cur : List Bool) (t : Option Bool),
      (flip bind (TM2.step (prog M inM outM)))^[x.length + 1]
        (some ⟨some (Sum.inr 0), (u, t, acc), embStk x cur [] (fun _ => [])⟩) =
      some ⟨some (Sum.inr 1), (u, none, acc),
        embStk [] (List.replicate x.length false ++ cur) [] (fun _ => [])⟩ := by
  intro x
  induction x with
  | nil =>
      intro cur t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.replicate_zero,
        List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd0]
  | cons a x ih =>
      intro cur t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M inM outM))
          (some ⟨some (Sum.inr 0), (u, t, acc), embStk (a :: x) cur [] (fun _ => [])⟩) =
          some ⟨some (Sum.inr 0), (u, some a, acc),
            embStk x (false :: cur) [] (fun _ => [])⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
          embStk_upd0, embStk_upd1]
      rw [hs]
      have hrep : List.replicate (x.length + 1) false ++ cur =
          List.replicate x.length false ++ (false :: cur) := by
        rw [List.replicate_succ', List.append_assoc]; rfl
      rw [hrep]
      exact ih (false :: cur) (some a)

lemma copyA_run (u : M.σ) (acc : Bool) :
    ∀ (l r : List Bool) (t : Option Bool),
      (flip bind (TM2.step (prog M inM outM)))^[l.length + 1]
        (some ⟨some (Sum.inr 1), (u, t, acc), embStk [] l r (fun _ => [])⟩) =
      some ⟨some (Sum.inr 2), (u, none, acc),
        embStk [] [] (l.reverse ++ r) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
      intro r t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd1]
  | cons a l ih =>
      intro r t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M inM outM))
          (some ⟨some (Sum.inr 1), (u, t, acc), embStk [] (a :: l) r (fun _ => [])⟩) =
          some ⟨some (Sum.inr 1), (u, some a, acc), embStk [] l (a :: r) (fun _ => [])⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
          embStk_upd1, embStk_upd2]
      rw [hs]
      simpa [List.reverse_cons, List.append_assoc] using ih (a :: r) (some a)

lemma copyB_run (u : M.σ) (acc : Bool) :
    ∀ (l cur : List Bool) (sM : List (M.Γ M.k₀)) (t : Option Bool),
      (flip bind (TM2.step (prog M inM outM)))^[l.length + 1]
        (some ⟨some (Sum.inr 2), (u, t, acc),
          embStk [] cur l (Function.update (fun _ => []) M.k₀ sM)⟩) =
      some ⟨some (Sum.inl M.main), (u, none, acc),
        embStk [] (l.reverse ++ cur) []
          (Function.update (fun _ => []) M.k₀ (l.reverse.map inM ++ sM))⟩ := by
  intro l
  induction l with
  | nil =>
      intro cur sM t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.map_nil, List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux,
        embStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd2]
  | cons a l ih =>
      intro cur sM t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M inM outM))
          (some ⟨some (Sum.inr 2), (u, t, acc),
            embStk [] cur (a :: l) (Function.update (fun _ => []) M.k₀ sM)⟩) =
          some ⟨some (Sum.inr 2), (u, some a, acc),
            embStk [] (a :: cur) l (Function.update (fun _ => []) M.k₀ (inM a :: sM))⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
          embStk_upd1, embStk_upd2, embStk_updM, Function.update_self, Function.update_idem]
      rw [hs]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (a :: cur) (inM a :: sM) (some a)

lemma restore_run (u : M.σ) (acc : Bool) :
    ∀ (tmp cur : List Bool) (t : Option Bool),
      (flip bind (TM2.step (prog M inM outM)))^[tmp.length + 1]
        (some ⟨some (Sum.inr 5), (u, t, acc), embStk [] cur tmp (fun _ => [])⟩) =
      some ⟨some (Sum.inr 1), (u, none, acc),
        embStk [] (tmp.reverse ++ cur) [] (fun _ => [])⟩ := by
  intro tmp
  induction tmp with
  | nil =>
      intro cur t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, embStk_upd2]
  | cons a tmp ih =>
      intro cur t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M inM outM))
          (some ⟨some (Sum.inr 5), (u, t, acc), embStk [] cur (a :: tmp) (fun _ => [])⟩) =
          some ⟨some (Sum.inr 5), (u, some a, acc),
            embStk [] (a :: cur) tmp (fun _ => [])⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
          embStk_upd1, embStk_upd2]
      rw [hs]
      simpa [List.reverse_cons, List.append_assoc] using ih (a :: cur) (some a)

lemma clear_run (u : M.σ) (acc : Bool) :
    ∀ (tmp : List Bool) (t : Option Bool),
      (flip bind (TM2.step (prog M inM outM)))^[tmp.length + 1]
        (some ⟨some (Sum.inr 6), (u, t, acc), embStk [] [] tmp (fun _ => [])⟩) =
      some ⟨none, (M.initialState, none, false), embStk [acc] [] [] (fun _ => [])⟩ := by
  intro tmp
  induction tmp with
  | nil =>
      intro t
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, List.tail_nil, Option.isSome_none,
        Bool.cond_false, embStk_upd2, embStk_upd0]
  | cons a tmp ih =>
      intro t
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply]
      have hs : flip bind (TM2.step (prog M inM outM))
          (some ⟨some (Sum.inr 6), (u, t, acc), embStk [] [] (a :: tmp) (fun _ => [])⟩) =
          some ⟨some (Sum.inr 6), (u, some a, acc), embStk [] [] tmp (fun _ => [])⟩ := by
        simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
          List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, embStk_upd2]
      rw [hs]
      exact ih (some a)

lemma inc_some_run (u : M.σ) (acc : Bool) :
    ∀ (y y' tmp : List Bool) (t : Option Bool),
      inc y = some y' →
      ∃ s ≤ 2 * y.length + tmp.length + 2,
        (flip bind (TM2.step (prog M inM outM)))^[s]
          (some ⟨some (Sum.inr 4), (u, t, acc), embStk [] y tmp (fun _ => [])⟩) =
        some ⟨some (Sum.inr 1), (u, none, acc),
          embStk [] (tmp.reverse ++ y') [] (fun _ => [])⟩ := by
  intro y
  induction y with
  | nil =>
      intro y' tmp t h
      simp [inc] at h
  | cons b bs ih =>
      intro y' tmp t h
      cases b with
      | false =>
          simp only [inc, Option.some.injEq] at h
          subst h
          have hs1 : flip bind (TM2.step (prog M inM outM))
              (some ⟨some (Sum.inr 4), (u, t, acc),
                embStk [] (false :: bs) tmp (fun _ => [])⟩) =
              some ⟨some (Sum.inr 5), (u, some false, acc),
                embStk [] (true :: bs) tmp (fun _ => [])⟩ := by
            simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
              List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
              Bool.cond_false, embStk_upd1]
          have hrest := restore_run M inM outM u acc tmp (true :: bs) (some false)
          refine ⟨(tmp.length + 1) + 1, by simp only [List.length_cons]; omega, ?_⟩
          rw [Function.iterate_add_apply, Function.iterate_one, hs1, hrest]
      | true =>
          simp only [inc, Option.map_eq_some_iff] at h
          obtain ⟨bs', hbs', rfl⟩ := h
          have hs1 : flip bind (TM2.step (prog M inM outM))
              (some ⟨some (Sum.inr 4), (u, t, acc),
                embStk [] (true :: bs) tmp (fun _ => [])⟩) =
              some ⟨some (Sum.inr 4), (u, some true, acc),
                embStk [] bs (false :: tmp) (fun _ => [])⟩ := by
            simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
              List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
              embStk_upd1, embStk_upd2]
          obtain ⟨s, hsle, hrun⟩ := ih bs' (false :: tmp) (some true) hbs'
          refine ⟨s + 1, by simp at hsle ⊢; omega, ?_⟩
          rw [Function.iterate_add_apply, Function.iterate_one, hs1]
          simpa [List.reverse_cons, List.append_assoc] using hrun

lemma inc_none_run (u : M.σ) (acc : Bool) :
    ∀ (y tmp : List Bool) (t : Option Bool),
      inc y = none →
      ∃ tmp', tmp'.length = y.length + tmp.length ∧
        (flip bind (TM2.step (prog M inM outM)))^[y.length + 1]
          (some ⟨some (Sum.inr 4), (u, t, acc), embStk [] y tmp (fun _ => [])⟩) =
        some ⟨some (Sum.inr 6), (u, none, acc), embStk [] [] tmp' (fun _ => [])⟩ := by
  intro y
  induction y with
  | nil =>
      intro tmp t _
      refine ⟨tmp, by simp, ?_⟩
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip, bind, Option.bind_some,
        TM2.step, prog, TM2.stepAux, embStk, List.head?_nil, List.tail_nil, Option.isSome_none,
        Bool.cond_false, embStk_upd1]
  | cons b bs ih =>
      intro tmp t h
      cases b with
      | false => simp [inc] at h
      | true =>
          simp only [inc, Option.map_eq_none_iff] at h
          have hs1 : flip bind (TM2.step (prog M inM outM))
              (some ⟨some (Sum.inr 4), (u, t, acc),
                embStk [] (true :: bs) tmp (fun _ => [])⟩) =
              some ⟨some (Sum.inr 4), (u, some true, acc),
                embStk [] bs (false :: tmp) (fun _ => [])⟩ := by
            simp only [flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux, embStk,
              List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some,
              embStk_upd1, embStk_upd2]
          obtain ⟨tmp', hlen, hrun⟩ := ih (false :: tmp) (some true) h
          refine ⟨tmp', by simp at hlen ⊢; omega, ?_⟩
          simp only [List.length_cons, Nat.add_assoc]
          rw [Function.iterate_succ_apply, hs1]
          exact hrun

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

lemma initList_eq_embStk (x : List Bool) :
    (initList (projTM M inM outM) x : TM2.Cfg (PΓ M) (PΛ M) (Pσ M)) =
      ⟨some (Sum.inr 0), (M.initialState, none, false), embStk x [] [] (fun _ => [])⟩ := by
  unfold initList projTM
  congr 1
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · simp [embStk]

lemma haltList_eq_embStk (y : List Bool) :
    (haltList (projTM M inM outM) y : TM2.Cfg (PΓ M) (PΛ M) (Pσ M)) =
      ⟨none, (M.initialState, none, false), embStk y [] [] (fun _ => [])⟩ := by
  unfold haltList projTM
  congr 1
  funext j
  rcases j with ⟨i, hi⟩ | j
  · interval_cases i <;> simp [embStk]
  · simp [embStk]

lemma one_eval_run {f : List Bool → Bool}
    (cM : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)
    (y : List Bool) (acc : Bool) :
    ∃ s ≤ 2 * y.length + 3 + cM.time y.length,
      (flip bind (TM2.step (prog cM.tm cM.inputAlphabet.invFun cM.outputAlphabet)))^[s]
        (some ⟨some (Sum.inr 1), (cM.tm.initialState, none, acc),
          embStk [] y [] (fun _ => [])⟩) =
      some ⟨some (Sum.inr 4), (cM.tm.initialState, none, acc || f y),
        embStk [] y [] (fun _ => [])⟩ := by
  let inM := cM.inputAlphabet.invFun
  let outM := cM.outputAlphabet
  have r := cM.outputsFun y
  have pA := copyA_run cM.tm inM outM cM.tm.initialState acc y [] none
  simp only [List.append_nil] at pA
  have pB := copyB_run cM.tm inM outM cM.tm.initialState acc y.reverse [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
    Function.update_eq_self] at pB
  have hM := simulate (TM2.step cM.tm.m) (TM2.step (prog cM.tm inM outM))
    (embM y (none, acc)) (stepM inM outM y (none, acc)) r.steps _ _ r.evals_in_steps
  have he_in : embM y (none, acc) (initList cM.tm (y.map inM)) =
      ⟨some (Sum.inl cM.tm.main), (cM.tm.initialState, none, acc),
        embStk [] y [] (Function.update (fun _ => []) cM.tm.k₀ (y.map inM))⟩ := by
    unfold embM
    rw [initList_stk_eq]
    rfl
  have he_out : embM y (none, acc)
      (haltList cM.tm [cM.outputAlphabet.invFun (f y)]) =
      ⟨some (Sum.inr 3), (cM.tm.initialState, none, acc),
        embStk [] y [] (Function.update (fun _ => []) cM.tm.k₁
          [cM.outputAlphabet.invFun (f y)])⟩ := by
    unfold embM
    rw [haltList_stk_eq]
    rfl
  have hM' : (flip bind (TM2.step (prog cM.tm inM outM)))^[r.steps]
      (some ⟨some (Sum.inl cM.tm.main), (cM.tm.initialState, none, acc),
        embStk [] y [] (Function.update (fun _ => []) cM.tm.k₀ (y.map inM))⟩) =
      some ⟨some (Sum.inr 3), (cM.tm.initialState, none, acc),
        embStk [] y [] (Function.update (fun _ => []) cM.tm.k₁
          [cM.outputAlphabet.invFun (f y)])⟩ := by
    rw [← he_in, ← he_out]
    exact hM
  have p3 : (flip bind (TM2.step (prog cM.tm inM outM)))^[1]
      (some ⟨some (Sum.inr 3), (cM.tm.initialState, none, acc),
        embStk [] y [] (Function.update (fun _ => []) cM.tm.k₁
          [cM.outputAlphabet.invFun (f y)])⟩) =
      some ⟨some (Sum.inr 4), (cM.tm.initialState, none, acc || f y),
        embStk [] y [] (fun _ => [])⟩ := by
    have ho : outM (cM.outputAlphabet.invFun (f y)) = f y :=
      cM.outputAlphabet.right_inv (f y)
    simp only [Function.iterate_one, flip, bind, Option.bind_some, TM2.step, prog, TM2.stepAux,
      embStk, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
      Option.getD_some, embStk_updM, Function.update_idem, Function.update_eq_self, ho]
  refine ⟨1 + (r.steps + ((y.length + 1) + (y.length + 1))), ?_, ?_⟩
  · have hb : r.steps ≤ cM.time y.length := r.steps_le_m
    omega
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      pA, pB, hM', p3]

lemma loop_run {f : List Bool → Bool}
    (cM : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (n : ℕ) :
    ∀ (rem m : ℕ) (acc : Bool),
      m + (rem + 1) = 2 ^ n →
      ∃ s ≤ (rem + 1) * (4 * n + 5 + cM.time n) + (n + 1),
        (flip bind (TM2.step (prog cM.tm cM.inputAlphabet.invFun cM.outputAlphabet)))^[s]
          (some ⟨some (Sum.inr 1), (cM.tm.initialState, none, acc),
            embStk [] (bits n m) [] (fun _ => [])⟩) =
        some ⟨none, (cM.tm.initialState, none, false),
          embStk [evalRange f n (rem + 1) m acc] [] [] (fun _ => [])⟩ := by
  let inM := cM.inputAlphabet.invFun
  let outM := cM.outputAlphabet
  intro rem
  induction rem with
  | zero =>
      intro m acc hm
      obtain ⟨s1, hs1, hr1⟩ := one_eval_run cM (bits n m) acc
      rw [bits_length] at hs1
      have hinc : inc (bits n m) = none := inc_bits_none n m hm
      obtain ⟨tmp', hlen, h4⟩ :=
        inc_none_run cM.tm inM outM cM.tm.initialState (acc || f (bits n m))
          (bits n m) [] none hinc
      rw [bits_length] at hlen h4
      have h6 := clear_run cM.tm inM outM cM.tm.initialState (acc || f (bits n m)) tmp' none
      rw [show tmp'.length = n by simp at hlen; omega] at h6
      refine ⟨(n + 1) + ((n + 1) + s1), by omega, ?_⟩
      rw [Function.iterate_add_apply _ (n + 1) ((n + 1) + s1),
        Function.iterate_add_apply _ (n + 1) s1, hr1, h4, h6]
      rfl
  | succ rem ih =>
      intro m acc hm
      obtain ⟨s1, hs1, hr1⟩ := one_eval_run cM (bits n m) acc
      rw [bits_length] at hs1
      have hinc : inc (bits n m) = some (bits n (m + 1)) :=
        inc_bits_some n m (by omega)
      obtain ⟨s2, hs2, h45⟩ :=
        inc_some_run cM.tm inM outM cM.tm.initialState (acc || f (bits n m))
          (bits n m) (bits n (m + 1)) [] none hinc
      rw [bits_length] at hs2
      simp only [List.length_nil, List.reverse_nil, List.nil_append] at hs2 h45
      obtain ⟨s3, hs3, hrest⟩ := ih (m + 1) (acc || f (bits n m)) (by omega)
      refine ⟨s3 + (s2 + s1), ?_, ?_⟩
      · have hmul : (rem + 1 + 1) * (4 * n + 5 + cM.time n) =
            (rem + 1) * (4 * n + 5 + cM.time n) + (4 * n + 5 + cM.time n) := by ring
        omega
      · rw [Function.iterate_add_apply, Function.iterate_add_apply, hr1, h45, hrest]
        rfl

end projMachine

/-! ### Putting the machine together and bounding its runtime -/

noncomputable def projInTime (f : List Bool → Bool)
    (cM : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (lengthProjFun f) where
  tm := projTM cM.tm cM.inputAlphabet.invFun cM.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := fun n => 2 ^ n * (4 * n + 5 + cM.time n) + 2 * n + 2
  outputsFun x := by
    let inM := cM.inputAlphabet.invFun
    let outM := cM.outputAlphabet
    have p0 := init_run cM.tm inM outM cM.tm.initialState false x [] none
    simp only [List.append_nil, ← bits_zero x.length] at p0
    have hpow : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    have hex : ∃ s ≤ 2 ^ x.length * (4 * x.length + 5 + cM.time x.length) + (x.length + 1),
        (flip bind (TM2.step (prog cM.tm inM outM)))^[s]
          (some ⟨some (Sum.inr 1), (cM.tm.initialState, none, false),
            embStk [] (bits x.length 0) [] (fun _ => [])⟩) =
        some ⟨none, (cM.tm.initialState, none, false),
          embStk [lengthProjFun f x] [] [] (fun _ => [])⟩ := by
      have h := loop_run cM x.length (2 ^ x.length - 1) 0 false (by omega)
      rw [show 2 ^ x.length - 1 + 1 = 2 ^ x.length by omega] at h
      exact h
    let s := Classical.choose hex
    have hs := Classical.choose_spec hex
    have hsle := hs.1
    have hloop := hs.2
    refine ⟨⟨s + (x.length + 1), ?_⟩, ?_⟩
    · have hid : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := List.map_id x
      rw [hid]
      change (flip bind (TM2.step (prog cM.tm inM outM)))^[s + (x.length + 1)]
          (some (initList (projTM cM.tm inM outM) x : TM2.Cfg (PΓ cM.tm) (PΛ cM.tm) (Pσ cM.tm))) =
        some (haltList (projTM cM.tm inM outM) [lengthProjFun f x] :
          TM2.Cfg (PΓ cM.tm) (PΛ cM.tm) (Pσ cM.tm))
      rw [initList_eq_embStk, haltList_eq_embStk, Function.iterate_add_apply, p0]
      exact hloop
    · change s + (x.length + 1) ≤
        2 ^ x.length * (4 * x.length + 5 + cM.time x.length) + 2 * x.length + 2
      omega

lemma le_two_pow_self (a : ℕ) : a ≤ 2 ^ a := by
  induction a with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hp : 0 < 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      omega

lemma exp_poly_bound (k : ℕ) (t : ℕ → ℕ) (ht : ∀ n, t n ≤ 2 ^ (n ^ k) + k) :
    ∃ k' : ℕ, ∀ n : ℕ, 2 ^ n * (4 * n + 5 + t n) + 2 * n + 2 ≤ 2 ^ (n ^ k') + k' := by
  let g : ℕ → ℕ := fun n => 2 ^ n * (4 * n + 5 + t n) + 2 * n + 2
  have hg : ∀ n, g n ≤ 2 ^ ((k + 9) * (n + 1) ^ (k + 1)) := by
    intro n
    have htn := ht n
    have h1 : 4 * n + 5 + k ≤ 2 ^ (n + k + 4) := by
      have hn : n ≤ 2 ^ n := le_two_pow_self n
      have hk : k ≤ 2 ^ k := le_two_pow_self k
      have h1a : 1 ≤ 2 ^ (n + k) := Nat.one_le_two_pow
      have h1b : 2 ^ n ≤ 2 ^ (n + k) := Nat.pow_le_pow_right (by omega) (by omega)
      have h1c : 2 ^ k ≤ 2 ^ (n + k) := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : 2 ^ (n + k + 4) = 16 * 2 ^ (n + k) := by ring
      omega
    have h2 : 4 * n + 5 + t n ≤ 2 ^ (n ^ k + n + k + 5) := by
      have ha : 2 ^ (n + k + 4) ≤ 2 ^ (n ^ k + n + k + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hb : 2 ^ (n ^ k) ≤ 2 ^ (n ^ k + n + k + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : 2 ^ (n ^ k + n + k + 5) = 2 * 2 ^ (n ^ k + n + k + 4) := by ring
      omega
    have h3 : 2 ^ n * (4 * n + 5 + t n) ≤ 2 ^ (n ^ k + 2 * n + k + 5) := by
      calc 2 ^ n * (4 * n + 5 + t n)
          ≤ 2 ^ n * 2 ^ (n ^ k + n + k + 5) := Nat.mul_le_mul_left _ h2
        _ = 2 ^ (n + (n ^ k + n + k + 5)) := (pow_add 2 _ _).symm
        _ = 2 ^ (n ^ k + 2 * n + k + 5) := by congr 1; omega
    have h4 : 2 * n + 2 ≤ 2 ^ (n ^ k + 2 * n + k + 5) := by
      have hle : 2 * n + 2 ≤ 2 ^ (2 * n + 2) := le_two_pow_self (2 * n + 2)
      exact hle.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h5 : g n ≤ 2 ^ (n ^ k + 2 * n + k + 6) := by
      have hpow : 2 ^ (n ^ k + 2 * n + k + 6) = 2 * 2 ^ (n ^ k + 2 * n + k + 5) := by ring
      show 2 ^ n * (4 * n + 5 + t n) + 2 * n + 2 ≤ 2 ^ (n ^ k + 2 * n + k + 6)
      omega
    have h6 : n ^ k + 2 * n + k + 6 ≤ (k + 9) * (n + 1) ^ (k + 1) := by
      have hp1 : 1 ≤ (n + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have hnk : n ^ k ≤ (n + 1) ^ (k + 1) := by
        calc n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hn1 : n ≤ (n + 1) ^ (k + 1) := by
        calc n ≤ (n + 1) ^ 1 := by simp
          _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hmul : (k + 6) * 1 ≤ (k + 6) * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hp1
      have hlin : (k + 9) * (n + 1) ^ (k + 1) =
          (n + 1) ^ (k + 1) + 2 * (n + 1) ^ (k + 1) + (k + 6) * (n + 1) ^ (k + 1) := by ring
      omega
    exact h5.trans (Nat.pow_le_pow_right (by omega) h6)
  let A := k + 9
  let D := k + 1
  let k' := A + 2 * D + g 0 + g 1
  refine ⟨k', fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h01 : g n ≤ k' := by
      rcases Nat.lt_or_ge n 1 with h0 | h1
      · have hn0 : n = 0 := by omega
        subst hn0; omega
      · have hn1 : n = 1 := by omega
        subst hn1; omega
    exact h01.trans (Nat.le_add_left _ _)
  · have hA : A ≤ n ^ A := le_trans (le_two_pow_self A) (Nat.pow_le_pow_left hn A)
    have hsq : n + 1 ≤ n ^ 2 := by nlinarith
    have hD : (n + 1) ^ D ≤ n ^ (2 * D) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hsq D
    have hAD : A * (n + 1) ^ D ≤ n ^ k' := by
      calc A * (n + 1) ^ D ≤ n ^ A * n ^ (2 * D) := Nat.mul_le_mul hA hD
        _ = n ^ (A + 2 * D) := (pow_add n A (2 * D)).symm
        _ ≤ n ^ k' := Nat.pow_le_pow_right (by omega) (by omega)
    calc g n ≤ 2 ^ (A * (n + 1) ^ D) := hg n
      _ ≤ 2 ^ (n ^ k') := Nat.pow_le_pow_right (by omega) hAD
      _ ≤ 2 ^ (n ^ k') + k' := Nat.le_add_right _ _

end PvsNP.Units.tc_exp_length_proj_aux

/-- EXP is closed under length projection: if `L ∈ EXP`, then `{x | ∃ y ∈ L, y.length = x.length} ∈ EXP`. -/
theorem PvsNP.Units.tc_exp_length_proj :
∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y ∈ L, y.length = x.length) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, htime⟩
  let M' := PvsNP.Units.tc_exp_length_proj_aux.projInTime f M
  obtain ⟨k', hk'⟩ := PvsNP.Units.tc_exp_length_proj_aux.exp_poly_bound k M.time htime
  refine ⟨k', PvsNP.Units.tc_exp_length_proj_aux.lengthProjFun f, M', fun x => ?_, hk'⟩
  rw [PvsNP.Units.tc_exp_length_proj_aux.lengthProjFun_spec]
  constructor
  · rintro ⟨y, hyL, hlen⟩
    exact ⟨y, hlen, (hf y).1 hyL⟩
  · rintro ⟨y, hlen, hyf⟩
    exact ⟨y, (hf y).2 hyf, hlen⟩
