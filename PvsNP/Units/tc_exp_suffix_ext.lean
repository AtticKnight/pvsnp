import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_suffix_ext

open Turing

def succB : List Bool → List Bool
  | [] => [false]
  | false :: rest => true :: rest
  | true :: rest => false :: succB rest

def cand : ℕ → List Bool
  | 0 => []
  | j + 1 => succB (cand j)

def idx : List Bool → ℕ
  | [] => 0
  | false :: rest => 2 * idx rest + 1
  | true :: rest => 2 * idx rest + 2

lemma idx_succB (y : List Bool) : idx (succB y) = idx y + 1 := by
  induction y with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => simp [succB, idx]
    | true => simp [succB, idx, ih]; omega

lemma idx_cand (j : ℕ) : idx (cand j) = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [cand, idx_succB, ih]

lemma idx_injective {y₁ y₂ : List Bool} (h : idx y₁ = idx y₂) : y₁ = y₂ := by
  induction y₁ generalizing y₂ with
  | nil =>
    cases y₂ with
    | nil => rfl
    | cons b rest => cases b <;> simp [idx] at h
  | cons b₁ r₁ ih =>
    cases y₂ with
    | nil => cases b₁ <;> simp [idx] at h
    | cons b₂ r₂ =>
      cases b₁ <;> cases b₂ <;> simp [idx] at h
      · exact congrArg (List.cons false) (ih (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih (by omega))

lemma cand_idx (y : List Bool) : cand (idx y) = y :=
  idx_injective (idx_cand (idx y))

lemma idx_bounds (y : List Bool) :
    2 ^ y.length ≤ idx y + 1 ∧ idx y + 1 < 2 ^ (y.length + 1) := by
  induction y with
  | nil => simp [idx]
  | cons b rest ih =>
    have hpow1 : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by ring
    have hpow2 : 2 ^ (rest.length + 2) = 2 * 2 ^ (rest.length + 1) := by ring
    cases b with
    | false =>
      simp only [List.length_cons, idx]
      omega
    | true =>
      simp only [List.length_cons, idx]
      omega

lemma cand_length_le_iff (j n : ℕ) :
    (cand j).length ≤ n ↔ j + 1 < 2 ^ (n + 1) := by
  have hb := idx_bounds (cand j)
  rw [idx_cand] at hb
  constructor
  · intro hle
    have hpow : 2 ^ ((cand j).length + 1) ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · intro hlt
    by_contra hgt
    have hge : n + 1 ≤ (cand j).length := by omega
    have hpow : 2 ^ (n + 1) ≤ 2 ^ (cand j).length :=
      Nat.pow_le_pow_right (by omega) hge
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

inductive WK
  | I | XR | X | Y | YR
  deriving DecidableEq

instance : Fintype WK :=
  Fintype.ofList [WK.I, WK.XR, WK.X, WK.Y, WK.YR] (fun x => by cases x <;> simp)

inductive WL
  | initRev | loadX | restX | revY | loadY | afterM
  | succ | succBack | cmp | cmpRestX | cmpRestY | drainXR | drainY
  deriving DecidableEq

instance : Fintype WL :=
  Fintype.ofList
    [WL.initRev, WL.loadX, WL.restX, WL.revY, WL.loadY, WL.afterM,
     WL.succ, WL.succBack, WL.cmp, WL.cmpRestX, WL.cmpRestY, WL.drainXR, WL.drainY]
    (fun x => by cases x <;> simp)

section wrapperMachine

variable (M : FinTM2)

abbrev EK : Type := WK ⊕ M.K

abbrev EΓ : EK M → Type
  | Sum.inl _ => Bool
  | Sum.inr k => M.Γ k

abbrev EΛ : Type := WL ⊕ M.Λ

abbrev Eσ : Type := M.σ × Option Bool × Bool

variable {M}

def tr : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (EΓ M) (EΛ M) (Eσ M)
  | .push k f q => .push (Sum.inr k) (fun s => f s.1) (tr q)
  | .peek k f q => .peek (Sum.inr k) (fun s o => (f s.1 o, s.2)) (tr q)
  | .pop k f q => .pop (Sum.inr k) (fun s o => (f s.1 o, s.2)) (tr q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr q₁) (tr q₂)
  | .goto f => .goto (fun s => Sum.inr (f s.1))
  | .halt => .goto (fun _ => Sum.inl .afterM)

variable (M)

def prog (inF : Bool → M.Γ M.k₀) (outF : M.Γ M.k₁ → Bool) :
    EΛ M → TM2.Stmt (EΓ M) (EΛ M) (Eσ M)
  | Sum.inr l => tr (M.m l)
  | Sum.inl .initRev =>
    .pop (Sum.inl .I) (fun s o => (s.1, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .XR) (fun s => s.2.1.getD false) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .initRev))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .loadX))
  | Sum.inl .loadX =>
    .pop (Sum.inl .XR) (fun s o => (s.1, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .X) (fun s => s.2.1.getD false) <|
         .push (Sum.inr M.k₀) (fun s => inF (s.2.1.getD false)) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .loadX))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .restX))
  | Sum.inl .restX =>
    .pop (Sum.inl .X) (fun s o => (s.1, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .XR) (fun s => s.2.1.getD false) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .restX))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .revY))
  | Sum.inl .revY =>
    .pop (Sum.inl .Y) (fun s o => (s.1, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .YR) (fun s => s.2.1.getD false) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .revY))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .loadY))
  | Sum.inl .loadY =>
    .pop (Sum.inl .YR) (fun s o => (s.1, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .Y) (fun s => s.2.1.getD false) <|
         .push (Sum.inr M.k₀) (fun s => inF (s.2.1.getD false)) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .loadY))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inr M.main))
  | Sum.inl .afterM =>
    .pop (Sum.inr M.k₁) (fun _ o => (M.initialState, none, (o.map outF).getD false)) <|
      .branch (fun s => s.2.2)
        (.push (Sum.inl .I) (fun _ => true) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .drainXR))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .succ))
  | Sum.inl .succ =>
    .pop (Sum.inl .Y) (fun _ o => (M.initialState, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.branch (fun s => s.2.1.getD false)
          (.push (Sum.inl .YR) (fun _ => false) <|
           .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .succ))
          (.push (Sum.inl .Y) (fun _ => true) <|
           .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .succBack)))
        (.push (Sum.inl .Y) (fun _ => false) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .succBack))
  | Sum.inl .succBack =>
    .pop (Sum.inl .YR) (fun _ o => (M.initialState, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .Y) (fun s => s.2.1.getD false) <|
         .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .succBack))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .cmp))
  | Sum.inl .cmp =>
    .pop (Sum.inl .Y) (fun _ o => (M.initialState, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .YR) (fun s => s.2.1.getD false) <|
         .pop (Sum.inl .XR) (fun _ o => (M.initialState, o, false)) <|
         .branch (fun s => s.2.1.isSome)
           (.push (Sum.inl .X) (fun s => s.2.1.getD false) <|
            .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .cmp))
           (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .cmpRestX)))
        (.load (fun _ => (M.initialState, none, true)) <| .goto (fun _ => Sum.inl .cmpRestX))
  | Sum.inl .cmpRestX =>
    .pop (Sum.inl .X) (fun s o => (M.initialState, o, s.2.2)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .XR) (fun s => s.2.1.getD false) <|
         .load (fun s => (M.initialState, none, s.2.2)) <| .goto (fun _ => Sum.inl .cmpRestX))
        (.load (fun s => (M.initialState, none, s.2.2)) <| .goto (fun _ => Sum.inl .cmpRestY))
  | Sum.inl .cmpRestY =>
    .pop (Sum.inl .YR) (fun s o => (M.initialState, o, s.2.2)) <|
      .branch (fun s => s.2.1.isSome)
        (.push (Sum.inl .Y) (fun s => s.2.1.getD false) <|
         .load (fun s => (M.initialState, none, s.2.2)) <| .goto (fun _ => Sum.inl .cmpRestY))
        (.branch (fun s => s.2.2)
          (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .loadX))
          (.push (Sum.inl .I) (fun _ => false) <|
           .load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .drainXR)))
  | Sum.inl .drainXR =>
    .pop (Sum.inl .XR) (fun _ o => (M.initialState, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .drainXR))
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .drainY))
  | Sum.inl .drainY =>
    .pop (Sum.inl .Y) (fun _ o => (M.initialState, o, false)) <|
      .branch (fun s => s.2.1.isSome)
        (.load (fun _ => (M.initialState, none, false)) <| .goto (fun _ => Sum.inl .drainY))
        (.load (fun _ => (M.initialState, none, false)) <| .halt)

abbrev searchTM (inF : Bool → M.Γ M.k₀) (outF : M.Γ M.k₁ → Bool) : FinTM2 :=
  { K := EK M
    k₀ := Sum.inl .I
    k₁ := Sum.inl .I
    Γ := EΓ M
    Λ := EΛ M
    main := Sum.inl .initRev
    σ := Eσ M
    initialState := (M.initialState, none, false)
    kFin := @instFintypeSum _ _ inferInstance M.kFin
    ΛFin := @instFintypeSum _ _ inferInstance M.ΛFin
    σFin := @instFintypeProd _ _ M.σFin inferInstance
    m := prog M inF outF }

variable {M}

def mkStk (i xr x y yr : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : EK M, List (EΓ M k)
  | Sum.inl .I => i
  | Sum.inl .XR => xr
  | Sum.inl .X => x
  | Sum.inl .Y => y
  | Sum.inl .YR => yr
  | Sum.inr k => S k

abbrev emptyS : ∀ k : M.K, List (M.Γ k) := fun _ => []

lemma upd_I (i i' xr x y yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inl .I) i' = mkStk i' xr x y yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma upd_XR (i xr xr' x y yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inl .XR) xr' = mkStk i xr' x y yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma upd_X (i xr x x' y yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inl .X) x' = mkStk i xr x' y yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma upd_Y (i xr x y y' yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inl .Y) y' = mkStk i xr x y' yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma upd_YR (i xr x y yr yr' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inl .YR) yr' = mkStk i xr x y yr' S := by
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma upd_M (i xr x y yr : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) (xs : List (M.Γ k)) :
    Function.update (mkStk i xr x y yr S) (Sum.inr k) xs =
      mkStk i xr x y yr (Function.update S k xs) := by
  funext j
  rcases j with (_ | _ | _ | _ | _) | j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · by_cases h : j = k
    · subst h; simp [mkStk]
    · simp [mkStk, h]

def embCfg (xr y : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (EΓ M) (EΛ M) (Eσ M) :=
  ⟨some (c.l.elim (Sum.inl .afterM) Sum.inr), (c.var, none, false), mkStk [] xr [] y [] c.stk⟩

lemma sim_tr (xr y : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (tr q) ((v, none, false) : Eσ M) (mkStk [] xr [] y [] S) =
      embCfg xr y (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [tr, TM2.stepAux]
    rw [upd_M]
    exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [tr, TM2.stepAux]
    rw [upd_M]
    exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (inF : Bool → M.Γ M.k₀) (outF : M.Γ M.k₁ → Bool)

abbrev ECfg := TM2.Cfg (EΓ M) (EΛ M) (Eσ M)
abbrev estep : Option (ECfg (M := M)) → Option (ECfg (M := M)) :=
  flip bind (TM2.step (prog M inF outF))

lemma initList_search (l : List Bool) :
    initList (searchTM M inF outF) l =
      (⟨some (Sum.inl .initRev), (M.initialState, none, false),
        mkStk l [] [] [] [] emptyS⟩ : ECfg (M := M)) := by
  simp only [initList, searchTM]
  congr 1
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma haltList_search (l : List Bool) :
    haltList (searchTM M inF outF) l =
      (⟨none, (M.initialState, none, false),
        mkStk l [] [] [] [] emptyS⟩ : ECfg (M := M)) := by
  simp only [haltList, searchTM]
  congr 1
  funext k; rcases k with (_ | _ | _ | _ | _) | k <;> rfl

lemma iter_trans {a b : ℕ} {x y z : Option (ECfg (M := M))}
    (h1 : (estep inF outF)^[a] x = y) (h2 : (estep inF outF)^[b] y = z) :
    (estep inF outF)^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

lemma step_emb (xr y : List Bool) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : TM2.step M.m c = some c') :
    TM2.step (prog M inF outF) (embCfg xr y c) = some (embCfg xr y c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    change some (TM2.stepAux (tr (M.m l)) (v, none, false) (mkStk [] xr [] y [] S)) = _
    rw [sim_tr]

lemma run_embedded (xr y : List Bool) (s : List (M.Γ M.k₀)) (out : List (M.Γ M.k₁)) (t : ℕ)
    (hrun : (flip bind (TM2.step M.m))^[t] (some (initList M s)) = some (haltList M out)) :
    (estep inF outF)^[t]
      (some ⟨some (Sum.inr M.main), (M.initialState, none, false),
        mkStk [] xr [] y [] (Function.update emptyS M.k₀ s)⟩) =
      some ⟨some (Sum.inl .afterM), (M.initialState, none, false),
        mkStk [] xr [] y [] (Function.update emptyS M.k₁ out)⟩ := by
  have hsim := simulate (TM2.step M.m) (TM2.step (prog M inF outF)) (embCfg xr y)
    (step_emb inF outF xr y) t (initList M s) (haltList M out) hrun
  have h1 : embCfg xr y (initList M s) =
      ⟨some (Sum.inr M.main), (M.initialState, none, false),
        mkStk [] xr [] y [] (Function.update emptyS M.k₀ s)⟩ := by
    simp only [embCfg, initList]
    congr 1
    funext k
    rcases k with (_ | _ | _ | _ | _) | k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hk : k = M.k₀
      · subst hk; simp [mkStk]
      · simp [mkStk, hk]
  have h2 : embCfg xr y (haltList M out) =
      ⟨some (Sum.inl .afterM), (M.initialState, none, false),
        mkStk [] xr [] y [] (Function.update emptyS M.k₁ out)⟩ := by
    simp only [embCfg, haltList]
    congr 1
    funext k
    rcases k with (_ | _ | _ | _ | _) | k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hk : k = M.k₁
      · subst hk; simp [mkStk]
      · simp [mkStk, hk]
  rw [h1, h2] at hsim
  exact hsim

lemma run_initRev (i xr : List Bool) :
    (estep inF outF)^[i.length + 1]
      (some ⟨some (Sum.inl .initRev), (M.initialState, none, false),
        mkStk i xr [] [] [] emptyS⟩) =
      some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
        mkStk [] (i.reverse ++ xr) [] [] [] emptyS⟩ := by
  induction i generalizing xr with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_I]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .initRev), (M.initialState, none, false),
          mkStk (a :: rest) xr [] [] [] emptyS⟩) =
        some ⟨some (Sum.inl .initRev), (M.initialState, none, false),
          mkStk rest (a :: xr) [] [] [] emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_I, upd_XR]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: xr))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_loadX (xr x y : List Bool) (ms : List (M.Γ M.k₀)) :
    (estep inF outF)^[xr.length + 1]
      (some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
        mkStk [] xr x y [] (Function.update emptyS M.k₀ ms)⟩) =
      some ⟨some (Sum.inl .restX), (M.initialState, none, false),
        mkStk [] [] (xr.reverse ++ x) y []
          (Function.update emptyS M.k₀ (xr.reverse.map inF ++ ms))⟩ := by
  induction xr generalizing x ms with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_XR]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
          mkStk [] (a :: rest) x y [] (Function.update emptyS M.k₀ ms)⟩) =
        some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
          mkStk [] rest (a :: x) y [] (Function.update emptyS M.k₀ (inF a :: ms))⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_XR, upd_X, upd_M]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: x) (inF a :: ms))
    simpa [List.length_cons, List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_restX (xr x y : List Bool) (S : ∀ k, List (M.Γ k)) :
    (estep inF outF)^[x.length + 1]
      (some ⟨some (Sum.inl .restX), (M.initialState, none, false),
        mkStk [] xr x y [] S⟩) =
      some ⟨some (Sum.inl .revY), (M.initialState, none, false),
        mkStk [] (x.reverse ++ xr) [] y [] S⟩ := by
  induction x generalizing xr with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_X]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .restX), (M.initialState, none, false),
          mkStk [] xr (a :: rest) y [] S⟩) =
        some ⟨some (Sum.inl .restX), (M.initialState, none, false),
          mkStk [] (a :: xr) rest y [] S⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_X, upd_XR]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: xr))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_revY (xr y yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    (estep inF outF)^[y.length + 1]
      (some ⟨some (Sum.inl .revY), (M.initialState, none, false),
        mkStk [] xr [] y yr S⟩) =
      some ⟨some (Sum.inl .loadY), (M.initialState, none, false),
        mkStk [] xr [] [] (y.reverse ++ yr) S⟩ := by
  induction y generalizing yr with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .revY), (M.initialState, none, false),
          mkStk [] xr [] (a :: rest) yr S⟩) =
        some ⟨some (Sum.inl .revY), (M.initialState, none, false),
          mkStk [] xr [] rest (a :: yr) S⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y, upd_YR]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: yr))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_loadY (xr y yr : List Bool) (ms : List (M.Γ M.k₀)) :
    (estep inF outF)^[yr.length + 1]
      (some ⟨some (Sum.inl .loadY), (M.initialState, none, false),
        mkStk [] xr [] y yr (Function.update emptyS M.k₀ ms)⟩) =
      some ⟨some (Sum.inr M.main), (M.initialState, none, false),
        mkStk [] xr [] (yr.reverse ++ y) []
          (Function.update emptyS M.k₀ (yr.reverse.map inF ++ ms))⟩ := by
  induction yr generalizing y ms with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .loadY), (M.initialState, none, false),
          mkStk [] xr [] y (a :: rest) (Function.update emptyS M.k₀ ms)⟩) =
        some ⟨some (Sum.inl .loadY), (M.initialState, none, false),
          mkStk [] xr [] (a :: y) rest (Function.update emptyS M.k₀ (inF a :: ms))⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR, upd_Y, upd_M]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: y) (inF a :: ms))
    simpa [List.length_cons, List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_succBack (xr y yr : List Bool) :
    (estep inF outF)^[yr.length + 1]
      (some ⟨some (Sum.inl .succBack), (M.initialState, none, false),
        mkStk [] xr [] y yr emptyS⟩) =
      some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
        mkStk [] xr [] (yr.reverse ++ y) [] emptyS⟩ := by
  induction yr generalizing y with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .succBack), (M.initialState, none, false),
          mkStk [] xr [] y (a :: rest) emptyS⟩) =
        some ⟨some (Sum.inl .succBack), (M.initialState, none, false),
          mkStk [] xr [] (a :: y) rest emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR, upd_Y]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: y))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_succ (xr y yr : List Bool) :
    ∃ t, t ≤ 2 * y.length + yr.length + 2 ∧
      (estep inF outF)^[t]
        (some ⟨some (Sum.inl .succ), (M.initialState, none, false),
          mkStk [] xr [] y yr emptyS⟩) =
        some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
          mkStk [] xr [] (yr.reverse ++ succB y) [] emptyS⟩ := by
  induction y generalizing yr with
  | nil =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .succ), (M.initialState, none, false),
          mkStk [] xr [] [] yr emptyS⟩) =
        some ⟨some (Sum.inl .succBack), (M.initialState, none, false),
          mkStk [] xr [] [false] yr emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
    refine ⟨1 + (yr.length + 1), by simp; omega, ?_⟩
    simpa [succB] using iter_trans inF outF (a := 1) (by simpa using hs)
      (run_succBack inF outF xr [false] yr)
  | cons b rest ih =>
    cases b with
    | false =>
      have hs : estep inF outF
          (some ⟨some (Sum.inl .succ), (M.initialState, none, false),
            mkStk [] xr [] (false :: rest) yr emptyS⟩) =
          some ⟨some (Sum.inl .succBack), (M.initialState, none, false),
            mkStk [] xr [] (true :: rest) yr emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
      refine ⟨1 + (yr.length + 1), by simp; omega, ?_⟩
      simpa [succB] using iter_trans inF outF (a := 1) (by simpa using hs)
        (run_succBack inF outF xr (true :: rest) yr)
    | true =>
      have hs : estep inF outF
          (some ⟨some (Sum.inl .succ), (M.initialState, none, false),
            mkStk [] xr [] (true :: rest) yr emptyS⟩) =
          some ⟨some (Sum.inl .succ), (M.initialState, none, false),
            mkStk [] xr [] rest (false :: yr) emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y, upd_YR]
      obtain ⟨t', ht', hrec⟩ := ih (false :: yr)
      refine ⟨1 + t', by simp at ht' ⊢; omega, ?_⟩
      have hstep := iter_trans inF outF (a := 1) (by simpa using hs) hrec
      simpa [succB, List.reverse_cons, List.append_assoc] using hstep

lemma run_cmpRestX (res : Bool) (xr x y yr : List Bool) :
    (estep inF outF)^[x.length + 1]
      (some ⟨some (Sum.inl .cmpRestX), (M.initialState, none, res),
        mkStk [] xr x y yr emptyS⟩) =
      some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, res),
        mkStk [] (x.reverse ++ xr) [] y yr emptyS⟩ := by
  induction x generalizing xr with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_X]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .cmpRestX), (M.initialState, none, res),
          mkStk [] xr (a :: rest) y yr emptyS⟩) =
        some ⟨some (Sum.inl .cmpRestX), (M.initialState, none, res),
          mkStk [] (a :: xr) rest y yr emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_X, upd_XR]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: xr))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_cmpRestY_true (xr y yr : List Bool) :
    (estep inF outF)^[yr.length + 1]
      (some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, true),
        mkStk [] xr [] y yr emptyS⟩) =
      some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
        mkStk [] xr [] (yr.reverse ++ y) [] emptyS⟩ := by
  induction yr generalizing y with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, true),
          mkStk [] xr [] y (a :: rest) emptyS⟩) =
        some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, true),
          mkStk [] xr [] (a :: y) rest emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR, upd_Y]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: y))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_cmpRestY_false (xr y yr : List Bool) :
    (estep inF outF)^[yr.length + 1]
      (some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, false),
        mkStk [] xr [] y yr emptyS⟩) =
      some ⟨some (Sum.inl .drainXR), (M.initialState, none, false),
        mkStk [false] xr [] (yr.reverse ++ y) [] emptyS⟩ := by
  induction yr generalizing y with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR, upd_I]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, false),
          mkStk [] xr [] y (a :: rest) emptyS⟩) =
        some ⟨some (Sum.inl .cmpRestY), (M.initialState, none, false),
          mkStk [] xr [] (a :: y) rest emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_YR, upd_Y]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) (ih (a :: y))
    simpa [List.length_cons, List.reverse_cons, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_cmp (y : List Bool) :
    ∀ (xr xAcc yAcc : List Bool),
      (y.length ≤ xr.length →
        ∃ t, t ≤ 3 * y.length + xAcc.length + yAcc.length + 4 ∧
          (estep inF outF)^[t]
            (some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
              mkStk [] xr xAcc y yAcc emptyS⟩) =
            some ⟨some (Sum.inl .loadX), (M.initialState, none, false),
              mkStk [] (xAcc.reverse ++ xr) [] (yAcc.reverse ++ y) [] emptyS⟩) ∧
      (xr.length < y.length →
        ∃ t, t ≤ 3 * y.length + xAcc.length + yAcc.length + 4 ∧
          (estep inF outF)^[t]
            (some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
              mkStk [] xr xAcc y yAcc emptyS⟩) =
            some ⟨some (Sum.inl .drainXR), (M.initialState, none, false),
              mkStk [false] (xAcc.reverse ++ xr) [] (yAcc.reverse ++ y) [] emptyS⟩) := by
  induction y with
  | nil =>
    intro xr xAcc yAcc
    constructor
    · intro _
      have hs : estep inF outF
          (some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
            mkStk [] xr xAcc [] yAcc emptyS⟩) =
          some ⟨some (Sum.inl .cmpRestX), (M.initialState, none, true),
            mkStk [] xr xAcc [] yAcc emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
      have h1 := iter_trans inF outF (a := 1) (by simpa using hs)
        (run_cmpRestX inF outF true xr xAcc [] yAcc)
      have h2 := iter_trans inF outF h1 (run_cmpRestY_true inF outF (xAcc.reverse ++ xr) [] yAcc)
      exact ⟨1 + (xAcc.length + 1) + (yAcc.length + 1), by simp; omega, h2⟩
    · intro hlt; simp at hlt
  | cons a y' ih =>
    intro xr xAcc yAcc
    cases xr with
    | nil =>
      constructor
      · intro hle; simp at hle
      · intro _
        have hs : estep inF outF
            (some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
              mkStk [] [] xAcc (a :: y') yAcc emptyS⟩) =
            some ⟨some (Sum.inl .cmpRestX), (M.initialState, none, false),
              mkStk [] [] xAcc y' (a :: yAcc) emptyS⟩ := by
          simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y, upd_YR, upd_XR]
        have h1 := iter_trans inF outF (a := 1) (by simpa using hs)
          (run_cmpRestX inF outF false [] xAcc y' (a :: yAcc))
        have h2 := iter_trans inF outF h1
          (run_cmpRestY_false inF outF (xAcc.reverse ++ []) y' (a :: yAcc))
        refine ⟨1 + (xAcc.length + 1) + ((a :: yAcc).length + 1), by simp; omega, ?_⟩
        simpa [List.reverse_cons, List.append_assoc] using h2
    | cons b xr' =>
      have hs : estep inF outF
          (some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
            mkStk [] (b :: xr') xAcc (a :: y') yAcc emptyS⟩) =
          some ⟨some (Sum.inl .cmp), (M.initialState, none, false),
            mkStk [] xr' (b :: xAcc) y' (a :: yAcc) emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y, upd_YR, upd_XR, upd_X]
      have hrec := ih xr' (b :: xAcc) (a :: yAcc)
      constructor
      · intro hle
        obtain ⟨t', ht', hrun⟩ := hrec.1 (by simp at hle; omega)
        refine ⟨1 + t', by simp at ht' ⊢; omega, ?_⟩
        have hstep := iter_trans inF outF (a := 1) (by simpa using hs) hrun
        simpa [List.reverse_cons, List.append_assoc] using hstep
      · intro hlt
        obtain ⟨t', ht', hrun⟩ := hrec.2 (by simp at hlt; omega)
        refine ⟨1 + t', by simp at ht' ⊢; omega, ?_⟩
        have hstep := iter_trans inF outF (a := 1) (by simpa using hs) hrun
        simpa [List.reverse_cons, List.append_assoc] using hstep

lemma run_drainY (i y : List Bool) :
    (estep inF outF)^[y.length + 1]
      (some ⟨some (Sum.inl .drainY), (M.initialState, none, false),
        mkStk i [] [] y [] emptyS⟩) =
      some ⟨none, (M.initialState, none, false), mkStk i [] [] [] [] emptyS⟩ := by
  induction y with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .drainY), (M.initialState, none, false),
          mkStk i [] [] (a :: rest) [] emptyS⟩) =
        some ⟨some (Sum.inl .drainY), (M.initialState, none, false),
          mkStk i [] [] rest [] emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_Y]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) ih
    simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma run_drainXR (i xr y : List Bool) :
    (estep inF outF)^[xr.length + 1]
      (some ⟨some (Sum.inl .drainXR), (M.initialState, none, false),
        mkStk i xr [] y [] emptyS⟩) =
      some ⟨some (Sum.inl .drainY), (M.initialState, none, false),
        mkStk i [] [] y [] emptyS⟩ := by
  induction xr with
  | nil =>
    simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_XR]
  | cons a rest ih =>
    have hs : estep inF outF
        (some ⟨some (Sum.inl .drainXR), (M.initialState, none, false),
          mkStk i (a :: rest) [] y [] emptyS⟩) =
        some ⟨some (Sum.inl .drainXR), (M.initialState, none, false),
          mkStk i rest [] y [] emptyS⟩ := by
      simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_XR]
    have hstep := iter_trans inF outF (a := 1) (by simpa using hs) ih
    simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep

lemma upd_empty_self (k : M.K) (sym : M.Γ k) :
    Function.update (Function.update (emptyS (M := M)) k [sym]) k [] = emptyS := by
  funext j
  by_cases h : j = k
  · subst h; simp [emptyS]
  · simp [emptyS, h]

end wrapperMachine

lemma exp_search_bound (k : ℕ) :
    ∃ K : ℕ, ∀ n : ℕ,
      (n + 1) + 2 ^ (n + 1) * (2 ^ ((2 * n) ^ k) + k + 12 * n + 20) ≤
        2 ^ (n ^ K) + K := by
  let B : ℕ → ℕ := fun n => (n + 1) + 2 ^ (n + 1) * (2 ^ ((2 * n) ^ k) + k + 12 * n + 20)
  let E : ℕ := 2 * k + 10
  let K : ℕ := max (E + 4) (B 0 + B 1)
  refine ⟨K, fun n => ?_⟩
  rcases n with _ | _ | m
  · have h0 : B 0 ≤ K := le_trans (Nat.le_add_right _ _) (le_max_right _ _)
    exact h0.trans (Nat.le_add_left K _)
  · have h1 : B 1 ≤ K := le_trans (Nat.le_add_left _ _) (le_max_right _ _)
    exact h1.trans (Nat.le_add_left K _)
  · set N := m + 2
    have hN2 : 2 ≤ N := by omega
    have h2N : 2 * N ≤ N ^ 2 := by nlinarith
    have h2Nk : (2 * N) ^ k ≤ N ^ (2 * k) := by
      calc (2 * N) ^ k ≤ (N ^ 2) ^ k := Nat.pow_le_pow_left h2N k
        _ = N ^ (2 * k) := by rw [← pow_mul]
    have h2kE : N ^ (2 * k) ≤ N ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hterm1 : 2 ^ ((2 * N) ^ k) ≤ 2 ^ (N ^ E) :=
      Nat.pow_le_pow_right (by omega) (h2Nk.trans h2kE)
    have hterm2 : k ≤ 2 ^ (N ^ E) := by
      have hk1 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      have hk2 : 2 ^ k ≤ N ^ k := Nat.pow_le_pow_left hN2 k
      have hk3 : N ^ k ≤ N ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hk4 : N ^ E ≤ 2 ^ (N ^ E) := Nat.lt_two_pow_self.le
      exact hk1.trans (hk2.trans (hk3.trans hk4))
    have hterm3 : 12 * N + 20 ≤ 2 ^ (N ^ E) := by
      have h32 : 12 * N + 20 ≤ 32 * N := by omega
      have hpow5 : 32 ≤ N ^ 5 := by
        have : 2 ^ 5 ≤ N ^ 5 := Nat.pow_le_pow_left hN2 5
        simpa using this
      have h6 : 32 * N ≤ N ^ 6 := by
        calc 32 * N ≤ N ^ 5 * N := Nat.mul_le_mul_right N hpow5
          _ = N ^ 6 := by ring
      have h6E : N ^ 6 ≤ N ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hE2 : N ^ E ≤ 2 ^ (N ^ E) := Nat.lt_two_pow_self.le
      exact h32.trans (h6.trans (h6E.trans hE2))
    have hinner : 2 ^ ((2 * N) ^ k) + k + 12 * N + 20 ≤ 4 * 2 ^ (N ^ E) := by omega
    have hmul : 2 ^ (N + 1) * (2 ^ ((2 * N) ^ k) + k + 12 * N + 20) ≤
        2 ^ (N + 1) * (4 * 2 ^ (N ^ E)) := Nat.mul_le_mul_left _ hinner
    have hN1 : N + 1 ≤ 2 ^ (N + 1) * (4 * 2 ^ (N ^ E)) := by
      have hlt : N + 1 ≤ 2 ^ (N + 1) := Nat.lt_two_pow_self.le
      have hpos : 1 ≤ 4 * 2 ^ (N ^ E) := by
        have : 1 ≤ 2 ^ (N ^ E) := Nat.one_le_two_pow
        omega
      calc N + 1 ≤ 2 ^ (N + 1) := hlt
        _ = 2 ^ (N + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ (N + 1) * (4 * 2 ^ (N ^ E)) := Nat.mul_le_mul_left _ hpos
    have hcomb : (N + 1) + 2 ^ (N + 1) * (2 ^ ((2 * N) ^ k) + k + 12 * N + 20) ≤
        2 ^ (N ^ E + N + 4) := by
      have heq : 2 * (2 ^ (N + 1) * (4 * 2 ^ (N ^ E))) = 2 ^ (N ^ E + N + 4) := by
        have hadd : N ^ E + N + 4 = N ^ E + (N + 1) + 3 := by omega
        rw [hadd, pow_add, pow_add]
        ring
      omega
    have hexp : N ^ E + N + 4 ≤ N ^ (E + 4) := by
      have hN4 : 16 ≤ N ^ 4 := by
        have : 2 ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hN2 4
        simpa using this
      have hNE : N ≤ N ^ E := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 1 ≤ N ^ E := Nat.one_le_pow _ _ (by omega)
      have hmul4 : 16 * N ^ E ≤ N ^ 4 * N ^ E := Nat.mul_le_mul_right _ hN4
      have hpow4 : N ^ 4 * N ^ E = N ^ (E + 4) := by rw [Nat.mul_comm, ← pow_add]
      omega
    have hEK : N ^ (E + 4) ≤ N ^ K :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hfinal : 2 ^ (N ^ E + N + 4) ≤ 2 ^ (N ^ K) :=
      Nat.pow_le_pow_right (by omega) (hexp.trans hEK)
    exact (hcomb.trans hfinal).trans (Nat.le_add_right _ K)

lemma run_search_loop (f : List Bool → Bool)
    (M : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (k : ℕ)
    (hM : ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) (x : List Bool) :
    ∀ (r' j : ℕ), j + (r' + 1) = 2 ^ (x.length + 1) - 1 →
      ∃ t, t ≤ (r' + 1) * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) ∧
        (estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet)^[t]
          (some ⟨some (Sum.inl .loadX), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) [] emptyS⟩) =
          some ⟨none, (M.tm.initialState, none, false),
            mkStk [decide (∃ i < r' + 1, f (cand (j + i) ++ x) = true)] [] [] [] [] emptyS⟩ := by
  intro r'
  induction r' with
  | zero =>
    intro j hj
    have hlen_y : (cand j).length ≤ x.length := by
      rw [cand_length_le_iff]
      have hpos : 1 ≤ 2 ^ (x.length + 1) := Nat.one_le_two_pow
      omega
    have hrun_one := M.outputsFun (cand j ++ x)
    have hloadX := run_loadX (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      x.reverse [] (cand j) []
    have hupd0 : Function.update (emptyS (M := M.tm)) M.tm.k₀ [] = emptyS := by
      funext s; by_cases h : s = M.tm.k₀ <;> simp [emptyS, h]
    rw [hupd0] at hloadX
    have hrestX := run_restX (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      [] (x.reverse.reverse ++ []) (cand j)
      (Function.update emptyS M.tm.k₀ (x.reverse.reverse.map M.inputAlphabet.invFun ++ []))
    have hrevY := run_revY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      ((x.reverse.reverse ++ []).reverse ++ []) (cand j) []
      (Function.update emptyS M.tm.k₀ (x.reverse.reverse.map M.inputAlphabet.invFun ++ []))
    have hloadY := run_loadY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      ((x.reverse.reverse ++ []).reverse ++ []) [] ((cand j).reverse ++ [])
      (x.reverse.reverse.map M.inputAlphabet.invFun ++ [])
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hloadX hrestX hrevY hloadY
    have hprep := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet hloadX hrestX) hrevY) hloadY
    have hmap : (cand j).map M.inputAlphabet.invFun ++ x.map M.inputAlphabet.invFun =
        (cand j ++ x).map M.inputAlphabet.invFun := (List.map_append ..).symm
    rw [hmap] at hprep
    have hemb := run_embedded (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      x.reverse (cand j) ((cand j ++ x).map M.inputAlphabet.invFun)
      [M.outputAlphabet.invFun (f (cand j ++ x))] hrun_one.steps hrun_one.evals_in_steps
    have htoAfter := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet hprep hemb
    have htM : hrun_one.steps ≤ 2 ^ ((2 * x.length) ^ k) + k := by
      have h1 := hrun_one.steps_le_m
      have h2 := hM ((cand j ++ x).length)
      have h3 : (cand j ++ x).length ≤ 2 * x.length := by simp; omega
      have h4 : (cand j ++ x).length ^ k ≤ (2 * x.length) ^ k := Nat.pow_le_pow_left h3 k
      have h5 : 2 ^ ((cand j ++ x).length ^ k) ≤ 2 ^ ((2 * x.length) ^ k) :=
        Nat.pow_le_pow_right (by omega) h4
      change hrun_one.steps ≤ M.time (cand j ++ x).length at h1
      omega
    cases hf : f (cand j ++ x) with
    | true =>
      have hafter : estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (some ⟨some (Sum.inl .afterM), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) []
              (Function.update emptyS M.tm.k₁ [M.outputAlphabet.invFun (f (cand j ++ x))])⟩) =
          some ⟨some (Sum.inl .drainXR), (M.tm.initialState, none, false),
            mkStk [true] x.reverse [] (cand j) [] emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_M, upd_I, hf]
      have hd1 := run_drainXR (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        [true] x.reverse (cand j)
      have hd2 := run_drainY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet [true] (cand j)
      have hall := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet htoAfter
            (b := 1) (by simpa using hafter)) hd1) hd2
      have hdec : decide (∃ i < 0 + 1, f (cand (j + i) ++ x) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨0, by omega, by simpa using hf⟩
      rw [hdec]
      refine ⟨(x.length + 1) + (x.length + 1) + ((cand j).length + 1) + ((cand j).length + 1) +
        hrun_one.steps + 1 + (x.reverse.length + 1) + ((cand j).length + 1), ?_, hall⟩
      simp only [List.length_reverse]
      omega
    | false =>
      have hafter : estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (some ⟨some (Sum.inl .afterM), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) []
              (Function.update emptyS M.tm.k₁ [M.outputAlphabet.invFun (f (cand j ++ x))])⟩) =
          some ⟨some (Sum.inl .succ), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) [] emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_M, hf]
      obtain ⟨ts, hts, hsucc⟩ := run_succ (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        x.reverse (cand j) []
      simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at hts hsucc
      have hnext_gt : x.reverse.length < (succB (cand j)).length := by
        rw [List.length_reverse]
        change x.length < (cand (j + 1)).length
        by_contra hle
        have hle' : (cand (j + 1)).length ≤ x.length := by omega
        rw [cand_length_le_iff] at hle'
        omega
      have hsucc_len : (succB (cand j)).length ≤ x.length + 1 := by
        have hsle : ∀ l : List Bool, (succB l).length ≤ l.length + 1 := by
          intro l; induction l with
          | nil => simp [succB]
          | cons b r ih => cases b <;> simp [succB] <;> omega
        have := hsle (cand j)
        omega
      obtain ⟨tc, htc, hcmp⟩ :=
        (run_cmp (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (succB (cand j)) x.reverse [] []).2 hnext_gt
      simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at htc hcmp
      have hd1 := run_drainXR (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        [false] x.reverse (succB (cand j))
      have hd2 := run_drainY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        [false] (succB (cand j))
      have hall := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
            (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
              (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet htoAfter
                (b := 1) (by simpa using hafter)) hsucc) hcmp) hd1) hd2
      have hdec : decide (∃ i < 0 + 1, f (cand (j + i) ++ x) = true) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨i, hi, hfi⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp [hf] at hfi
      rw [hdec]
      refine ⟨(x.length + 1) + (x.length + 1) + ((cand j).length + 1) + ((cand j).length + 1) +
        hrun_one.steps + 1 + ts + tc + (x.reverse.length + 1) + ((succB (cand j)).length + 1),
        ?_, hall⟩
      simp only [List.length_reverse]
      omega
  | succ r' ih =>
    intro j hj
    have hlen_y : (cand j).length ≤ x.length := by
      rw [cand_length_le_iff]
      have hpos : 1 ≤ 2 ^ (x.length + 1) := Nat.one_le_two_pow
      omega
    have hrun_one := M.outputsFun (cand j ++ x)
    have hloadX := run_loadX (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      x.reverse [] (cand j) []
    have hupd0 : Function.update (emptyS (M := M.tm)) M.tm.k₀ [] = emptyS := by
      funext s; by_cases h : s = M.tm.k₀ <;> simp [emptyS, h]
    rw [hupd0] at hloadX
    have hrestX := run_restX (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      [] (x.reverse.reverse ++ []) (cand j)
      (Function.update emptyS M.tm.k₀ (x.reverse.reverse.map M.inputAlphabet.invFun ++ []))
    have hrevY := run_revY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      ((x.reverse.reverse ++ []).reverse ++ []) (cand j) []
      (Function.update emptyS M.tm.k₀ (x.reverse.reverse.map M.inputAlphabet.invFun ++ []))
    have hloadY := run_loadY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      ((x.reverse.reverse ++ []).reverse ++ []) [] ((cand j).reverse ++ [])
      (x.reverse.reverse.map M.inputAlphabet.invFun ++ [])
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hloadX hrestX hrevY hloadY
    have hprep := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet hloadX hrestX) hrevY) hloadY
    have hmap : (cand j).map M.inputAlphabet.invFun ++ x.map M.inputAlphabet.invFun =
        (cand j ++ x).map M.inputAlphabet.invFun := (List.map_append ..).symm
    rw [hmap] at hprep
    have hemb := run_embedded (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
      x.reverse (cand j) ((cand j ++ x).map M.inputAlphabet.invFun)
      [M.outputAlphabet.invFun (f (cand j ++ x))] hrun_one.steps hrun_one.evals_in_steps
    have htoAfter := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet hprep hemb
    have htM : hrun_one.steps ≤ 2 ^ ((2 * x.length) ^ k) + k := by
      have h1 := hrun_one.steps_le_m
      have h2 := hM ((cand j ++ x).length)
      have h3 : (cand j ++ x).length ≤ 2 * x.length := by simp; omega
      have h4 : (cand j ++ x).length ^ k ≤ (2 * x.length) ^ k := Nat.pow_le_pow_left h3 k
      have h5 : 2 ^ ((cand j ++ x).length ^ k) ≤ 2 ^ ((2 * x.length) ^ k) :=
        Nat.pow_le_pow_right (by omega) h4
      change hrun_one.steps ≤ M.time (cand j ++ x).length at h1
      omega
    cases hf : f (cand j ++ x) with
    | true =>
      have hafter : estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (some ⟨some (Sum.inl .afterM), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) []
              (Function.update emptyS M.tm.k₁ [M.outputAlphabet.invFun (f (cand j ++ x))])⟩) =
          some ⟨some (Sum.inl .drainXR), (M.tm.initialState, none, false),
            mkStk [true] x.reverse [] (cand j) [] emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_M, upd_I, hf]
      have hd1 := run_drainXR (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        [true] x.reverse (cand j)
      have hd2 := run_drainY (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet [true] (cand j)
      have hall := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet htoAfter
            (b := 1) (by simpa using hafter)) hd1) hd2
      have hdec : decide (∃ i < r' + 1 + 1, f (cand (j + i) ++ x) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨0, by omega, by simpa using hf⟩
      rw [hdec]
      refine ⟨(x.length + 1) + (x.length + 1) + ((cand j).length + 1) + ((cand j).length + 1) +
        hrun_one.steps + 1 + (x.reverse.length + 1) + ((cand j).length + 1), ?_, hall⟩
      simp only [List.length_reverse]
      have hmul : 2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20 ≤
          (r' + 1 + 1) * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    | false =>
      have hafter : estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (some ⟨some (Sum.inl .afterM), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) []
              (Function.update emptyS M.tm.k₁ [M.outputAlphabet.invFun (f (cand j ++ x))])⟩) =
          some ⟨some (Sum.inl .succ), (M.tm.initialState, none, false),
            mkStk [] x.reverse [] (cand j) [] emptyS⟩ := by
        simp [estep, flip, TM2.step, prog, TM2.stepAux, mkStk, upd_M, hf]
      obtain ⟨ts, hts, hsucc⟩ := run_succ (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        x.reverse (cand j) []
      simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at hts hsucc
      have hnext_le : (succB (cand j)).length ≤ x.reverse.length := by
        rw [List.length_reverse]
        change (cand (j + 1)).length ≤ x.length
        rw [cand_length_le_iff]
        have hpos : 1 ≤ 2 ^ (x.length + 1) := Nat.one_le_two_pow
        omega
      obtain ⟨tc, htc, hcmp⟩ :=
        (run_cmp (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (succB (cand j)) x.reverse [] []).1 hnext_le
      simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at htc hcmp
      obtain ⟨trec, htrec, hrec⟩ := ih (j + 1) (by omega)
      have hall := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
        (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
          (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet
            (iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet htoAfter
              (b := 1) (by simpa using hafter)) hsucc) hcmp) hrec
      have hdec : decide (∃ i < r' + 1 + 1, f (cand (j + i) ++ x) = true) =
          decide (∃ i < r' + 1, f (cand (j + 1 + i) ++ x) = true) := by
        rw [decide_eq_decide]
        constructor
        · rintro ⟨i, hi, hfi⟩
          cases i with
          | zero => simp [hf] at hfi
          | succ i' =>
            refine ⟨i', by omega, ?_⟩
            have heq : j + 1 + i' = j + (i' + 1) := by omega
            rwa [heq]
        · rintro ⟨i, hi, hfi⟩
          refine ⟨i + 1, by omega, ?_⟩
          have heq : j + (i + 1) = j + 1 + i := by omega
          rwa [heq]
      rw [hdec]
      refine ⟨(x.length + 1) + (x.length + 1) + ((cand j).length + 1) + ((cand j).length + 1) +
        hrun_one.steps + 1 + ts + tc + trec, ?_, hall⟩
      simp only [List.length_reverse] at hnext_le
      have hmul : (r' + 1 + 1) * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) =
          (r' + 1) * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) +
          (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) := by ring
      omega

def searchDecider (f : List Bool → Bool) (x : List Bool) : Bool :=
  decide (∃ j < 2 ^ (x.length + 1) - 1, f (cand j ++ x) = true)

theorem main_proof :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y : List Bool, y.length ≤ x.length ∧ y ++ x ∈ L) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, hM⟩
  obtain ⟨K, hK⟩ := exp_search_bound k
  have hrun_all : ∀ x : List Bool,
      ∃ t, t ≤ 2 ^ (x.length ^ K) + K ∧
        (estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet)^[t]
          (some (initList (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet) x)) =
          some (haltList (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet)
            [searchDecider f x]) := by
    intro x
    have hpos : 1 ≤ 2 ^ (x.length + 1) - 1 := by
      have : 2 ≤ 2 ^ (x.length + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (x.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    set R := 2 ^ (x.length + 1) - 1
    have hinitRev := run_initRev (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet x []
    simp only [List.append_nil] at hinitRev
    obtain ⟨tl, htl, hloop⟩ := run_search_loop f M k hM x (R - 1) 0 (by omega)
    have hR : R - 1 + 1 = R := by omega
    rw [hR] at htl hloop
    have hcomb := iter_trans (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet hinitRev hloop
    have hdec : decide (∃ i < R, f (cand (0 + i) ++ x) = true) = searchDecider f x := by
      simp [searchDecider, R]
    rw [hdec] at hcomb
    have hRle : R ≤ 2 ^ (x.length + 1) := Nat.sub_le _ _
    have hmul : R * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) ≤
        2 ^ (x.length + 1) * (2 ^ ((2 * x.length) ^ k) + k + 12 * x.length + 20) :=
      Nat.mul_le_mul_right _ hRle
    have hbound := hK x.length
    refine ⟨(x.length + 1) + tl, by omega, ?_⟩
    exact (congrArg (fun c =>
      (estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet)^[(x.length + 1) + tl] (some c))
      (initList_search M.inputAlphabet.invFun M.outputAlphabet x)).trans
      (hcomb.trans (congrArg some
        (haltList_search M.inputAlphabet.invFun M.outputAlphabet [searchDecider f x]).symm))
  let M' : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer (searchDecider f) :=
    { tm := searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := fun n => 2 ^ (n ^ K) + K
      outputsFun := fun x =>
        let h := hrun_all x
        { steps := Classical.choose h
          evals_in_steps := by
            have hm : ∀ l : List Bool,
                @List.map Bool ((searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet).Γ
                  (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet).k₀)
                  (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
            have hm1 : ∀ l : List Bool,
                @List.map Bool ((searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet).Γ
                  (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet).k₁)
                  (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
            have hspec := (Classical.choose_spec h).2
            exact (congrArg (fun l =>
              (estep (M := M.tm) M.inputAlphabet.invFun M.outputAlphabet)^[Classical.choose h]
                (some (initList (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet) l)))
              (hm x)).trans (hspec.trans (congrArg (fun l =>
                some (haltList (searchTM M.tm M.inputAlphabet.invFun M.outputAlphabet) l))
                (hm1 [searchDecider f x]).symm))
          steps_le_m := (Classical.choose_spec h).1 } }
  refine ⟨K, searchDecider f, M', ?_, fun n => le_rfl⟩
  intro x
  simp only [searchDecider, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hylen, hyx⟩
    refine ⟨idx y, ?_, ?_⟩
    · have hb := idx_bounds y
      have hpow : 2 ^ (y.length + 1) ≤ 2 ^ (x.length + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · rw [cand_idx]
      exact (hf (y ++ x)).mp hyx
  · rintro ⟨j, hj, hfj⟩
    refine ⟨cand j, ?_, (hf (cand j ++ x)).mpr hfj⟩
    rw [cand_length_le_iff]
    have hpos : 1 ≤ 2 ^ (x.length + 1) := Nat.one_le_two_pow
    omega

end PvsNP.Units.tc_exp_suffix_ext

theorem PvsNP.Units.tc_exp_suffix_ext :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y : List Bool, y.length ≤ x.length ∧ y ++ x ∈ L) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_suffix_ext.main_proof
