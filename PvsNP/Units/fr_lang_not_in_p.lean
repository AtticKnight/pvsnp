import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.fr_lang_not_in_p_aux

open Turing

/-- Symbols explicitly pushed onto stack `k` inside a `TM2.Stmt` syntax tree. -/
def pushedOn {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) : TM2.Stmt Γ Λ σ → Set (Γ k)
  | .push k' f q =>
      (if h : k' = k then Set.range (fun s => h ▸ f s) else ∅) ∪ pushedOn k q
  | .peek _ _ q => pushedOn k q
  | .pop _ _ q => pushedOn k q
  | .load _ q => pushedOn k q
  | .branch _ q₁ q₂ => pushedOn k q₁ ∪ pushedOn k q₂
  | .goto _ => ∅
  | .halt => ∅

lemma pushedOn_finite {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Finite σ]
    (k : K) (q : TM2.Stmt Γ Λ σ) : (pushedOn k q).Finite := by
  induction q with
  | push k' f q ih =>
      simp only [pushedOn]
      apply Set.Finite.union _ ih
      split_ifs
      · exact Set.finite_range _
      · exact Set.finite_empty
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- Reachable symbols on stack `k` for a machine with Bool input and output alphabets. -/
def GoodSym (M : TM2ComputableAux Bool Bool) (k : M.tm.K) : Set (M.tm.Γ k) :=
  (if k = M.tm.k₀ then Set.univ else ∅) ∪
  (if k = M.tm.k₁ then Set.univ else ∅) ∪
  ⋃ l : M.tm.Λ, pushedOn k (M.tm.m l)

lemma goodSym_finite (M : TM2ComputableAux Bool Bool) (k : M.tm.K) : (GoodSym M k).Finite := by
  unfold GoodSym
  have : Finite M.tm.Λ := M.tm.ΛFin.finite
  have : Finite M.tm.σ := M.tm.σFin.finite
  apply Set.Finite.union
  · apply Set.Finite.union
    · split_ifs with h
      · subst h
        have : Finite (M.tm.Γ M.tm.k₀) := M.tm.Γk₀Fin.finite
        exact Set.finite_univ
      · exact Set.finite_empty
    · split_ifs with h
      · subst h
        have : Finite (M.tm.Γ M.tm.k₁) := Finite.of_equiv Bool M.outputAlphabet.symm
        exact Set.finite_univ
      · exact Set.finite_empty
  · exact Set.finite_iUnion (fun l => pushedOn_finite k (M.tm.m l))

/-- Canonical finite-indexed TM2 representation over `Fin` types. -/
structure CanonTM2 where
  nK : ℕ
  k₀ : Fin nK
  k₁ : Fin nK
  nΓ : Fin nK → ℕ
  nΛ : ℕ
  main : Fin nΛ
  nσ : ℕ
  init : Fin nσ
  prog : Fin nΛ → TM2.Stmt (fun k => Fin (nΓ k)) (Fin nΛ) (Fin nσ)
  inMap : Bool → Fin (nΓ k₀)
  outMap : Bool → Fin (nΓ k₁)

abbrev CanonTM2.toFinTM2 (c : CanonTM2) : FinTM2 where
  K := Fin c.nK
  k₀ := c.k₀
  k₁ := c.k₁
  Γ k := Fin (c.nΓ k)
  Λ := Fin c.nΛ
  main := c.main
  σ := Fin c.nσ
  initialState := c.init
  m := c.prog

/-- Countability of `TM2.Stmt` when all index, alphabet, label, and state types are finite. -/
def stmtDepth {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtDepth q + 1
  | .peek _ _ q => stmtDepth q + 1
  | .pop _ _ q => stmtDepth q + 1
  | .load _ q => stmtDepth q + 1
  | .branch _ q₁ q₂ => max (stmtDepth q₁) (stmtDepth q₂) + 1
  | .goto _ => 0
  | .halt => 0

abbrev stmtOfDepthLe {K : Type} {Γ : K → Type} {Λ σ : Type} (d : ℕ) : Type :=
  { q : TM2.Stmt Γ Λ σ // stmtDepth q ≤ d }

lemma stmtOfDepthLe_countable {K : Type} [Countable K] {Γ : K → Type} [∀ k, Finite (Γ k)]
    {Λ σ : Type} [Finite σ] [Countable Λ] :
    ∀ d, Countable (stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d)
  | 0 => by
      let f : stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) 0 → Option (σ → Λ) := fun ⟨q, hq⟩ =>
        match q with
        | .goto g => some g
        | .halt => none
        | .push _ _ _ => by simp [stmtDepth] at hq
        | .peek _ _ _ => by simp [stmtDepth] at hq
        | .pop _ _ _ => by simp [stmtDepth] at hq
        | .load _ _ => by simp [stmtDepth] at hq
        | .branch _ _ _ => by simp [stmtDepth] at hq
      refine Function.Injective.countable (f := f) ?_
      rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ heq
      cases q₁ <;> cases q₂ <;> simp [stmtDepth] at h₁ h₂
      · simp [f] at heq; subst heq; rfl
      · simp [f] at heq
      · simp [f] at heq
      · rfl
  | d + 1 => by
      have : Countable (stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) :=
        stmtOfDepthLe_countable d
      let T :=
        (Σ k : K, (σ → Γ k) × stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) ⊕
        (Σ k : K, (σ → Option (Γ k) → σ) × stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) ⊕
        (Σ k : K, (σ → Option (Γ k) → σ) × stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) ⊕
        ((σ → σ) × stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) ⊕
        ((σ → Bool) × stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d ×
          stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) ⊕
        (σ → Λ) ⊕
        Unit
      have : Countable T := by dsimp only [T]; infer_instance
      let enc : stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) (d + 1) → T := fun ⟨q, hq⟩ =>
        match q with
        | .push k g q' => Sum.inl ⟨k, g, ⟨q', by simp [stmtDepth] at hq; omega⟩⟩
        | .peek k g q' => Sum.inr (Sum.inl ⟨k, g, ⟨q', by simp [stmtDepth] at hq; omega⟩⟩)
        | .pop k g q' => Sum.inr (Sum.inr (Sum.inl ⟨k, g, ⟨q', by simp [stmtDepth] at hq; omega⟩⟩))
        | .load g q' => Sum.inr (Sum.inr (Sum.inr (Sum.inl (g, ⟨q', by simp [stmtDepth] at hq; omega⟩))))
        | .branch g q₁ q₂ =>
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (g,
              ⟨q₁, by simp [stmtDepth] at hq; omega⟩,
              ⟨q₂, by simp [stmtDepth] at hq; omega⟩)))))
        | .goto g => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g)))))
        | .halt => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
      refine Function.Injective.countable (f := enc) ?_
      rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ heq
      cases q₁ with
      | push k₁ g₁ r₁ =>
          cases q₂ with
          | push k₂ g₂ r₂ =>
              have h0 := Sum.inl.inj heq
              rcases Sigma.mk.inj_iff.mp h0 with ⟨rfl, h⟩
              rcases Prod.mk.inj (eq_of_heq h) with ⟨rfl, hq⟩
              cases Subtype.mk.inj hq; rfl
          | _ => cases heq
      | peek k₁ g₁ r₁ =>
          cases q₂ with
          | peek k₂ g₂ r₂ =>
              have h0 := Sum.inl.inj (Sum.inr.inj heq)
              rcases Sigma.mk.inj_iff.mp h0 with ⟨rfl, h⟩
              rcases Prod.mk.inj (eq_of_heq h) with ⟨rfl, hq⟩
              cases Subtype.mk.inj hq; rfl
          | push _ _ _ => cases heq
          | _ => have h' := Sum.inr.inj heq; cases h'
      | pop k₁ g₁ r₁ =>
          cases q₂ with
          | pop k₂ g₂ r₂ =>
              have h0 := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj heq))
              rcases Sigma.mk.inj_iff.mp h0 with ⟨rfl, h⟩
              rcases Prod.mk.inj (eq_of_heq h) with ⟨rfl, hq⟩
              cases Subtype.mk.inj hq; rfl
          | push _ _ _ => cases heq
          | peek _ _ _ => have h' := Sum.inr.inj heq; cases h'
          | _ => have h' := Sum.inr.inj (Sum.inr.inj heq); cases h'
      | load g₁ r₁ =>
          cases q₂ with
          | load g₂ r₂ =>
              have h0 := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)))
              rcases Prod.mk.inj h0 with ⟨rfl, hq⟩
              cases Subtype.mk.inj hq; rfl
          | push _ _ _ => cases heq
          | peek _ _ _ => have h' := Sum.inr.inj heq; cases h'
          | pop _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj heq); cases h'
          | _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)); cases h'
      | branch g₁ a₁ b₁ =>
          cases q₂ with
          | branch g₂ a₂ b₂ =>
              have h0 := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq))))
              rcases Prod.mk.inj h0 with ⟨rfl, hq12⟩
              rcases Prod.mk.inj hq12 with ⟨hq1, hq2⟩
              cases Subtype.mk.inj hq1; cases Subtype.mk.inj hq2; rfl
          | push _ _ _ => cases heq
          | peek _ _ _ => have h' := Sum.inr.inj heq; cases h'
          | pop _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj heq); cases h'
          | load _ _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)); cases h'
          | _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq))); cases h'
      | goto g₁ =>
          cases q₂ with
          | goto g₂ =>
              have h0 := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)))))
              subst h0; rfl
          | push _ _ _ => cases heq
          | peek _ _ _ => have h' := Sum.inr.inj heq; cases h'
          | pop _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj heq); cases h'
          | load _ _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)); cases h'
          | branch _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq))); cases h'
          | halt => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)))); cases h'
      | halt =>
          cases q₂ with
          | halt => rfl
          | push _ _ _ => cases heq
          | peek _ _ _ => have h' := Sum.inr.inj heq; cases h'
          | pop _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj heq); cases h'
          | load _ _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)); cases h'
          | branch _ _ _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq))); cases h'
          | goto _ => have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj heq)))); cases h'

instance stmt_countable {K : Type} [Countable K] {Γ : K → Type} [∀ k, Finite (Γ k)]
    {Λ σ : Type} [Finite σ] [Countable Λ] : Countable (TM2.Stmt Γ Λ σ) := by
  haveI : ∀ d, Countable (stmtOfDepthLe (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) d) :=
    stmtOfDepthLe_countable
  refine Function.Injective.countable
    (f := fun q : TM2.Stmt Γ Λ σ => (⟨stmtDepth q, ⟨q, le_rfl⟩⟩ : Σ d, stmtOfDepthLe d)) ?_
  intro q₁ q₂ h
  have := congrArg (fun x => x.2.1) h
  exact this

instance canonTM2_countable : Countable CanonTM2 := by
  let Hdr :=
    (Σ nK : ℕ, Fin nK × Fin nK × (Fin nK → ℕ)) ×
    (Σ nΛ : ℕ, Fin nΛ) ×
    (Σ nσ : ℕ, Fin nσ)
  haveI : Countable Hdr := by dsimp only [Hdr]; infer_instance
  let Body (h : Hdr) : Type :=
    (Fin h.2.1.1 → TM2.Stmt (fun k => Fin (h.1.2.2.2 k)) (Fin h.2.1.1) (Fin h.2.2.1)) ×
    (Bool → Fin (h.1.2.2.2 h.1.2.1)) ×
    (Bool → Fin (h.1.2.2.2 h.1.2.2.1))
  haveI : ∀ h : Hdr, Countable (Body h) := fun h => by
    dsimp only [Body]
    haveI : Countable (TM2.Stmt (fun k => Fin (h.1.2.2.2 k)) (Fin h.2.1.1) (Fin h.2.2.1)) :=
      stmt_countable
    infer_instance
  let enc : CanonTM2 → Σ h : Hdr, Body h := fun c =>
    ⟨(⟨c.nK, c.k₀, c.k₁, c.nΓ⟩, ⟨c.nΛ, c.main⟩, ⟨c.nσ, c.init⟩), (c.prog, c.inMap, c.outMap)⟩
  refine Function.Injective.countable (f := enc) ?_
  rintro ⟨nK₁, k₀₁, k₁₁, nΓ₁, nΛ₁, main₁, nσ₁, init₁, prog₁, in₁, out₁⟩
         ⟨nK₂, k₀₂, k₁₂, nΓ₂, nΛ₂, main₂, nσ₂, init₂, prog₂, in₂, out₂⟩ h
  rcases Sigma.mk.inj_iff.mp h with ⟨hhdr, hbody⟩
  rcases Prod.mk.inj hhdr with ⟨h1, h23⟩
  rcases Prod.mk.inj h23 with ⟨h2, h3⟩
  rcases Sigma.mk.inj_iff.mp h1 with ⟨rfl, h1'⟩
  rcases Prod.mk.inj (eq_of_heq h1') with ⟨rfl, h1''⟩
  rcases Prod.mk.inj h1'' with ⟨rfl, rfl⟩
  rcases Sigma.mk.inj_iff.mp h2 with ⟨rfl, h2'⟩
  cases eq_of_heq h2'
  rcases Sigma.mk.inj_iff.mp h3 with ⟨rfl, h3'⟩
  cases eq_of_heq h3'
  rcases Prod.mk.inj (eq_of_heq hbody) with ⟨rfl, hio⟩
  rcases Prod.mk.inj hio with ⟨rfl, rfl⟩
  rfl

/-- Map a statement along equivalences on `K`, `Λ`, `σ` and partial encodings on `Γ`. -/
def mapStmt
    {K K' : Type} [DecidableEq K] [DecidableEq K']
    {Γ : K → Type} {Γ' : K' → Type} {Λ Λ' σ σ' : Type}
    (eK : K ≃ K') (eΛ : Λ ≃ Λ') (eσ : σ ≃ σ')
    (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (fromΓ' : ∀ k, Γ' (eK k) → Option (Γ k)) :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ'
  | .push k f q =>
      .push (eK k) (fun s' => toΓ' k (f (eσ.symm s'))) (mapStmt eK eΛ eσ toΓ' fromΓ' q)
  | .peek k f q =>
      .peek (eK k) (fun s' o => eσ (f (eσ.symm s') (o.bind (fromΓ' k))))
        (mapStmt eK eΛ eσ toΓ' fromΓ' q)
  | .pop k f q =>
      .pop (eK k) (fun s' o => eσ (f (eσ.symm s') (o.bind (fromΓ' k))))
        (mapStmt eK eΛ eσ toΓ' fromΓ' q)
  | .load f q =>
      .load (fun s' => eσ (f (eσ.symm s'))) (mapStmt eK eΛ eσ toΓ' fromΓ' q)
  | .branch f q₁ q₂ =>
      .branch (fun s' => f (eσ.symm s'))
        (mapStmt eK eΛ eσ toΓ' fromΓ' q₁) (mapStmt eK eΛ eσ toΓ' fromΓ' q₂)
  | .goto f =>
      .goto (fun s' => eΛ (f (eσ.symm s')))
  | .halt => .halt

/-- Transport a configuration along the equivalences. -/
def mapCfg
    {K K' : Type} {Γ : K → Type} {Γ' : K' → Type} {Λ Λ' σ σ' : Type}
    (eK : K ≃ K') (eΛ : Λ ≃ Λ') (eσ : σ ≃ σ')
    (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ' Λ' σ' where
  l := c.l.map eΛ
  var := eσ c.var
  stk k' := by
    have h : eK (eK.symm k') = k' := eK.apply_symm_apply k'
    exact h ▸ (c.stk (eK.symm k')).map (toΓ' (eK.symm k'))

lemma cast_stk_eq
    {K K' : Type} {Γ : K → Type} {Γ' : K' → Type}
    (eK : K ≃ K') (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (S : ∀ k, List (Γ k)) (k : K) :
    (eK.apply_symm_apply (eK k) ▸ (S (eK.symm (eK k))).map (toΓ' (eK.symm (eK k))) : List (Γ' (eK k))) =
    (S k).map (toΓ' k) := by
  have aux : ∀ (j : K) (h : eK j = eK k),
      (h ▸ (S j).map (toΓ' j) : List (Γ' (eK k))) = (S k).map (toΓ' k) := by
    intro j h
    have hjk : j = k := eK.injective h
    subst hjk
    rfl
  exact aux (eK.symm (eK k)) (eK.apply_symm_apply (eK k))

lemma eq_rec_nil {α : Type} {F : α → Type} {a b : α} (h : a = b) :
    (h ▸ ([] : List (F a)) : List (F b)) = [] := by
  subst h; rfl

lemma mapCfg_stk_apply
    {K K' : Type} {Γ : K → Type} {Γ' : K' → Type} {Λ Λ' σ σ' : Type}
    (eK : K ≃ K') (eΛ : Λ ≃ Λ') (eσ : σ ≃ σ')
    (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (c : TM2.Cfg Γ Λ σ) (k : K) :
    (mapCfg eK eΛ eσ toΓ' c).stk (eK k) = (c.stk k).map (toΓ' k) :=
  cast_stk_eq eK toΓ' c.stk k

lemma update_mapCfg_stk
    {K K' : Type} [DecidableEq K] [DecidableEq K']
    {Γ : K → Type} {Γ' : K' → Type}
    (eK : K ≃ K') (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    Function.update
      (fun k' => (eK.apply_symm_apply k' ▸ (S (eK.symm k')).map (toΓ' (eK.symm k'))))
      (eK k) (l.map (toΓ' k)) =
    (fun k' => (eK.apply_symm_apply k' ▸ (Function.update S k l (eK.symm k')).map (toΓ' (eK.symm k')))) := by
  funext k'
  by_cases h : k' = eK k
  · subst h
    rw [Function.update_self, cast_stk_eq eK toΓ' (Function.update S k l) k, Function.update_self]
  · have hne : eK.symm k' ≠ k := fun heq => h (by rw [← heq, eK.apply_symm_apply])
    simp only [Function.update_of_ne h, Function.update_of_ne hne]

lemma stepAux_mapStmt
    {K K' : Type} [DecidableEq K] [DecidableEq K']
    {Γ : K → Type} {Γ' : K' → Type} {Λ Λ' σ σ' : Type}
    (eK : K ≃ K') (eΛ : Λ ≃ Λ') (eσ : σ ≃ σ')
    (G : ∀ k, Set (Γ k))
    (toΓ' : ∀ k, Γ k → Γ' (eK k))
    (fromΓ' : ∀ k, Γ' (eK k) → Option (Γ k))
    (hinv : ∀ k a, a ∈ G k → fromΓ' k (toΓ' k a) = some a)
    (q : TM2.Stmt Γ Λ σ)
    (hq : ∀ k, pushedOn k q ⊆ G k)
    (v : σ) (S : ∀ k, List (Γ k))
    (hS : ∀ k, ∀ a ∈ S k, a ∈ G k) :
    let res := TM2.stepAux q v S
    TM2.stepAux (mapStmt eK eΛ eσ toΓ' fromΓ' q) (eσ v)
      (fun k' => eK.apply_symm_apply k' ▸ (S (eK.symm k')).map (toΓ' (eK.symm k'))) =
      mapCfg eK eΛ eσ toΓ' res ∧
    (∀ k, ∀ a ∈ res.stk k, a ∈ G k) := by
  induction q generalizing v S with
  | push k f q ih =>
      have hfG : f v ∈ G k := hq k (Or.inl (by simp))
      have hq' : ∀ j, pushedOn j q ⊆ G j := fun j x hx => hq j (Or.inr hx)
      have hS' : ∀ j, ∀ a ∈ Function.update S k (f v :: S k) j, a ∈ G j := by
        intro j a ha
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hfG
          · exact hS j a ha
        · simp only [Function.update_of_ne hj] at ha
          exact hS j a ha
      have hupd := update_mapCfg_stk eK toΓ' S k (f v :: S k)
      have hstk := cast_stk_eq eK toΓ' S k
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply, hstk]
      change TM2.stepAux (mapStmt eK eΛ eσ toΓ' fromΓ' q) (eσ v)
        (Function.update
          (fun k' => eK.apply_symm_apply k' ▸ (S (eK.symm k')).map (toΓ' (eK.symm k')))
          (eK k) ((f v :: S k).map (toΓ' k))) = _ ∧ _
      rw [hupd]
      exact ih hq' v (Function.update S k (f v :: S k)) hS'
  | peek k f q ih =>
      have hstk := cast_stk_eq eK toΓ' S k
      have hhead : ((S k).map (toΓ' k)).head?.bind (fromΓ' k) = (S k).head? := by
        cases hsk : S k with
        | nil => rfl
        | cons a tl =>
            simp only [List.map_cons, List.head?_cons, Option.bind_some]
            exact hinv k a (hS k a (by rw [hsk]; simp))
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply, hstk, hhead]
      exact ih hq (f v (S k).head?) S hS
  | pop k f q ih =>
      have hstk := cast_stk_eq eK toΓ' S k
      have hhead : ((S k).map (toΓ' k)).head?.bind (fromΓ' k) = (S k).head? := by
        cases hsk : S k with
        | nil => rfl
        | cons a tl =>
            simp only [List.map_cons, List.head?_cons, Option.bind_some]
            exact hinv k a (hS k a (by rw [hsk]; simp))
      have htail : ((S k).map (toΓ' k)).tail = (S k).tail.map (toΓ' k) := List.map_tail.symm
      have hupd := update_mapCfg_stk eK toΓ' S k (S k).tail
      have hS' : ∀ j, ∀ a ∈ Function.update S k (S k).tail j, a ∈ G j := by
        intro j a ha
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self] at ha
          exact hS j a (List.mem_of_mem_tail ha)
        · simp only [Function.update_of_ne hj] at ha
          exact hS j a ha
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply, hstk, hhead, htail]
      rw [hupd]
      exact ih hq (f v (S k).head?) (Function.update S k (S k).tail) hS'
  | load f q ih =>
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply]
      exact ih hq (f v) S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
      have hq₁ : ∀ j, pushedOn j q₁ ⊆ G j := fun j x hx => hq j (Or.inl hx)
      have hq₂ : ∀ j, pushedOn j q₂ ⊆ G j := fun j x hx => hq j (Or.inr hx)
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply]
      cases f v
      · exact ih₂ hq₂ v S hS
      · exact ih₁ hq₁ v S hS
  | goto f =>
      simp only [mapStmt, TM2.stepAux, Equiv.symm_apply_apply, mapCfg, Option.map_some]
      exact ⟨trivial, hS⟩
  | halt =>
      simp only [mapStmt, TM2.stepAux, mapCfg, Option.map_none]
      exact ⟨trivial, hS⟩

lemma iterate_flip_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ k, (flip bind f)^[k] none = none
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_flip_bind_none f k

/-- Determinism of `StateTransition.EvalsToInTime` when both endpoints are terminal (`f b = none`). -/
lemma evalsToInTime_det_halted {σ : Type} {f : σ → Option σ} {a b₁ b₂ : σ} {m₁ m₂ : ℕ}
    (h₁ : StateTransition.EvalsToInTime f a (some b₁) m₁)
    (h₂ : StateTransition.EvalsToInTime f a (some b₂) m₂)
    (ht₁ : f b₁ = none) (ht₂ : f b₂ = none) :
    b₁ = b₂ := by
  have he₁ := h₁.evals_in_steps
  have he₂ := h₂.evals_in_steps
  rcases lt_trichotomy h₁.steps h₂.steps with hlt | heq | hgt
  · have hsplit : h₂.steps = (h₂.steps - h₁.steps - 1) + 1 + h₁.steps := by omega
    rw [hsplit, Function.iterate_add_apply, he₁, Function.iterate_add_apply, Function.iterate_one] at he₂
    change (flip bind f)^[h₂.steps - h₁.steps - 1] (f b₁) = some b₂ at he₂
    rw [ht₁, iterate_flip_bind_none] at he₂
    cases he₂
  · rw [heq] at he₁
    exact Option.some.inj (he₁.symm.trans he₂)
  · have hsplit : h₁.steps = (h₁.steps - h₂.steps - 1) + 1 + h₂.steps := by omega
    rw [hsplit, Function.iterate_add_apply, he₂, Function.iterate_add_apply, Function.iterate_one] at he₁
    change (flip bind f)^[h₁.steps - h₂.steps - 1] (f b₂) = some b₁ at he₁
    rw [ht₂, iterate_flip_bind_none] at he₁
    cases he₁

/-- Every `TM2ComputableInPolyTime encodeString encodeAnswer f` yields a `CanonTM2` with the same behavior. -/
noncomputable def canonicalize {f : List Bool → Bool}
    (M : TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    { c : CanonTM2 // c.outMap true ≠ c.outMap false ∧
      ∀ x : List Bool, ∃ m,
        Nonempty (TM2OutputsInTime c.toFinTM2 (x.map c.inMap) (some [c.outMap (f x)]) m) } := by
  classical
  let tm := M.tm
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  let eK : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let eΛ : tm.Λ ≃ Fin (Fintype.card tm.Λ) := Fintype.equivFin tm.Λ
  let eσ : tm.σ ≃ Fin (Fintype.card tm.σ) := Fintype.equivFin tm.σ
  let G : ∀ k : tm.K, Set (tm.Γ k) := GoodSym M.toTM2ComputableAux
  have hGfin : ∀ k, (G k).Finite := goodSym_finite M.toTM2ComputableAux
  let eG : ∀ k : tm.K, (G k) ≃ Fin (Nat.card (G k)) := fun k => by
    haveI : Finite (G k) := (hGfin k).to_subtype
    exact Finite.equivFin (G k)
  let nΓ : Fin (Fintype.card tm.K) → ℕ := fun k' => Nat.card (G (eK.symm k')) + 1
  let toΓ' : ∀ k : tm.K, tm.Γ k → Fin (nΓ (eK k)) := fun k a =>
    if ha : a ∈ G k then
      ⟨(eG k ⟨a, ha⟩).val, by
        have hlt := (eG k ⟨a, ha⟩).isLt
        dsimp only [nΓ]
        rw [eK.symm_apply_apply]
        exact Nat.lt_succ_of_lt hlt⟩
    else
      ⟨Nat.card (G k), by
        dsimp only [nΓ]
        rw [eK.symm_apply_apply]
        exact Nat.lt_succ_self _⟩
  let fromΓ' : ∀ k : tm.K, Fin (nΓ (eK k)) → Option (tm.Γ k) := fun k y =>
    if hy : y.val < Nat.card (G k) then
      some ((eG k).symm ⟨y.val, hy⟩).1
    else
      none
  have hinv : ∀ k a, a ∈ G k → fromΓ' k (toΓ' k a) = some a := by
    intro k a ha
    have hlt : (eG k ⟨a, ha⟩).val < Nat.card (G k) := (eG k ⟨a, ha⟩).isLt
    simp only [fromΓ', toΓ', ha, ↓reduceDIte, hlt, Fin.eta, Equiv.symm_apply_apply]
  let prog : Fin (Fintype.card tm.Λ) →
      TM2.Stmt (fun k' => Fin (nΓ k')) (Fin (Fintype.card tm.Λ)) (Fin (Fintype.card tm.σ)) :=
    fun l' => mapStmt (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' fromΓ' (tm.m (eΛ.symm l'))
  let c : CanonTM2 := {
    nK := Fintype.card tm.K
    k₀ := eK tm.k₀
    k₁ := eK tm.k₁
    nΓ := nΓ
    nΛ := Fintype.card tm.Λ
    main := eΛ tm.main
    nσ := Fintype.card tm.σ
    init := eσ tm.initialState
    prog := prog
    inMap := fun b => toΓ' tm.k₀ (M.inputAlphabet.symm b)
    outMap := fun b => toΓ' tm.k₁ (M.outputAlphabet.symm b)
  }
  refine ⟨c, ?_, ?_⟩
  · intro heq
    have htG : M.outputAlphabet.symm true ∈ G tm.k₁ := Or.inl (Or.inr (by simp [tm]))
    have hfG : M.outputAlphabet.symm false ∈ G tm.k₁ := Or.inl (Or.inr (by simp [tm]))
    have h1 := hinv tm.k₁ _ htG
    have h2 := hinv tm.k₁ _ hfG
    change toΓ' tm.k₁ (M.outputAlphabet.symm true) = toΓ' tm.k₁ (M.outputAlphabet.symm false) at heq
    rw [heq] at h1
    rw [h2] at h1
    have h3 := Option.some.inj h1
    have h4 := M.outputAlphabet.symm.injective h3
    exact Bool.noConfusion h4
  · intro x
    have hout := M.outputsFun x
    have hstep : ∀ cfg : tm.Cfg, (∀ k, ∀ a ∈ cfg.stk k, a ∈ G k) →
        match tm.step cfg with
        | none => c.toFinTM2.step (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' cfg) = none
        | some cfg' =>
            c.toFinTM2.step (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' cfg) =
              some (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' cfg') ∧
            (∀ k, ∀ a ∈ cfg'.stk k, a ∈ G k) := by
      intro cfg hcfg
      rcases cfg with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          simp only [FinTM2.step, TM2.step, mapCfg, Option.map_some]
          have hq : ∀ k, pushedOn k (tm.m l) ⊆ G k := fun k a ha =>
            Or.inr (Set.mem_iUnion.mpr ⟨l, ha⟩)
          have hsim := stepAux_mapStmt (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ G toΓ' fromΓ' hinv (tm.m l) hq v S hcfg
          dsimp only [CanonTM2.toFinTM2, c, prog]
          simp only [Equiv.symm_apply_apply]
          exact ⟨congrArg some hsim.1, hsim.2⟩
    have hinit : mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (initList tm (x.map M.inputAlphabet.symm)) =
        initList c.toFinTM2 (x.map c.inMap) := by
      cases hcf1 : mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (initList tm (x.map M.inputAlphabet.symm)) with
      | mk l1 v1 s1 =>
        cases hcf2 : initList c.toFinTM2 (x.map c.inMap) with
        | mk l2 v2 s2 =>
          have hl : l1 = l2 := by
            have h1 := congrArg TM2.Cfg.l hcf1
            have h2 := congrArg TM2.Cfg.l hcf2
            exact h1.symm.trans h2
          have hv : v1 = v2 := by
            have h1 := congrArg TM2.Cfg.var hcf1
            have h2 := congrArg TM2.Cfg.var hcf2
            exact h1.symm.trans h2
          have hs : s1 = s2 := by
            funext k'
            have h1 : (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (initList tm (x.map M.inputAlphabet.symm))).stk k' = s1 k' :=
              congrArg (fun cfg => cfg.stk k') hcf1
            have h2 : (initList c.toFinTM2 (x.map c.inMap)).stk k' = s2 k' :=
              congrArg (fun cfg => cfg.stk k') hcf2
            rw [← h1, ← h2]
            by_cases h : k' = eK tm.k₀
            · subst h
              have hstk := mapCfg_stk_apply (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ'
                (initList tm (x.map M.inputAlphabet.symm)) tm.k₀
              rw [hstk]
              simp only [initList, CanonTM2.toFinTM2, c, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
                List.map_map, Function.comp_def]
            · have hne : eK.symm k' ≠ tm.k₀ := fun heq => h (by rw [← heq, eK.apply_symm_apply])
              simp only [mapCfg, initList, CanonTM2.toFinTM2, c, h, hne, ↓reduceDIte, List.map_nil]
              exact eq_rec_nil (F := fun k' => Fin (nΓ k')) (eK.apply_symm_apply k')
          subst hl; subst hv; subst hs; rfl
    have hhalt : mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (haltList tm [M.outputAlphabet.symm (f x)]) =
        haltList c.toFinTM2 [c.outMap (f x)] := by
      cases hcf1 : mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (haltList tm [M.outputAlphabet.symm (f x)]) with
      | mk l1 v1 s1 =>
        cases hcf2 : haltList c.toFinTM2 [c.outMap (f x)] with
        | mk l2 v2 s2 =>
          have hl : l1 = l2 := by
            have h1 := congrArg TM2.Cfg.l hcf1
            have h2 := congrArg TM2.Cfg.l hcf2
            exact h1.symm.trans h2
          have hv : v1 = v2 := by
            have h1 := congrArg TM2.Cfg.var hcf1
            have h2 := congrArg TM2.Cfg.var hcf2
            exact h1.symm.trans h2
          have hs : s1 = s2 := by
            funext k'
            have h1 : (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' (haltList tm [M.outputAlphabet.symm (f x)])).stk k' = s1 k' :=
              congrArg (fun cfg => cfg.stk k') hcf1
            have h2 : (haltList c.toFinTM2 [c.outMap (f x)]).stk k' = s2 k' :=
              congrArg (fun cfg => cfg.stk k') hcf2
            rw [← h1, ← h2]
            by_cases h : k' = eK tm.k₁
            · subst h
              have hstk := mapCfg_stk_apply (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ'
                (haltList tm [M.outputAlphabet.symm (f x)]) tm.k₁
              rw [hstk]
              simp only [haltList, CanonTM2.toFinTM2, c, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
                List.map_cons, List.map_nil]
            · have hne : eK.symm k' ≠ tm.k₁ := fun heq => h (by rw [← heq, eK.apply_symm_apply])
              simp only [mapCfg, haltList, CanonTM2.toFinTM2, c, h, hne, ↓reduceDIte, List.map_nil]
              exact eq_rec_nil (F := fun k' => Fin (nΓ k')) (eK.apply_symm_apply k')
          subst hl; subst hv; subst hs; rfl
    have hinitG : ∀ k, ∀ a ∈ (initList tm (x.map M.inputAlphabet.symm)).stk k, a ∈ G k := by
      intro k a ha
      simp only [initList] at ha
      split_ifs at ha with hk
      · subst hk; exact Or.inl (Or.inl (by simp [tm]))
      · cases ha
    have hstepBind : ∀ n (cfg : tm.Cfg), (∀ k, ∀ a ∈ cfg.stk k, a ∈ G k) →
        ∀ out : Option tm.Cfg,
          (flip bind tm.step)^[n] (some cfg) = out →
          (flip bind c.toFinTM2.step)^[n] (some (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' cfg)) =
            out.map (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ') := by
      intro n
      induction n with
      | zero =>
          intro cfg _ out h
          simp only [Function.iterate_zero_apply] at h ⊢
          rw [← h]; rfl
      | succ n ih =>
          intro cfg hcfg out h
          rw [Function.iterate_succ_apply] at h ⊢
          change (flip bind tm.step)^[n] (tm.step cfg) = out at h
          change (flip bind c.toFinTM2.step)^[n] (c.toFinTM2.step (mapCfg (Γ' := fun k' => Fin (nΓ k')) eK eΛ eσ toΓ' cfg)) = _
          have hs := hstep cfg hcfg
          cases h1 : tm.step cfg with
          | none =>
              rw [h1] at hs h
              dsimp only at hs
              rw [hs, iterate_flip_bind_none]
              rw [iterate_flip_bind_none] at h
              rw [← h]; rfl
          | some cfg1 =>
              rw [h1] at hs h
              dsimp only at hs
              rw [hs.1]
              exact ih cfg1 hs.2 out h
    refine ⟨hout.steps, ⟨⟨⟨hout.steps, ?_⟩, le_rfl⟩⟩⟩
    have hev : (flip bind tm.step)^[hout.steps] (some (initList tm (x.map M.inputAlphabet.symm))) =
        some (haltList tm [M.outputAlphabet.symm (f x)]) := hout.evals_in_steps
    simp only [Option.map_some]
    rw [← hinit, ← hhalt]
    exact hstepBind hout.steps (initList tm (x.map M.inputAlphabet.symm)) hinitG
      (some (haltList tm [M.outputAlphabet.symm (f x)])) hev

lemma polyTimeBoolFun_countable :
    Set.Countable { f : List Bool → Bool | PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f } := by
  classical
  let S := { f : List Bool → Bool | PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f }
  let encodeF : S → CanonTM2 := fun ⟨f, hf⟩ => (canonicalize (Classical.choice hf)).1
  have hinj : Function.Injective encodeF := by
    rintro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
    apply Subtype.ext
    funext x
    have hc₁ := (canonicalize (Classical.choice hf₁)).2
    have hc₂ := (canonicalize (Classical.choice hf₂)).2
    obtain ⟨hne₁, hrun₁⟩ := hc₁
    obtain ⟨_, hrun₂⟩ := hc₂
    obtain ⟨m₁, ⟨hm₁⟩⟩ := hrun₁ x
    obtain ⟨m₂, ⟨hm₂⟩⟩ := hrun₂ x
    change (canonicalize (Classical.choice hf₁)).1 = (canonicalize (Classical.choice hf₂)).1 at heq
    rw [← heq] at hm₂
    have hcfg := evalsToInTime_det_halted hm₁ hm₂ rfl rfl
    set c₁ := (canonicalize (Classical.choice hf₁)).1
    have hstk := congrArg (fun cfg => cfg.stk c₁.k₁) hcfg
    simp only [haltList, CanonTM2.toFinTM2, ↓reduceDIte] at hstk
    have hmpr : ∀ {α : Type} {p : α = α} {a b : α}, p.mpr a = p.mpr b → a = b := by
      intro α p a b hab; cases p; exact hab
    have hlist := hmpr hstk
    have hout : c₁.outMap (f₁ x) = c₁.outMap (f₂ x) := (List.cons.inj hlist).1
    cases hb₁ : f₁ x <;> cases hb₂ : f₂ x
    · exact hb₁.trans hb₂.symm
    · rw [hb₁, hb₂] at hout; exact False.elim (hne₁ hout.symm)
    · rw [hb₁, hb₂] at hout; exact False.elim (hne₁ hout)
    · exact hb₁.trans hb₂.symm
  have : Countable S := hinj.countable
  exact Set.countable_coe_iff.mp inferInstance

end PvsNP.Units.fr_lang_not_in_p_aux

theorem PvsNP.Units.fr_lang_not_in_p : ∃ L : Language Bool, L ∉ PvsNP.P := by
  classical
  let S := { f : List Bool → Bool | PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f }
  by_cases hne : S.Nonempty
  · have hcount : S.Countable := PvsNP.Units.fr_lang_not_in_p_aux.polyTimeBoolFun_countable
    obtain ⟨g, hg⟩ := hcount.exists_eq_range hne
    refine ⟨({ x : List Bool | g x.length x = false } : Set (List Bool)), ?_⟩
    rintro ⟨f, hf, hL⟩
    have hfr : f ∈ Set.range g := by rw [← hg]; exact hf
    obtain ⟨n, hn⟩ := hfr
    have hx := hL (List.replicate n true)
    change g (List.replicate n true).length (List.replicate n true) = false ↔
      f (List.replicate n true) = true at hx
    rw [List.length_replicate, hn] at hx
    cases hfval : f (List.replicate n true) <;> simp [hfval] at hx
  · refine ⟨(∅ : Set (List Bool)), ?_⟩
    rintro ⟨f, hf, _⟩
    exact hne ⟨f, hf⟩
