import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m1_tm2_to_st

open Turing

/-! ## Tape shifting, writing, and EvalsToInTime helpers -/

lemma tape_ext_nth {Γ : Type} [Inhabited Γ] {T₁ T₂ : Tape Γ}
    (h : ∀ i : ℤ, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  rcases T₁ with ⟨h₁, L₁, R₁⟩
  rcases T₂ with ⟨h₂, L₂, R₂⟩
  have hh : h₁ = h₂ := h 0
  have hL : L₁ = L₂ := ListBlank.ext fun n => h (-(n + 1 : ℕ))
  have hR : R₁ = R₂ := ListBlank.ext fun n => h ((n + 1 : ℕ))
  subst hh; subst hL; subst hR; rfl

lemma mk₁_nth_neg {Γ : Type} [Inhabited Γ] (cells : List Γ) (n : ℕ) :
    (Tape.mk₁ cells).nth (-(n + 1 : ℕ)) = default := by
  change (ListBlank.mk ([] : List Γ)).nth n = default
  simp [ListBlank.nth_mk, List.getI]

lemma mk₁_nth_nat {Γ : Type} [Inhabited Γ] (cells : List Γ) (n : ℕ) :
    (Tape.mk₁ cells).nth (n : ℕ) = cells.getI n := by
  change (Tape.mk' (ListBlank.mk []) (ListBlank.mk cells)).nth (n : ℕ) = cells.getI n
  rw [Tape.mk'_nth_nat, ListBlank.nth_mk]

def shiftZ {Γ : Type} [Inhabited Γ] (T : Tape Γ) : ℤ → Tape Γ
  | Int.ofNat n => (Tape.move Dir.right)^[n] T
  | Int.negSucc n => (Tape.move Dir.left)^[n + 1] T

lemma shiftZ_zero {Γ : Type} [Inhabited Γ] (T : Tape Γ) : shiftZ T 0 = T := rfl

lemma move_right_iter_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (n : ℕ) (i : ℤ) :
    ((Tape.move Dir.right)^[n] T).nth i = T.nth (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Tape.move_right_nth, ih (i + 1)]
      congr 1; omega

lemma move_left_iter_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (n : ℕ) (i : ℤ) :
    ((Tape.move Dir.left)^[n] T).nth i = T.nth (i - n) := by
  induction n generalizing i with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Tape.move_left_nth, ih (i - 1)]
      congr 1; omega

lemma shiftZ_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z i : ℤ) :
    (shiftZ T z).nth i = T.nth (i + z) := by
  cases z with
  | ofNat n =>
      rw [shiftZ, move_right_iter_nth]
      rfl
  | negSucc n =>
      rw [shiftZ, move_left_iter_nth]
      exact congrArg T.nth (by omega)

lemma shiftZ_head {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (shiftZ T z).head = T.nth z := by
  change (shiftZ T z).nth 0 = T.nth z
  rw [shiftZ_nth, zero_add]

lemma shiftZ_right₀_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) (k : ℕ) :
    (shiftZ T z).right₀.nth k = T.nth ((k : ℤ) + z) := by
  rw [Tape.right₀_nth, shiftZ_nth]

lemma shiftZ_move_right {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (shiftZ T z).move Dir.right = shiftZ T (z + 1) := by
  apply tape_ext_nth; intro i
  rw [Tape.move_right_nth, shiftZ_nth, shiftZ_nth]
  exact congrArg T.nth (by omega)

lemma shiftZ_move_left {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (shiftZ T z).move Dir.left = shiftZ T (z - 1) := by
  apply tape_ext_nth; intro i
  rw [Tape.move_left_nth, shiftZ_nth, shiftZ_nth]
  exact congrArg T.nth (by omega)

lemma cfg_shiftZ_eq {Γ Λ : Type} [Inhabited Γ] (q : Λ) (T : Tape Γ) {z₁ z₂ : ℤ} (h : z₁ = z₂) :
    (some ⟨q, shiftZ T z₁⟩ : Option (TM0.Cfg Γ Λ)) = some ⟨q, shiftZ T z₂⟩ := by
  subst h; rfl

def tapeWriteZ {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) (g : Γ) : Tape Γ :=
  shiftZ ((shiftZ T z).write g) (-z)

lemma tapeWriteZ_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) (g : Γ) (i : ℤ) :
    (tapeWriteZ T z g).nth i = if i = z then g else T.nth i := by
  rw [tapeWriteZ, shiftZ_nth, Tape.write_nth, shiftZ_nth]
  have h1 : (i + -z = 0) ↔ (i = z) := by omega
  have h2 : i + -z + z = i := by omega
  rw [h2]
  by_cases h : i = z
  · rw [ite_eq_left (h1.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (h1.mp hc)), ite_eq_right h]

lemma shiftZ_write {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) (g : Γ) :
    (shiftZ T z).write g = shiftZ (tapeWriteZ T z g) z := by
  apply tape_ext_nth; intro i
  rw [Tape.write_nth, shiftZ_nth, shiftZ_nth, tapeWriteZ_nth]
  by_cases h : i = 0
  · subst h; simp
  · have h2 : i + z ≠ z := by omega
    rw [ite_eq_right h, ite_eq_right h2]

lemma evals_zero {σ : Type} {f : σ → Option σ} (a : σ) :
    Nonempty (StateTransition.EvalsToInTime f a (some a) 0) :=
  ⟨⟨⟨0, rfl⟩, le_rfl⟩⟩

lemma evals_step {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m : ℕ}
    (h1 : f a = some b) (hrest : Nonempty (StateTransition.EvalsToInTime f b c m)) :
    Nonempty (StateTransition.EvalsToInTime f a c (m + 1)) := by
  obtain ⟨hr⟩ := hrest
  exact ⟨⟨⟨hr.steps + 1, by
    rw [Function.iterate_succ_apply]
    change (flip bind f)^[hr.steps] (Option.bind (some a) f) = c
    rw [Option.bind_some, h1]
    exact hr.evals_in_steps⟩, Nat.add_le_add_right hr.steps_le_m 1⟩⟩

lemma evals_one {σ : Type} {f : σ → Option σ} {a b : σ}
    (h1 : f a = some b) :
    Nonempty (StateTransition.EvalsToInTime f a (some b) 1) :=
  evals_step h1 (evals_zero b)

lemma evals_trans {σ : Type} {f : σ → Option σ} {a b c : σ} {m₁ m₂ : ℕ}
    (h₁ : Nonempty (StateTransition.EvalsToInTime f a (some b) m₁))
    (h₂ : Nonempty (StateTransition.EvalsToInTime f b (some c) m₂)) :
    Nonempty (StateTransition.EvalsToInTime f a (some c) (m₁ + m₂)) := by
  obtain ⟨r₁⟩ := h₁
  obtain ⟨r₂⟩ := h₂
  exact ⟨⟨⟨r₁.steps + r₂.steps, by
    rw [add_comm, Function.iterate_add_apply, r₁.evals_in_steps]
    exact r₂.evals_in_steps⟩, Nat.add_le_add r₁.steps_le_m r₂.steps_le_m⟩⟩

lemma evals_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m₁ m₂ : ℕ}
    (h : Nonempty (StateTransition.EvalsToInTime f a b m₁)) (hle : m₁ ≤ m₂) :
    Nonempty (StateTransition.EvalsToInTime f a b m₂) := by
  obtain ⟨r⟩ := h
  exact ⟨⟨r.toEvalsTo, le_trans r.steps_le_m hle⟩⟩

lemma iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

/-! ## Finite reachable symbols and sub-statements of a FinTM2 -/

noncomputable def pushedByStmt (tm : FinTM2) (k : tm.K) :
    TM2.Stmt tm.Γ tm.Λ tm.σ → Finset (tm.Γ k) := by
  classical
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.σ := tm.σFin
  intro q
  induction q with
  | push k' f _ ih =>
      exact (if h : k' = k then Finset.univ.image (fun v : tm.σ => h ▸ f v) else ∅) ∪ ih
  | peek _ _ _ ih => exact ih
  | pop _ _ _ ih => exact ih
  | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁ ∪ ih₂
  | goto _ => exact ∅
  | halt => exact ∅

lemma pushedByStmt_push_mem (tm : FinTM2) (k : tm.K) (f : tm.σ → tm.Γ k)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) :
    f v ∈ pushedByStmt tm k (.push k f q) := by
  classical
  let _ : DecidableEq tm.K := tm.kDecidableEq
  let _ : Fintype tm.σ := tm.σFin
  simp only [pushedByStmt, ↓reduceDIte, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact Or.inl ⟨v, rfl⟩

lemma pushedByStmt_mono (tm : FinTM2) (k : tm.K) :
    ∀ {q₁ q₂ : TM2.Stmt tm.Γ tm.Λ tm.σ}, q₁ ∈ TM2.stmts₁ q₂ →
      pushedByStmt tm k q₁ ⊆ pushedByStmt tm k q₂ := by
  classical
  intro q₁ q₂ hmem
  induction q₂ with
  | push k' f q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hmem
      rcases hmem with rfl | hq
      · exact Finset.Subset.refl _
      · exact (ih hq).trans (by simp [pushedByStmt])
  | peek _ _ q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hmem
      rcases hmem with rfl | hq
      · exact Finset.Subset.refl _
      · exact (ih hq).trans (by simp [pushedByStmt])
  | pop _ _ q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hmem
      rcases hmem with rfl | hq
      · exact Finset.Subset.refl _
      · exact (ih hq).trans (by simp [pushedByStmt])
  | load _ q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hmem
      rcases hmem with rfl | hq
      · exact Finset.Subset.refl _
      · exact (ih hq).trans (by simp [pushedByStmt])
  | branch _ q₁' q₂' ih₁ ih₂ =>
      simp only [TM2.stmts₁, Finset.mem_insert, Finset.mem_union] at hmem
      rcases hmem with rfl | h1 | h2
      · exact Finset.Subset.refl _
      · exact (ih₁ h1).trans (by simp [pushedByStmt])
      · exact (ih₂ h2).trans (by simp [pushedByStmt])
  | goto _ =>
      simp only [TM2.stmts₁, Finset.mem_singleton] at hmem
      subst hmem; exact Finset.Subset.refl _
  | halt =>
      simp only [TM2.stmts₁, Finset.mem_singleton] at hmem
      subst hmem; exact Finset.Subset.refl _

noncomputable def reachSet (tm : FinTM2) (k : tm.K) : Finset (tm.Γ k) := by
  classical
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin
  exact (Finset.univ.biUnion fun l : tm.Λ => pushedByStmt tm k (tm.m l)) ∪
    (if h : k = tm.k₀ then Finset.univ.image (fun x : tm.Γ tm.k₀ => h ▸ x) else ∅)

abbrev Reach (tm : FinTM2) (k : tm.K) : Type :=
  { x : tm.Γ k // x ∈ reachSet tm k }

noncomputable def allStmts (tm : FinTM2) : Finset (TM2.Stmt tm.Γ tm.Λ tm.σ) := by
  classical
  letI : Fintype tm.Λ := tm.ΛFin
  exact Finset.univ.biUnion fun l : tm.Λ => TM2.stmts₁ (tm.m l)

abbrev SubStmt (tm : FinTM2) : Type :=
  { q : TM2.Stmt tm.Γ tm.Λ tm.σ // q ∈ allStmts tm }

lemma mem_allStmts_m (tm : FinTM2) (l : tm.Λ) : tm.m l ∈ allStmts tm := by
  classical
  let _ : Fintype tm.Λ := tm.ΛFin
  simp only [allStmts, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨l, TM2.stmts₁_self⟩

lemma mem_allStmts_sub (tm : FinTM2) {q₁ q₂ : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h₁ : q₁ ∈ TM2.stmts₁ q₂) (h₂ : q₂ ∈ allStmts tm) : q₁ ∈ allStmts tm := by
  classical
  let _ : Fintype tm.Λ := tm.ΛFin
  simp only [allStmts, Finset.mem_biUnion, Finset.mem_univ, true_and] at h₂ ⊢
  rcases h₂ with ⟨l, hl⟩
  exact ⟨l, TM2.stmts₁_trans hl h₁⟩

lemma mem_reachSet_k0 (tm : FinTM2) (x : tm.Γ tm.k₀) : x ∈ reachSet tm tm.k₀ := by
  classical
  let _ : DecidableEq tm.K := tm.kDecidableEq
  let _ : Fintype tm.Λ := tm.ΛFin
  let _ : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin
  simp only [reachSet, ↓reduceDIte, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨x, rfl⟩

lemma mem_reachSet_push (tm : FinTM2) {k : tm.K} {f : tm.σ → tm.Γ k}
    {q : TM2.Stmt tm.Γ tm.Λ tm.σ} (hq : TM2.Stmt.push k f q ∈ allStmts tm) (v : tm.σ) :
    f v ∈ reachSet tm k := by
  classical
  let _ : Fintype tm.Λ := tm.ΛFin
  simp only [allStmts, Finset.mem_biUnion, Finset.mem_univ, true_and] at hq
  rcases hq with ⟨l, hl⟩
  have hsub := pushedByStmt_mono tm k hl
  have hmem := hsub (pushedByStmt_push_mem tm k f q v)
  simp only [reachSet, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl ⟨l, hmem⟩

lemma sub_push (tm : FinTM2) {k : tm.K} {f : tm.σ → tm.Γ k} {q : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.push k f q ∈ allStmts tm) : q ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

lemma sub_peek (tm : FinTM2) {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ}
    {q : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.peek k f q ∈ allStmts tm) : q ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

lemma sub_pop (tm : FinTM2) {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ}
    {q : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.pop k f q ∈ allStmts tm) : q ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

lemma sub_load (tm : FinTM2) {f : tm.σ → tm.σ} {q : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.load f q ∈ allStmts tm) : q ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

lemma sub_branch_left (tm : FinTM2) {f : tm.σ → Bool} {q₁ q₂ : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.branch f q₁ q₂ ∈ allStmts tm) : q₁ ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

lemma sub_branch_right (tm : FinTM2) {f : tm.σ → Bool} {q₁ q₂ : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (h : TM2.Stmt.branch f q₁ q₂ ∈ allStmts tm) : q₂ ∈ allStmts tm :=
  mem_allStmts_sub tm (by simp [TM2.stmts₁, TM2.stmts₁_self]) h

/-! ## Tape Alphabet and State Space for the Single-Tape Simulator -/

abbrev Track (tm : FinTM2) : Type :=
  ∀ k : tm.K, Option (Reach tm k)

inductive Sym (A B : Type) (tm : FinTM2) where
  | blank
  | inp (a : A)
  | out (b : B)
  | wall
  | outWall
  | mark
  | cell (tr : Track tm)

instance (A B : Type) (tm : FinTM2) : Inhabited (Sym A B tm) := ⟨.blank⟩

def symEquiv (A B : Type) (tm : FinTM2) :
    Sym A B tm ≃ Fin 4 ⊕ A ⊕ B ⊕ Track tm where
  toFun
    | .blank => Sum.inl ⟨0, by omega⟩
    | .wall => Sum.inl ⟨1, by omega⟩
    | .outWall => Sum.inl ⟨2, by omega⟩
    | .mark => Sum.inl ⟨3, by omega⟩
    | .inp a => Sum.inr (Sum.inl a)
    | .out b => Sum.inr (Sum.inr (Sum.inl b))
    | .cell tr => Sum.inr (Sum.inr (Sum.inr tr))
  invFun
    | Sum.inl ⟨0, _⟩ => .blank
    | Sum.inl ⟨1, _⟩ => .wall
    | Sum.inl ⟨2, _⟩ => .outWall
    | Sum.inl ⟨3, _⟩ => .mark
    | Sum.inl ⟨n + 4, hn⟩ => absurd hn (by omega)
    | Sum.inr (Sum.inl a) => .inp a
    | Sum.inr (Sum.inr (Sum.inl b)) => .out b
    | Sum.inr (Sum.inr (Sum.inr tr)) => .cell tr
  left_inv s := by cases s <;> rfl
  right_inv x := by
    rcases x with ⟨n, hn⟩ | a | b | tr
    · interval_cases n <;> rfl
    · rfl
    · rfl
    · rfl

noncomputable abbrev fintypeSym (A B : Type) [Fintype A] [Fintype B] (tm : FinTM2) :
    Fintype (Sym A B tm) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.K := tm.kFin
  exact Fintype.ofEquiv _ (symEquiv A B tm).symm

inductive State (A B : Type) (tm : FinTM2) where
  | p1_toRight
  | p1_startFetch
  | p1_seekL
  | p1_carryR (a : A)
  | p1_backToWall
  | p1_doneL
  | exec (q : SubStmt tm) (v : tm.σ)
  | pushSeek (q : SubStmt tm) (v : tm.σ)
  | peekSeek (q : SubStmt tm) (v : tm.σ)
  | peekRead (q : SubStmt tm) (v : tm.σ)
  | popSeek (q : SubStmt tm) (v : tm.σ)
  | popRead (q : SubStmt tm) (v : tm.σ)
  | rewind (q : SubStmt tm) (v : tm.σ)
  | p3_toEnd
  | p3_startFetch
  | p3_fetch
  | p3_carryOut (b : B)
  | p3_backToOutWall
  | p3_toOutWall
  | halt

instance (A B : Type) (tm : FinTM2) : Inhabited (State A B tm) := ⟨.p1_toRight⟩

def stateEquiv (A B : Type) (tm : FinTM2) :
    State A B tm ≃ Fin 11 ⊕ A ⊕ B ⊕ (Fin 7 × SubStmt tm × tm.σ) where
  toFun
    | .p1_toRight => Sum.inl ⟨0, by omega⟩
    | .p1_startFetch => Sum.inl ⟨1, by omega⟩
    | .p1_seekL => Sum.inl ⟨2, by omega⟩
    | .p1_backToWall => Sum.inl ⟨3, by omega⟩
    | .p1_doneL => Sum.inl ⟨4, by omega⟩
    | .p3_toEnd => Sum.inl ⟨5, by omega⟩
    | .p3_startFetch => Sum.inl ⟨6, by omega⟩
    | .p3_fetch => Sum.inl ⟨7, by omega⟩
    | .p3_backToOutWall => Sum.inl ⟨8, by omega⟩
    | .p3_toOutWall => Sum.inl ⟨9, by omega⟩
    | .halt => Sum.inl ⟨10, by omega⟩
    | .p1_carryR a => Sum.inr (Sum.inl a)
    | .p3_carryOut b => Sum.inr (Sum.inr (Sum.inl b))
    | .exec q v => Sum.inr (Sum.inr (Sum.inr (⟨0, by omega⟩, q, v)))
    | .pushSeek q v => Sum.inr (Sum.inr (Sum.inr (⟨1, by omega⟩, q, v)))
    | .peekSeek q v => Sum.inr (Sum.inr (Sum.inr (⟨2, by omega⟩, q, v)))
    | .peekRead q v => Sum.inr (Sum.inr (Sum.inr (⟨3, by omega⟩, q, v)))
    | .popSeek q v => Sum.inr (Sum.inr (Sum.inr (⟨4, by omega⟩, q, v)))
    | .popRead q v => Sum.inr (Sum.inr (Sum.inr (⟨5, by omega⟩, q, v)))
    | .rewind q v => Sum.inr (Sum.inr (Sum.inr (⟨6, by omega⟩, q, v)))
  invFun
    | Sum.inl ⟨0, _⟩ => .p1_toRight
    | Sum.inl ⟨1, _⟩ => .p1_startFetch
    | Sum.inl ⟨2, _⟩ => .p1_seekL
    | Sum.inl ⟨3, _⟩ => .p1_backToWall
    | Sum.inl ⟨4, _⟩ => .p1_doneL
    | Sum.inl ⟨5, _⟩ => .p3_toEnd
    | Sum.inl ⟨6, _⟩ => .p3_startFetch
    | Sum.inl ⟨7, _⟩ => .p3_fetch
    | Sum.inl ⟨8, _⟩ => .p3_backToOutWall
    | Sum.inl ⟨9, _⟩ => .p3_toOutWall
    | Sum.inl ⟨10, _⟩ => .halt
    | Sum.inl ⟨n + 11, hn⟩ => absurd hn (by omega)
    | Sum.inr (Sum.inl a) => .p1_carryR a
    | Sum.inr (Sum.inr (Sum.inl b)) => .p3_carryOut b
    | Sum.inr (Sum.inr (Sum.inr (⟨0, _⟩, q, v))) => .exec q v
    | Sum.inr (Sum.inr (Sum.inr (⟨1, _⟩, q, v))) => .pushSeek q v
    | Sum.inr (Sum.inr (Sum.inr (⟨2, _⟩, q, v))) => .peekSeek q v
    | Sum.inr (Sum.inr (Sum.inr (⟨3, _⟩, q, v))) => .peekRead q v
    | Sum.inr (Sum.inr (Sum.inr (⟨4, _⟩, q, v))) => .popSeek q v
    | Sum.inr (Sum.inr (Sum.inr (⟨5, _⟩, q, v))) => .popRead q v
    | Sum.inr (Sum.inr (Sum.inr (⟨6, _⟩, q, v))) => .rewind q v
    | Sum.inr (Sum.inr (Sum.inr (⟨n + 7, hn⟩, _, _))) => absurd hn (by omega)
  left_inv s := by cases s <;> rfl
  right_inv x := by
    rcases x with ⟨n, hn⟩ | a | b | ⟨⟨m, hm⟩, q, v⟩
    · interval_cases n <;> rfl
    · rfl
    · rfl
    · interval_cases m <;> rfl

noncomputable abbrev fintypeState (A B : Type) [Fintype A] [Fintype B] (tm : FinTM2) :
    Fintype (State A B tm) := by
  letI : Fintype tm.σ := tm.σFin
  exact Fintype.ofEquiv _ (stateEquiv A B tm).symm

/-! ## Track operations -/

def readTrack {A B : Type} {tm : FinTM2} (g : Sym A B tm) (k : tm.K) :
    Option (Reach tm k) :=
  match g with
  | .cell tr => tr k
  | _ => none

def setTrack {A B : Type} {tm : FinTM2} (g : Sym A B tm) (k : tm.K)
    (v : Option (Reach tm k)) : Sym A B tm :=
  letI : DecidableEq tm.K := tm.kDecidableEq
  match g with
  | .cell tr => .cell (Function.update tr k v)
  | _ => .cell (Function.update (fun _ => none) k v)

def singleTrack (tm : FinTM2) (k : tm.K) (v : Reach tm k) : Track tm :=
  letI : DecidableEq tm.K := tm.kDecidableEq
  Function.update (fun _ => none) k (some v)

def isTrackOrBlank {A B : Type} {tm : FinTM2} : Sym A B tm → Prop
  | .blank => True
  | .cell _ => True
  | _ => False

lemma isTrackOrBlank_setTrack {A B : Type} {tm : FinTM2} (g : Sym A B tm) (k : tm.K)
    (v : Option (Reach tm k)) : isTrackOrBlank (setTrack g k v) := by
  cases g <;> trivial

lemma readTrack_setTrack_self {A B : Type} {tm : FinTM2} {g : Sym A B tm}
    (hg : isTrackOrBlank g) (k : tm.K) (v : Option (Reach tm k)) :
    readTrack (setTrack g k v) k = v := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  cases g with
  | blank => simp [setTrack, readTrack, Function.update_self]
  | cell tr => simp [setTrack, readTrack, Function.update_self]
  | _ => cases hg

lemma readTrack_setTrack_ne {A B : Type} {tm : FinTM2} {g : Sym A B tm}
    (hg : isTrackOrBlank g) {k k' : tm.K} (hne : k' ≠ k) (v : Option (Reach tm k)) :
    readTrack (setTrack g k v) k' = readTrack g k' := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  cases g with
  | blank => simp [setTrack, readTrack, Function.update_of_ne hne]
  | cell tr => simp [setTrack, readTrack, Function.update_of_ne hne]
  | _ => cases hg

lemma readTrack_singleTrack_self {A B : Type} {tm : FinTM2} (k : tm.K) (v : Reach tm k) :
    readTrack (Sym.cell (singleTrack tm k v) : Sym A B tm) k = some v := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  simp [readTrack, singleTrack, Function.update_self]

lemma readTrack_singleTrack_ne {A B : Type} {tm : FinTM2} {k k' : tm.K} (hne : k' ≠ k)
    (v : Reach tm k) :
    readTrack (Sym.cell (singleTrack tm k v) : Sym A B tm) k' = none := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  simp [readTrack, singleTrack, Function.update_of_ne hne]

/-! ## Transition function of the Single-Tape Machine -/

noncomputable def simDelta {A B : Type} (aux : TM2ComputableAux A B) :
    TM0.Machine (Sym A B aux.tm) (State A B aux.tm)
  -- Phase 1
  | .p1_toRight, .inp _ => some (.p1_toRight, .move .right)
  | .p1_toRight, _ => some (.p1_startFetch, .write .wall)
  | .p1_startFetch, _ => some (.p1_seekL, .move .left)
  | .p1_seekL, .mark => some (.p1_seekL, .move .left)
  | .p1_seekL, .inp a => some (.p1_carryR a, .write .mark)
  | .p1_seekL, _ => some (.p1_doneL, .move .right)
  | .p1_carryR a, .blank =>
      let sym : Reach aux.tm aux.tm.k₀ :=
        ⟨aux.inputAlphabet.invFun a, mem_reachSet_k0 aux.tm _⟩
      some (.p1_backToWall, .write (.cell (singleTrack aux.tm aux.tm.k₀ sym)))
  | .p1_carryR a, _ => some (.p1_carryR a, .move .right)
  | .p1_backToWall, .wall => some (.p1_seekL, .move .left)
  | .p1_backToWall, _ => some (.p1_backToWall, .move .left)
  | .p1_doneL, .wall =>
      some (.exec ⟨aux.tm.m aux.tm.main, mem_allStmts_m aux.tm aux.tm.main⟩
        aux.tm.initialState, .write .wall)
  | .p1_doneL, _ => some (.p1_doneL, .move .right)
  -- Phase 2
  | .exec q v, _ =>
      match hq : q.val with
      | .push _ _ _ => some (.pushSeek q v, .move .right)
      | .peek _ _ _ => some (.peekSeek q v, .move .right)
      | .pop _ _ _ => some (.popSeek q v, .move .right)
      | .load a q' =>
          some (.exec ⟨q', sub_load aux.tm (hq ▸ q.property)⟩ (a v), .write .wall)
      | .branch f q₁ q₂ =>
          if f v then
            some (.exec ⟨q₁, sub_branch_left aux.tm (hq ▸ q.property)⟩ v, .write .wall)
          else
            some (.exec ⟨q₂, sub_branch_right aux.tm (hq ▸ q.property)⟩ v, .write .wall)
      | .goto f =>
          some (.exec ⟨aux.tm.m (f v), mem_allStmts_m aux.tm (f v)⟩ v, .write .wall)
      | .halt => some (.p3_toEnd, .move .right)
  | .pushSeek q v, g =>
      match hq : q.val with
      | .push k f q' =>
          if (readTrack g k).isSome then
            some (.pushSeek q v, .move .right)
          else
            let sym : Reach aux.tm k := ⟨f v, mem_reachSet_push aux.tm (hq ▸ q.property) v⟩
            some (.rewind ⟨q', sub_push aux.tm (hq ▸ q.property)⟩ v,
              .write (setTrack g k (some sym)))
      | _ => none
  | .peekSeek q v, g =>
      match _hq : q.val with
      | .peek k _ _ =>
          if (readTrack g k).isSome then
            some (.peekSeek q v, .move .right)
          else
            some (.peekRead q v, .move .left)
      | _ => none
  | .peekRead q v, g =>
      match hq : q.val with
      | .peek k f q' =>
          let nextQ : SubStmt aux.tm := ⟨q', sub_peek aux.tm (hq ▸ q.property)⟩
          match g with
          | .wall => some (.exec nextQ (f v none), .write .wall)
          | _ =>
              some (.rewind nextQ (f v ((readTrack g k).map Subtype.val)), .write g)
      | _ => none
  | .popSeek q v, g =>
      match _hq : q.val with
      | .pop k _ _ =>
          if (readTrack g k).isSome then
            some (.popSeek q v, .move .right)
          else
            some (.popRead q v, .move .left)
      | _ => none
  | .popRead q v, g =>
      match hq : q.val with
      | .pop k f q' =>
          let nextQ : SubStmt aux.tm := ⟨q', sub_pop aux.tm (hq ▸ q.property)⟩
          match g with
          | .wall => some (.exec nextQ (f v none), .write .wall)
          | _ =>
              some (.rewind nextQ (f v ((readTrack g k).map Subtype.val)),
                .write (setTrack g k none))
      | _ => none
  | .rewind q v, .wall => some (.exec q v, .write .wall)
  | .rewind q v, _ => some (.rewind q v, .move .left)
  -- Phase 3
  | .p3_toEnd, g =>
      if (readTrack g aux.tm.k₁).isSome then
        some (.p3_toEnd, .move .right)
      else
        some (.p3_startFetch, .write .outWall)
  | .p3_startFetch, _ => some (.p3_fetch, .move .left)
  | .p3_fetch, .mark => some (.p3_fetch, .move .left)
  | .p3_fetch, .wall => some (.p3_toOutWall, .move .right)
  | .p3_fetch, g =>
      match readTrack g aux.tm.k₁ with
      | some y => some (.p3_carryOut (aux.outputAlphabet y.val), .write .mark)
      | none => none
  | .p3_carryOut b, .mark => some (.p3_carryOut b, .move .right)
  | .p3_carryOut b, .outWall => some (.p3_carryOut b, .move .right)
  | .p3_carryOut b, .out _ => some (.p3_carryOut b, .move .right)
  | .p3_carryOut b, _ => some (.p3_backToOutWall, .write (.out b))
  | .p3_backToOutWall, .outWall => some (.p3_fetch, .move .left)
  | .p3_backToOutWall, _ => some (.p3_backToOutWall, .move .left)
  | .p3_toOutWall, .outWall => some (.halt, .move .right)
  | .p3_toOutWall, _ => some (.p3_toOutWall, .move .right)
  | .halt, _ => none

noncomputable abbrev simMachine {A B : Type} [Fintype A] [Fintype B]
    (aux : TM2ComputableAux A B) : PvsNP.SingleTape.Machine A B where
  Γ := Sym A B aux.tm
  Λ := State A B aux.tm
  fintypeΓ := fintypeSym A B aux.tm
  fintypeΛ := fintypeState A B aux.tm
  inp := Sym.inp
  out := Sym.out
  inp_injective := fun _ _ h => by cases h; rfl
  out_injective := fun _ _ h => by cases h; rfl
  inp_ne_blank := fun _ h => by cases h
  out_ne_blank := fun _ h => by cases h
  δ := simDelta aux

lemma step_write {A B : Type} [Fintype A] [Fintype B] {aux : TM2ComputableAux A B}
    {q q' : State A B aux.tm} {T : Tape (Sym A B aux.tm)} {g : Sym A B aux.tm}
    (h : simDelta aux q T.head = some (q', .write g)) :
    (simMachine aux).step ⟨q, T⟩ = some ⟨q', T.write g⟩ := by
  change Option.map _ (simDelta aux q T.head) = _
  rw [h]; rfl

lemma step_move {A B : Type} [Fintype A] [Fintype B] {aux : TM2ComputableAux A B}
    {q q' : State A B aux.tm} {T : Tape (Sym A B aux.tm)} {d : Dir}
    (h : simDelta aux q T.head = some (q', .move d)) :
    (simMachine aux).step ⟨q, T⟩ = some ⟨q', T.move d⟩ := by
  change Option.map _ (simDelta aux q T.head) = _
  rw [h]; rfl

/-! ## Representation Invariant and Stack Depth -/

def Represents {A B : Type} {tm : FinTM2} (T : Tape (Sym A B tm))
    (S : ∀ k : tm.K, List (Reach tm k)) : Prop :=
  T.head = .wall ∧
  (∀ i : ℕ, isTrackOrBlank (T.nth ((i + 1 : ℕ) : ℤ))) ∧
  (∀ (k : tm.K) (i : ℕ), readTrack (T.nth ((i + 1 : ℕ) : ℤ)) k = (S k).reverse[i]?)

def liftStk {tm : FinTM2} (S : ∀ k : tm.K, List (Reach tm k)) : ∀ k : tm.K, List (tm.Γ k) :=
  fun k => (S k).map Subtype.val

noncomputable def maxDepth {tm : FinTM2} (S : ∀ k : tm.K, List (Reach tm k)) : ℕ :=
  (@Finset.univ tm.K tm.kFin).sup (fun k => (S k).length)

lemma length_le_maxDepth {tm : FinTM2} (S : ∀ k : tm.K, List (Reach tm k)) (k : tm.K) :
    (S k).length ≤ maxDepth S :=
  Finset.le_sup (f := fun j => (S j).length) (@Finset.mem_univ tm.K tm.kFin k)

lemma maxDepth_update_cons {tm : FinTM2} (S : ∀ k : tm.K, List (Reach tm k))
    (k : tm.K) (x : Reach tm k) :
    letI : DecidableEq tm.K := tm.kDecidableEq
    maxDepth (Function.update S k (x :: S k)) ≤ maxDepth S + 1 := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  unfold maxDepth
  apply Finset.sup_le
  intro j _
  by_cases h : j = k
  · subst h
    rw [Function.update_self, List.length_cons]
    have := length_le_maxDepth S j
    unfold maxDepth at this; omega
  · rw [Function.update_of_ne h]
    have := length_le_maxDepth S j
    unfold maxDepth at this; omega

lemma maxDepth_update_tail {tm : FinTM2} (S : ∀ k : tm.K, List (Reach tm k)) (k : tm.K) :
    letI : DecidableEq tm.K := tm.kDecidableEq
    maxDepth (Function.update S k (S k).tail) ≤ maxDepth S := by
  let _ : DecidableEq tm.K := tm.kDecidableEq
  unfold maxDepth
  apply Finset.sup_le
  intro j _
  by_cases h : j = k
  · subst h
    rw [Function.update_self, List.length_tail]
    have := length_le_maxDepth S j
    unfold maxDepth at this; omega
  · rw [Function.update_of_ne h]
    exact length_le_maxDepth S j

def initReachStk {A B : Type} (aux : TM2ComputableAux A B) (x : List A) :
    ∀ k : aux.tm.K, List (Reach aux.tm k) :=
  letI : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  fun k =>
    if h : k = aux.tm.k₀ then
      h ▸ (x.map fun a => ⟨aux.inputAlphabet.invFun a, mem_reachSet_k0 aux.tm _⟩)
    else []

lemma liftStk_initReachStk {A B : Type} (aux : TM2ComputableAux A B) (x : List A) :
    liftStk (initReachStk aux x) =
      (initList aux.tm (x.map aux.inputAlphabet.invFun)).stk := by
  let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  funext k
  simp only [liftStk, initReachStk, initList]
  by_cases h : k = aux.tm.k₀
  · subst h; simp [List.map_map, Function.comp_def]
  · simp [h]

lemma maxDepth_initReachStk {A B : Type} (aux : TM2ComputableAux A B) (x : List A) :
    maxDepth (initReachStk aux x) ≤ x.length := by
  let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  unfold maxDepth
  apply Finset.sup_le
  intro j _
  simp only [initReachStk]
  by_cases h : j = aux.tm.k₀
  · subst h; simp
  · simp [h]

/-! ## Phase 1 Proof: Input Reversal onto Track k₀ -/

def Phase1Inv {A B : Type} (aux : TM2ComputableAux A B) (x : List A)
    (T : Tape (Sym A B aux.tm)) (done : ℕ) : Prop :=
  T.nth 0 = .wall ∧
  (∀ j : ℕ, j < done → T.nth (-(j + 1 : ℕ)) = .mark) ∧
  (∀ (j : ℕ) (hj : j < x.length), done ≤ j →
    T.nth (-(j + 1 : ℕ)) = .inp (x.reverse[j]'(by simpa using hj))) ∧
  (∀ j : ℕ, x.length ≤ j → T.nth (-(j + 1 : ℕ)) = .blank) ∧
  (∀ (i : ℕ) (hi : i < done),
    ∃ (hix : i < x.length),
      T.nth ((i + 1 : ℕ) : ℤ) =
        .cell (singleTrack aux.tm aux.tm.k₀
          ⟨aux.inputAlphabet.invFun (x.reverse[i]'(by simpa using hix)),
            mem_reachSet_k0 aux.tm _⟩)) ∧
  (∀ i : ℕ, done ≤ i → T.nth ((i + 1 : ℕ) : ℤ) = .blank)

lemma p1_toRight_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (x : List A) :
    ∀ (k : ℕ), k ≤ x.length →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p1_toRight, shiftZ (Tape.mk₁ (x.map Sym.inp)) (k : ℤ)⟩
        (some ⟨.p1_startFetch,
          (shiftZ (Tape.mk₁ (x.map Sym.inp)) (x.length : ℤ)).write .wall⟩)
        (x.length - k + 1)) := by
  intro k hk
  induction hd : x.length - k generalizing k with
  | zero =>
      have hkeq : k = x.length := by omega
      subst hkeq
      apply evals_one
      have hhead : (shiftZ (Tape.mk₁ (x.map (Sym.inp : A → Sym A B aux.tm))) (x.length : ℤ)).head =
          .blank := by
        rw [shiftZ_head, mk₁_nth_nat, List.getI_eq_default _ (by simp)]
        rfl
      rw [step_write (by rw [hhead]; rfl)]
  | succ d ih =>
      have hklt : k < x.length := by omega
      have hhead : (shiftZ (Tape.mk₁ (x.map (Sym.inp : A → Sym A B aux.tm))) (k : ℤ)).head =
          .inp (x[k]'hklt) := by
        rw [shiftZ_head, mk₁_nth_nat, List.getI_eq_getElem _ (by simp; omega), List.getElem_map]
      have s1 : (simMachine aux).step
          ⟨.p1_toRight, shiftZ (Tape.mk₁ (x.map Sym.inp)) (k : ℤ)⟩ =
          some ⟨.p1_toRight, shiftZ (Tape.mk₁ (x.map Sym.inp)) ((k + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move (by rw [hhead]; rfl), shiftZ_move_right]
        exact cfg_shiftZ_eq _ _ (by omega)
      exact evals_step s1 (ih (k + 1) (by omega) (by omega))

lemma p1_seekL_marks {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (done : ℕ)
    (hmarks : ∀ j : ℕ, j < done → T.nth (-(j + 1 : ℕ)) = .mark) :
    ∀ (k : ℕ), k ≤ done →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p1_seekL, shiftZ T (-(k + 1 : ℕ))⟩
        (some ⟨.p1_seekL, shiftZ T (-(done + 1 : ℕ))⟩)
        (done - k)) := by
  intro k hk
  induction hd : done - k generalizing k with
  | zero =>
      have hkeq : k = done := by omega
      subst hkeq
      exact evals_zero _
  | succ d ih =>
      have hklt : k < done := by omega
      have hhead : (shiftZ T (-(k + 1 : ℕ))).head = .mark := by
        rw [shiftZ_head]; exact hmarks k hklt
      have s1 : (simMachine aux).step ⟨.p1_seekL, shiftZ T (-(k + 1 : ℕ))⟩ =
          some ⟨.p1_seekL, shiftZ T (-((k + 1) + 1 : ℕ))⟩ := by
        rw [step_move (by rw [hhead]; rfl), shiftZ_move_left]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (k + 1) (by omega) (by omega))

lemma p1_carryR_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (a : A) (z₀ : ℤ) :
    ∀ (m : ℕ),
      (∀ t : ℕ, t < m → T.nth (z₀ + t) ≠ .blank) →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p1_carryR a, shiftZ T z₀⟩
        (some ⟨.p1_carryR a, shiftZ T (z₀ + m)⟩) m) := by
  intro m
  induction m generalizing z₀ with
  | zero =>
      intro _
      simp only [Nat.cast_zero, add_zero]
      exact evals_zero _
  | succ m ih =>
      intro hne
      have h0 : (shiftZ T z₀).head ≠ .blank := by
        rw [shiftZ_head]
        simpa using hne 0 (Nat.zero_lt_succ m)
      have hstep_eq : simDelta aux (.p1_carryR a) (shiftZ T z₀).head =
          some (.p1_carryR a, .move .right) := by
        cases h : (shiftZ T z₀).head with
        | blank => exact absurd h h0
        | inp _ => rfl
        | out _ => rfl
        | wall => rfl
        | outWall => rfl
        | mark => rfl
        | cell _ => rfl
      have s1 : (simMachine aux).step ⟨.p1_carryR a, shiftZ T z₀⟩ =
          some ⟨.p1_carryR a, shiftZ T (z₀ + 1)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
      have hrest := ih (z₀ + 1) (fun t ht => by
        have := hne (t + 1) (by omega)
        rw [show z₀ + 1 + (t : ℤ) = z₀ + ((t + 1 : ℕ) : ℤ) by omega]
        exact this)
      rw [show z₀ + 1 + (m : ℤ) = z₀ + ((m + 1 : ℕ) : ℤ) by omega] at hrest
      exact evals_step s1 hrest

lemma p1_backToWall_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) :
    ∀ (k : ℕ),
      (∀ i : ℕ, i < k → T.nth ((i + 1 : ℕ) : ℤ) ≠ .wall) →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p1_backToWall, shiftZ T (k : ℤ)⟩
        (some ⟨.p1_backToWall, shiftZ T 0⟩) k) := by
  intro k
  induction k with
  | zero => intro _; exact evals_zero _
  | succ k ih =>
      intro hne
      have h0 : (shiftZ T ((k + 1 : ℕ) : ℤ)).head ≠ .wall := by
        rw [shiftZ_head]; exact hne k (Nat.lt_succ_self k)
      have hstep_eq : simDelta aux .p1_backToWall (shiftZ T ((k + 1 : ℕ) : ℤ)).head =
          some (.p1_backToWall, .move .left) := by
        cases h : (shiftZ T ((k + 1 : ℕ) : ℤ)).head with
        | wall => exact absurd h h0
        | blank => rfl
        | inp _ => rfl
        | out _ => rfl
        | outWall => rfl
        | mark => rfl
        | cell _ => rfl
      have s1 : (simMachine aux).step ⟨.p1_backToWall, shiftZ T ((k + 1 : ℕ) : ℤ)⟩ =
          some ⟨.p1_backToWall, shiftZ T (k : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_left]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih fun i hi => hne i (by omega))

lemma p1_doneL_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) :
    ∀ (k : ℕ),
      (∀ j : ℕ, j < k → T.nth (-(j + 1 : ℕ)) ≠ .wall) →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p1_doneL, shiftZ T (-(k : ℤ))⟩
        (some ⟨.p1_doneL, shiftZ T 0⟩) k) := by
  intro k
  induction k with
  | zero => intro _; simp; exact evals_zero _
  | succ k ih =>
      intro hne
      have h0 : (shiftZ T (-((k + 1 : ℕ) : ℤ))).head ≠ .wall := by
        rw [shiftZ_head]
        exact hne k (Nat.lt_succ_self k)
      have hstep_eq : simDelta aux .p1_doneL (shiftZ T (-((k + 1 : ℕ) : ℤ))).head =
          some (.p1_doneL, .move .right) := by
        cases h : (shiftZ T (-((k + 1 : ℕ) : ℤ))).head with
        | wall => exact absurd h h0
        | blank => rfl
        | inp _ => rfl
        | out _ => rfl
        | outWall => rfl
        | mark => rfl
        | cell _ => rfl
      have s1 : (simMachine aux).step ⟨.p1_doneL, shiftZ T (-((k + 1 : ℕ) : ℤ))⟩ =
          some ⟨.p1_doneL, shiftZ T (-(k : ℤ))⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih fun j hj => hne j (by omega))

lemma p1_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B) (x : List A) :
    ∀ (done : ℕ) (T : Tape (Sym A B aux.tm)),
      done ≤ x.length →
      Phase1Inv aux x T done →
      ∃ T_f : Tape (Sym A B aux.tm),
        Represents T_f (initReachStk aux x) ∧
        Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
          ⟨.p1_seekL, shiftZ T (-1)⟩
          (some ⟨.exec ⟨aux.tm.m aux.tm.main, mem_allStmts_m aux.tm aux.tm.main⟩
            aux.tm.initialState, T_f⟩)
          ((x.length - done) * (4 * x.length + 6) + 2 * x.length + 2)) := by
  intro done T hle hinv
  induction hd : x.length - done generalizing done T with
  | zero =>
      have hdeq : done = x.length := by omega
      subst hdeq
      rcases hinv with ⟨h0, hmarks, _, hblL, hcells, hblR⟩
      have hseek := p1_seekL_marks aux T x.length hmarks 0 (Nat.zero_le _)
      have hheadB : (shiftZ T (-(x.length + 1 : ℕ))).head = .blank := by
        rw [shiftZ_head]; exact hblL x.length le_rfl
      have s_done : (simMachine aux).step ⟨.p1_seekL, shiftZ T (-(x.length + 1 : ℕ))⟩ =
          some ⟨.p1_doneL, shiftZ T (-(x.length : ℤ))⟩ := by
        rw [step_move (by rw [hheadB]; rfl), shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      have hwalk := p1_doneL_walk aux T x.length (fun j hj => by
        rw [hmarks j hj]; intro h; cases h)
      have s_wall : (simMachine aux).step ⟨.p1_doneL, shiftZ T 0⟩ =
          some ⟨.exec ⟨aux.tm.m aux.tm.main, mem_allStmts_m aux.tm aux.tm.main⟩
            aux.tm.initialState, T⟩ := by
        have hw : (shiftZ T 0).head = .wall := by rw [shiftZ_head]; exact h0
        rw [step_write (by rw [hw]; rfl), shiftZ_zero]
        congr 2; rw [← h0]; exact Tape.write_self T
      have hall := evals_trans hseek (evals_step s_done (evals_trans hwalk (evals_one s_wall)))
      refine ⟨T, ?_, evals_mono hall (by simp; omega)⟩
      refine ⟨h0, ?_, ?_⟩
      · intro i
        by_cases hi : i < x.length
        · rcases hcells i hi with ⟨_, hci⟩
          rw [hci]; trivial
        · rw [hblR i (Nat.le_of_not_lt hi)]; trivial
      · intro k i
        let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
        by_cases hi : i < x.length
        · rcases hcells i hi with ⟨hix, hci⟩
          rw [hci]
          by_cases hk : k = aux.tm.k₀
          · subst hk
            rw [readTrack_singleTrack_self]
            simp only [initReachStk, ↓reduceDIte]
            rw [← List.map_reverse]
            rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_map]
          · rw [readTrack_singleTrack_ne hk]
            simp [hk, initReachStk]
        · rw [hblR i (Nat.le_of_not_lt hi)]
          simp only [readTrack, initReachStk]
          by_cases hk : k = aux.tm.k₀
          · subst hk
            simp only [↓reduceDIte]
            symm
            rw [List.getElem?_eq_none (by simp; omega)]
          · simp [hk]
  | succ d ih =>
      have hdlt : done < x.length := by omega
      rcases hinv with ⟨h0, hmarks, hinps, hblL, hcells, hblR⟩
      have hseek := p1_seekL_marks aux T done hmarks 0 (Nat.zero_le _)
      let a : A := x.reverse[done]'(by simpa using hdlt)
      have hheadA : (shiftZ T (-(done + 1 : ℕ))).head = .inp a := by
        rw [shiftZ_head]; exact hinps done hdlt le_rfl
      let T1 := tapeWriteZ T (-(done + 1 : ℕ)) .mark
      have s_mark : (simMachine aux).step ⟨.p1_seekL, shiftZ T (-(done + 1 : ℕ))⟩ =
          some ⟨.p1_carryR a, shiftZ T1 (-(done + 1 : ℕ))⟩ := by
        rw [step_write (by rw [hheadA]; rfl), shiftZ_write]
      have hcarry := p1_carryR_walk aux T1 a (-(done + 1 : ℕ)) (2 * done + 2) (fun t ht => by
        rw [tapeWriteZ_nth]
        by_cases hteq : (-(done + 1 : ℕ) : ℤ) + t = -(done + 1 : ℕ)
        · rw [ite_eq_left hteq]; intro h; cases h
        · rw [ite_eq_right hteq]
          by_cases hneg : (-(done + 1 : ℕ) : ℤ) + t < 0
          · have hidx : ∃ j : ℕ, j < done ∧ (-(done + 1 : ℕ) : ℤ) + t = -(j + 1 : ℕ) :=
              ⟨done - t, by omega, by omega⟩
            rcases hidx with ⟨j, hj, hjeq⟩
            rw [hjeq, hmarks j hj]; intro h; cases h
          · by_cases hzero : (-(done + 1 : ℕ) : ℤ) + t = 0
            · rw [hzero, h0]; intro h; cases h
            · have hidx : ∃ i : ℕ, i < done ∧ (-(done + 1 : ℕ) : ℤ) + t = ((i + 1 : ℕ) : ℤ) :=
                ⟨t - (done + 2), by omega, by omega⟩
              rcases hidx with ⟨i, hi, hieq⟩
              rcases hcells i hi with ⟨_, hci⟩
              rw [hieq, hci]; intro h; cases h)
      have hpos_eq : (-(done + 1 : ℕ) : ℤ) + ((2 * done + 2 : ℕ) : ℤ) = ((done + 1 : ℕ) : ℤ) := by
        omega
      rw [hpos_eq] at hcarry
      have hheadBl : (shiftZ T1 ((done + 1 : ℕ) : ℤ)).head = .blank := by
        rw [shiftZ_head, tapeWriteZ_nth, ite_eq_right (by omega)]
        exact hblR done le_rfl
      let symA : Reach aux.tm aux.tm.k₀ :=
        ⟨aux.inputAlphabet.invFun a, mem_reachSet_k0 aux.tm _⟩
      let T2 := tapeWriteZ T1 ((done + 1 : ℕ) : ℤ) (.cell (singleTrack aux.tm aux.tm.k₀ symA))
      have s_cell : (simMachine aux).step ⟨.p1_carryR a, shiftZ T1 ((done + 1 : ℕ) : ℤ)⟩ =
          some ⟨.p1_backToWall, shiftZ T2 ((done + 1 : ℕ) : ℤ)⟩ := by
        rw [step_write (by rw [hheadBl]; rfl), shiftZ_write]
      have hback := p1_backToWall_walk aux T2 (done + 1) (fun i hi => by
        rw [tapeWriteZ_nth]
        by_cases hieq : ((i + 1 : ℕ) : ℤ) = ((done + 1 : ℕ) : ℤ)
        · rw [ite_eq_left hieq]; intro h; cases h
        · rw [ite_eq_right hieq, tapeWriteZ_nth, ite_eq_right (by omega)]
          rcases hcells i (by omega) with ⟨_, hci⟩
          rw [hci]; intro h; cases h)
      have hheadW2 : (shiftZ T2 0).head = .wall := by
        rw [shiftZ_head, tapeWriteZ_nth, ite_eq_right (by omega),
            tapeWriteZ_nth, ite_eq_right (by omega)]
        exact h0
      have s_left : (simMachine aux).step ⟨.p1_backToWall, shiftZ T2 0⟩ =
          some ⟨.p1_seekL, shiftZ T2 (-1)⟩ := by
        rw [step_move (by rw [hheadW2]; rfl), shiftZ_move_left]
        congr 2
      have hinv2 : Phase1Inv aux x T2 (done + 1) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact h0
        · intro j hj
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth]
          by_cases hje : (-(j + 1 : ℕ) : ℤ) = -(done + 1 : ℕ)
          · rw [ite_eq_left hje]
          · rw [ite_eq_right hje]; exact hmarks j (by omega)
        · intro j hj hge
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hinps j hj (by omega)
        · intro j hge
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hblL j hge
        · intro i hi
          rw [tapeWriteZ_nth]
          by_cases hie : ((i + 1 : ℕ) : ℤ) = ((done + 1 : ℕ) : ℤ)
          · have hid : i = done := by omega
            subst hid
            refine ⟨hdlt, ?_⟩
            rw [ite_eq_left hie]
          · rw [ite_eq_right hie, tapeWriteZ_nth, ite_eq_right (by omega)]
            exact hcells i (by omega)
        · intro i hge
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hblR i (by omega)
      obtain ⟨T_f, hrep, hrest⟩ := ih (done + 1) T2 (by omega) hinv2 (by omega)
      have hiter := evals_trans hseek
        (evals_step s_mark (evals_trans hcarry (evals_step s_cell
          (evals_trans hback (evals_step s_left hrest)))))
      refine ⟨T_f, hrep, evals_mono hiter ?_⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega

lemma phase1_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B) (x : List A) :
    ∃ T : Tape (Sym A B aux.tm),
      Represents T (initReachStk aux x) ∧
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ((simMachine aux).init x)
        (some ⟨.exec ⟨aux.tm.m aux.tm.main, mem_allStmts_m aux.tm aux.tm.main⟩
          aux.tm.initialState, T⟩)
        (4 * x.length * x.length + 9 * x.length + 4)) := by
  have hinit : (simMachine aux).init x =
      ⟨.p1_toRight, shiftZ (Tape.mk₁ (x.map Sym.inp)) 0⟩ := rfl
  rw [hinit]
  have h1 := p1_toRight_loop aux x 0 (Nat.zero_le _)
  let Tw : Tape (Sym A B aux.tm) :=
    (shiftZ (Tape.mk₁ (x.map (Sym.inp : A → Sym A B aux.tm))) (x.length : ℤ)).write .wall
  have s2 : (simMachine aux).step ⟨.p1_startFetch, Tw⟩ =
      some ⟨.p1_seekL, shiftZ Tw (-1)⟩ := by
    rw [step_move rfl, show Tw.move .left = shiftZ Tw (-1) by
      rw [← shiftZ_zero Tw, shiftZ_move_left]; rfl]
  have hinv0 : Phase1Inv aux x Tw 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Tape.write_nth]; simp
    · intro j hj; omega
    · intro j hj _
      rw [Tape.write_nth, ite_eq_right (by omega), shiftZ_nth]
      have hidx : (-(j + 1 : ℕ) : ℤ) + (x.length : ℤ) = ((x.length - 1 - j : ℕ) : ℤ) := by omega
      rw [hidx, mk₁_nth_nat, List.getI_eq_getElem _ (by simp; omega), List.getElem_map]
      congr 1
      rw [List.getElem_reverse]
    · intro j hge
      rw [Tape.write_nth, ite_eq_right (by omega), shiftZ_nth]
      have hidx : (-(j + 1 : ℕ) : ℤ) + (x.length : ℤ) = -((j - x.length) + 1 : ℕ) := by omega
      rw [hidx, mk₁_nth_neg]; rfl
    · intro i hi; omega
    · intro i _
      rw [Tape.write_nth, ite_eq_right (by omega), shiftZ_nth]
      have hidx : ((i + 1 : ℕ) : ℤ) + (x.length : ℤ) = ((x.length + i + 1 : ℕ) : ℤ) := by omega
      rw [hidx, mk₁_nth_nat, List.getI_eq_default _ (by simp; omega)]; rfl
  obtain ⟨T_f, hrep, hloop⟩ := p1_loop aux x 0 Tw (Nat.zero_le _) hinv0
  have hall := evals_trans h1 (evals_step s2 hloop)
  refine ⟨T_f, hrep, evals_mono hall ?_⟩
  simp only [Nat.sub_zero]
  nlinarith

/-! ## Phase 2 Proof: Simulating TM2 Statements on Parallel Tracks -/

lemma rewind_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (v : aux.tm.σ) (T : Tape (Sym A B aux.tm))
    (hw : T.head = .wall) (htr : ∀ i : ℕ, isTrackOrBlank (T.nth ((i + 1 : ℕ) : ℤ))) :
    ∀ (k : ℕ),
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.rewind q v, shiftZ T (k : ℤ)⟩
        (some ⟨.exec q v, T⟩) (k + 1)) := by
  intro k
  induction k with
  | zero =>
      apply evals_one
      rw [Nat.cast_zero, shiftZ_zero]
      rw [step_write (by rw [hw]; rfl)]
      congr 2; rw [← hw]; exact Tape.write_self T
  | succ k ih =>
      have hnotW : (shiftZ T ((k + 1 : ℕ) : ℤ)).head ≠ .wall := by
        rw [shiftZ_head]
        have h := htr k
        cases hcell : T.nth ((k + 1 : ℕ) : ℤ) <;> rw [hcell] at h
        · intro hc; cases hc
        · cases h
        · cases h
        · cases h
        · cases h
        · cases h
        · intro hc; cases hc
      have hstep_eq : simDelta aux (.rewind q v) (shiftZ T ((k + 1 : ℕ) : ℤ)).head =
          some (.rewind q v, .move .left) := by
        cases h : (shiftZ T ((k + 1 : ℕ) : ℤ)).head with
        | wall => exact absurd h hnotW
        | blank => rfl
        | inp _ => rfl
        | out _ => rfl
        | outWall => rfl
        | mark => rfl
        | cell _ => rfl
      have s1 : (simMachine aux).step ⟨.rewind q v, shiftZ T ((k + 1 : ℕ) : ℤ)⟩ =
          some ⟨.rewind q v, shiftZ T (k : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_left]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 ih

lemma push_seek_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → aux.tm.Γ k)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .push k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    ∀ (i : ℕ), i ≤ (S k).length →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.pushSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩
        (some ⟨.pushSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩)
        ((S k).length - i)) := by
  intro i hi
  induction hd : (S k).length - i generalizing i with
  | zero =>
      have hieq : i = (S k).length := by omega
      subst hieq; exact evals_zero _
  | succ d ih =>
      have hilt : i < (S k).length := by omega
      have hsome : (readTrack (shiftZ T ((i + 1 : ℕ) : ℤ)).head k).isSome = true := by
        rw [shiftZ_head, hrep.2.2 k i, List.getElem?_eq_getElem (by simp; omega)]
        rfl
      have hstep_eq : simDelta aux (.pushSeek q v) (shiftZ T ((i + 1 : ℕ) : ℤ)).head =
          some (.pushSeek q v, .move .right) := by
        simp only [simDelta]
        split
        · rename_i k1 f1 q1 heq
          have heq' := hq.symm.trans heq
          cases heq'
          rw [ite_eq_left hsome]
        · rename_i hne
          exact absurd hq (hne k f q')
      have s1 : (simMachine aux).step ⟨.pushSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩ =
          some ⟨.pushSeek q v, shiftZ T (((i + 1) + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (i + 1) (by omega) (by omega))

lemma push_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → aux.tm.Γ k)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .push k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    letI : DecidableEq aux.tm.K := aux.tm.kDecidableEq
    let sym : Reach aux.tm k := ⟨f v, mem_reachSet_push aux.tm (hq ▸ q.property) v⟩
    let qNext : SubStmt aux.tm := ⟨q', sub_push aux.tm (hq ▸ q.property)⟩
    ∃ T' : Tape (Sym A B aux.tm),
      Represents T' (Function.update S k (sym :: S k)) ∧
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.exec q v, T⟩ (some ⟨.exec qNext v, T'⟩) (2 * (S k).length + 4)) := by
  let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  intro sym qNext
  have s0 : (simMachine aux).step ⟨.exec q v, T⟩ =
      some ⟨.pushSeek q v, shiftZ T ((0 + 1 : ℕ) : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.exec q v) T.head = some (.pushSeek q v, .move .right) := by
      simp only [simDelta]
      split
      · rfl
      all_goals (rename_i h; rw [hq] at h; cases h)
    rw [step_move hstep_eq, show T.move .right = shiftZ T ((0 + 1 : ℕ) : ℤ) by
      rw [← shiftZ_zero T, shiftZ_move_right]; rfl]
  have hseek := push_seek_loop aux q k f q' hq v T S hrep 0 (Nat.zero_le _)
  let gEnd := T.nth (((S k).length + 1 : ℕ) : ℤ)
  have hnone : (readTrack gEnd k).isSome = false := by
    change (readTrack (T.nth (((S k).length + 1 : ℕ) : ℤ)) k).isSome = false
    rw [hrep.2.2 k (S k).length, List.getElem?_eq_none (by simp)]
    rfl
  let T' := tapeWriteZ T (((S k).length + 1 : ℕ) : ℤ) (setTrack gEnd k (some sym))
  have s_wr : (simMachine aux).step ⟨.pushSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩ =
      some ⟨.rewind qNext v, shiftZ T' (((S k).length + 1 : ℕ) : ℤ)⟩ := by
    have hhead : (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head = gEnd := shiftZ_head _ _
    have hstep_eq : simDelta aux (.pushSeek q v) (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head =
        some (.rewind qNext v, .write (setTrack gEnd k (some sym))) := by
      rw [hhead]
      simp only [simDelta]
      split
      · rename_i k1 f1 q1 heq
        have heq' := hq.symm.trans heq
        cases heq'
        rw [ite_eq_right (by rw [hnone]; decide)]
      · rename_i hne
        exact absurd hq (hne k f q')
    rw [step_write hstep_eq, shiftZ_write]
  have hrep' : Represents T' (Function.update S k (sym :: S k)) := by
    refine ⟨?_, ?_, ?_⟩
    · change T'.nth 0 = .wall
      rw [tapeWriteZ_nth, ite_eq_right (by omega)]
      exact hrep.1
    · intro i
      rw [tapeWriteZ_nth]
      by_cases hi : ((i + 1 : ℕ) : ℤ) = (((S k).length + 1 : ℕ) : ℤ)
      · rw [ite_eq_left hi]; exact isTrackOrBlank_setTrack _ _ _
      · rw [ite_eq_right hi]; exact hrep.2.1 i
    · intro j i
      rw [tapeWriteZ_nth]
      by_cases hi : ((i + 1 : ℕ) : ℤ) = (((S k).length + 1 : ℕ) : ℤ)
      · have hieq : i = (S k).length := by omega
        subst hieq
        rw [ite_eq_left hi]
        by_cases hj : j = k
        · subst hj
          rw [readTrack_setTrack_self (hrep.2.1 (S j).length), Function.update_self,
            List.reverse_cons, List.getElem?_append_right (by simp)]
          simp
        · rw [readTrack_setTrack_ne (hrep.2.1 (S k).length) hj, Function.update_of_ne hj]
          exact hrep.2.2 j (S k).length
      · have hine : i ≠ (S k).length := by omega
        rw [ite_eq_right hi, hrep.2.2 j i]
        by_cases hj : j = k
        · subst hj
          rw [Function.update_self, List.reverse_cons]
          by_cases hlt : i < (S j).length
          · rw [List.getElem?_append_left (by simp; omega)]
          · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        · rw [Function.update_of_ne hj]
  have hrew := rewind_loop aux qNext v T' hrep'.1 hrep'.2.1 ((S k).length + 1)
  have hall := evals_step s0 (evals_trans hseek (evals_step s_wr hrew))
  exact ⟨T', hrep', evals_mono hall (by simp; omega)⟩

lemma peek_seek_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → Option (aux.tm.Γ k) → aux.tm.σ)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .peek k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    ∀ (i : ℕ), i ≤ (S k).length →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.peekSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩
        (some ⟨.peekSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩)
        ((S k).length - i)) := by
  intro i hi
  induction hd : (S k).length - i generalizing i with
  | zero =>
      have hieq : i = (S k).length := by omega
      subst hieq; exact evals_zero _
  | succ d ih =>
      have hilt : i < (S k).length := by omega
      have hsome : (readTrack (shiftZ T ((i + 1 : ℕ) : ℤ)).head k).isSome = true := by
        rw [shiftZ_head, hrep.2.2 k i, List.getElem?_eq_getElem (by simp; omega)]
        rfl
      have hstep_eq : simDelta aux (.peekSeek q v) (shiftZ T ((i + 1 : ℕ) : ℤ)).head =
          some (.peekSeek q v, .move .right) := by
        simp only [simDelta]
        split
        · rename_i k1 f1 q1 heq
          have heq' := hq.symm.trans heq
          cases heq'
          rw [ite_eq_left hsome]
        · rename_i hne
          exact absurd hq (hne k f q')
      have s1 : (simMachine aux).step ⟨.peekSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩ =
          some ⟨.peekSeek q v, shiftZ T (((i + 1) + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (i + 1) (by omega) (by omega))

lemma peek_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → Option (aux.tm.Γ k) → aux.tm.σ)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .peek k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    let qNext : SubStmt aux.tm := ⟨q', sub_peek aux.tm (hq ▸ q.property)⟩
    Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
      ⟨.exec q v, T⟩ (some ⟨.exec qNext (f v (liftStk S k).head?), T⟩)
      (2 * (S k).length + 4)) := by
  intro qNext
  have s0 : (simMachine aux).step ⟨.exec q v, T⟩ =
      some ⟨.peekSeek q v, shiftZ T ((0 + 1 : ℕ) : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.exec q v) T.head = some (.peekSeek q v, .move .right) := by
      simp only [simDelta]
      split
      all_goals first | rfl | (rename_i h; rw [hq] at h; cases h)
    rw [step_move hstep_eq, show T.move .right = shiftZ T ((0 + 1 : ℕ) : ℤ) by
      rw [← shiftZ_zero T, shiftZ_move_right]; rfl]
  have hseek := peek_seek_loop aux q k f q' hq v T S hrep 0 (Nat.zero_le _)
  have hnone : (readTrack (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head k).isSome = false := by
    rw [shiftZ_head, hrep.2.2 k (S k).length, List.getElem?_eq_none (by simp)]
    rfl
  have s_left : (simMachine aux).step ⟨.peekSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩ =
      some ⟨.peekRead q v, shiftZ T ((S k).length : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.peekSeek q v) (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head =
        some (.peekRead q v, .move .left) := by
      simp only [simDelta]
      split
      · rename_i k1 f1 q1 heq
        have heq' := hq.symm.trans heq
        cases heq'
        rw [ite_eq_right (by rw [hnone]; decide)]
      · rename_i hne
        exact absurd hq (hne k f q')
    rw [step_move hstep_eq, shiftZ_move_left]
    exact cfg_shiftZ_eq _ T (by omega)
  cases hSk : S k with
  | nil =>
      have hlen0 : (S k).length = 0 := by rw [hSk]; rfl
      have hhead0 : (liftStk S k).head? = none := by simp [liftStk, hSk]
      rw [hhead0]
      have s_rd : (simMachine aux).step ⟨.peekRead q v, shiftZ T ((S k).length : ℤ)⟩ =
          some ⟨.exec qNext (f v none), T⟩ := by
        rw [hlen0, Nat.cast_zero, shiftZ_zero]
        have hstep_eq : simDelta aux (.peekRead q v) T.head =
            some (.exec qNext (f v none), .write .wall) := by
          rw [hrep.1]
          simp only [simDelta]
          split
          · rename_i k1 f1 q1 heq
            have heq' := hq.symm.trans heq
            cases heq'; rfl
          · rename_i hne
            exact absurd hq (hne k f q')
        rw [step_write hstep_eq]
        congr 2; rw [← hrep.1]; exact Tape.write_self T
      have hall := evals_step s0 (evals_trans hseek (evals_step s_left (evals_one s_rd)))
      exact evals_mono hall (by simp; omega)
  | cons top rest =>
      have hlen : (S k).length = rest.length + 1 := by rw [hSk]; rfl
      have hhead_top : (liftStk S k).head? = some top.val := by simp [liftStk, hSk]
      rw [hhead_top]
      let gTop := T.nth ((rest.length + 1 : ℕ) : ℤ)
      have hgTop_notW : gTop ≠ .wall := by
        have h := hrep.2.1 rest.length
        cases hc : gTop <;> simp only [gTop] at hc <;> rw [hc] at h
        · intro e; cases e
        · cases h
        · cases h
        · cases h
        · cases h
        · cases h
        · intro e; cases e
      have hread_top : readTrack gTop k = some top := by
        change readTrack (T.nth ((rest.length + 1 : ℕ) : ℤ)) k = some top
        rw [hrep.2.2 k rest.length, hSk, List.reverse_cons]
        rw [List.getElem?_append_right (by simp)]
        simp
      have s_rd : (simMachine aux).step ⟨.peekRead q v, shiftZ T ((S k).length : ℤ)⟩ =
          some ⟨.rewind qNext (f v (some top.val)), shiftZ T ((S k).length : ℤ)⟩ := by
        rw [hlen]
        have hheadG : (shiftZ T ((rest.length + 1 : ℕ) : ℤ)).head = gTop := shiftZ_head _ _
        have hstep_eq : simDelta aux (.peekRead q v) (shiftZ T ((rest.length + 1 : ℕ) : ℤ)).head =
            some (.rewind qNext (f v (some top.val)), .write gTop) := by
          rw [hheadG]
          simp only [simDelta]
          split
          · rename_i k1 f1 q1 heq
            have heq' := hq.symm.trans heq
            cases heq'
            cases hgc : gTop with
            | wall => exact absurd hgc hgTop_notW
            | blank => rw [← hgc, hread_top]; rfl
            | inp _ => rw [← hgc, hread_top]; rfl
            | out _ => rw [← hgc, hread_top]; rfl
            | outWall => rw [← hgc, hread_top]; rfl
            | mark => rw [← hgc, hread_top]; rfl
            | cell _ => rw [← hgc, hread_top]; rfl
          · rename_i hne
            exact absurd hq (hne k f q')
        rw [step_write hstep_eq]
        congr 2; rw [← hheadG]; exact Tape.write_self _
      have hrew := rewind_loop aux qNext (f v (some top.val)) T hrep.1 hrep.2.1 (S k).length
      have hall := evals_step s0 (evals_trans hseek (evals_step s_left (evals_step s_rd hrew)))
      exact evals_mono hall (by simp; omega)

lemma pop_seek_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → Option (aux.tm.Γ k) → aux.tm.σ)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .pop k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    ∀ (i : ℕ), i ≤ (S k).length →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.popSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩
        (some ⟨.popSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩)
        ((S k).length - i)) := by
  intro i hi
  induction hd : (S k).length - i generalizing i with
  | zero =>
      have hieq : i = (S k).length := by omega
      subst hieq; exact evals_zero _
  | succ d ih =>
      have hilt : i < (S k).length := by omega
      have hsome : (readTrack (shiftZ T ((i + 1 : ℕ) : ℤ)).head k).isSome = true := by
        rw [shiftZ_head, hrep.2.2 k i, List.getElem?_eq_getElem (by simp; omega)]
        rfl
      have hstep_eq : simDelta aux (.popSeek q v) (shiftZ T ((i + 1 : ℕ) : ℤ)).head =
          some (.popSeek q v, .move .right) := by
        simp only [simDelta]
        split
        · rename_i k1 f1 q1 heq
          have heq' := hq.symm.trans heq
          cases heq'
          rw [ite_eq_left hsome]
        · rename_i hne
          exact absurd hq (hne k f q')
      have s1 : (simMachine aux).step ⟨.popSeek q v, shiftZ T ((i + 1 : ℕ) : ℤ)⟩ =
          some ⟨.popSeek q v, shiftZ T (((i + 1) + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (i + 1) (by omega) (by omega))

lemma pop_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q : SubStmt aux.tm) (k : aux.tm.K) (f : aux.tm.σ → Option (aux.tm.Γ k) → aux.tm.σ)
    (q' : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : q.val = .pop k f q')
    (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ j, List (Reach aux.tm j))
    (hrep : Represents T S) :
    letI : DecidableEq aux.tm.K := aux.tm.kDecidableEq
    let qNext : SubStmt aux.tm := ⟨q', sub_pop aux.tm (hq ▸ q.property)⟩
    ∃ T' : Tape (Sym A B aux.tm),
      Represents T' (Function.update S k (S k).tail) ∧
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.exec q v, T⟩ (some ⟨.exec qNext (f v (liftStk S k).head?), T'⟩)
        (2 * (S k).length + 4)) := by
  let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  intro qNext
  have s0 : (simMachine aux).step ⟨.exec q v, T⟩ =
      some ⟨.popSeek q v, shiftZ T ((0 + 1 : ℕ) : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.exec q v) T.head = some (.popSeek q v, .move .right) := by
      simp only [simDelta]
      split
      all_goals first | rfl | (rename_i h; rw [hq] at h; cases h)
    rw [step_move hstep_eq, show T.move .right = shiftZ T ((0 + 1 : ℕ) : ℤ) by
      rw [← shiftZ_zero T, shiftZ_move_right]; rfl]
  have hseek := pop_seek_loop aux q k f q' hq v T S hrep 0 (Nat.zero_le _)
  have hnone : (readTrack (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head k).isSome = false := by
    rw [shiftZ_head, hrep.2.2 k (S k).length, List.getElem?_eq_none (by simp)]
    rfl
  have s_left : (simMachine aux).step ⟨.popSeek q v, shiftZ T (((S k).length + 1 : ℕ) : ℤ)⟩ =
      some ⟨.popRead q v, shiftZ T ((S k).length : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.popSeek q v) (shiftZ T (((S k).length + 1 : ℕ) : ℤ)).head =
        some (.popRead q v, .move .left) := by
      simp only [simDelta]
      split
      · rename_i k1 f1 q1 heq
        have heq' := hq.symm.trans heq
        cases heq'
        rw [ite_eq_right (by rw [hnone]; decide)]
      · rename_i hne
        exact absurd hq (hne k f q')
    rw [step_move hstep_eq, shiftZ_move_left]
    exact cfg_shiftZ_eq _ T (by omega)
  cases hSk : S k with
  | nil =>
      have hlen0 : (S k).length = 0 := by rw [hSk]; rfl
      have hhead0 : (liftStk S k).head? = none := by simp [liftStk, hSk]
      rw [hhead0]
      have hupd : Function.update S k (S k).tail = S := by
        rw [Function.update_eq_self_iff, hSk]; rfl
      have s_rd : (simMachine aux).step ⟨.popRead q v, shiftZ T ((S k).length : ℤ)⟩ =
          some ⟨.exec qNext (f v none), T⟩ := by
        rw [hlen0, Nat.cast_zero, shiftZ_zero]
        have hstep_eq : simDelta aux (.popRead q v) T.head =
            some (.exec qNext (f v none), .write .wall) := by
          rw [hrep.1]
          simp only [simDelta]
          split
          · rename_i k1 f1 q1 heq
            have heq' := hq.symm.trans heq
            cases heq'; rfl
          · rename_i hne
            exact absurd hq (hne k f q')
        rw [step_write hstep_eq]
        congr 2; rw [← hrep.1]; exact Tape.write_self T
      have hall := evals_step s0 (evals_trans hseek (evals_step s_left (evals_one s_rd)))
      refine ⟨T, by rw [← hSk, hupd]; exact hrep, evals_mono hall (by simp; omega)⟩
  | cons top rest =>
      have hlen : (S k).length = rest.length + 1 := by rw [hSk]; rfl
      have hhead_top : (liftStk S k).head? = some top.val := by simp [liftStk, hSk]
      rw [hhead_top]
      let gTop := T.nth ((rest.length + 1 : ℕ) : ℤ)
      have hgTop_notW : gTop ≠ .wall := by
        have h := hrep.2.1 rest.length
        cases hc : gTop <;> simp only [gTop] at hc <;> rw [hc] at h
        · intro e; cases e
        · cases h
        · cases h
        · cases h
        · cases h
        · cases h
        · intro e; cases e
      have hread_top : readTrack gTop k = some top := by
        change readTrack (T.nth ((rest.length + 1 : ℕ) : ℤ)) k = some top
        rw [hrep.2.2 k rest.length, hSk, List.reverse_cons]
        rw [List.getElem?_append_right (by simp)]
        simp
      let T' := tapeWriteZ T ((rest.length + 1 : ℕ) : ℤ) (setTrack gTop k none)
      have s_rd : (simMachine aux).step ⟨.popRead q v, shiftZ T ((S k).length : ℤ)⟩ =
          some ⟨.rewind qNext (f v (some top.val)), shiftZ T' ((rest.length + 1 : ℕ) : ℤ)⟩ := by
        rw [hlen]
        have hheadG : (shiftZ T ((rest.length + 1 : ℕ) : ℤ)).head = gTop := shiftZ_head _ _
        have hstep_eq : simDelta aux (.popRead q v) (shiftZ T ((rest.length + 1 : ℕ) : ℤ)).head =
            some (.rewind qNext (f v (some top.val)), .write (setTrack gTop k none)) := by
          rw [hheadG]
          simp only [simDelta]
          split
          · rename_i k1 f1 q1 heq
            have heq' := hq.symm.trans heq
            cases heq'
            cases hgc : gTop with
            | wall => exact absurd hgc hgTop_notW
            | blank => rw [← hgc, hread_top]; rfl
            | inp _ => rw [← hgc, hread_top]; rfl
            | out _ => rw [← hgc, hread_top]; rfl
            | outWall => rw [← hgc, hread_top]; rfl
            | mark => rw [← hgc, hread_top]; rfl
            | cell _ => rw [← hgc, hread_top]; rfl
          · rename_i hne
            exact absurd hq (hne k f q')
        rw [step_write hstep_eq, shiftZ_write]
      have hrep' : Represents T' (Function.update S k (S k).tail) := by
        refine ⟨?_, ?_, ?_⟩
        · change T'.nth 0 = .wall
          rw [tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hrep.1
        · intro i
          rw [tapeWriteZ_nth]
          by_cases hi : ((i + 1 : ℕ) : ℤ) = ((rest.length + 1 : ℕ) : ℤ)
          · rw [ite_eq_left hi]; exact isTrackOrBlank_setTrack _ _ _
          · rw [ite_eq_right hi]; exact hrep.2.1 i
        · intro j i
          rw [tapeWriteZ_nth]
          by_cases hi : ((i + 1 : ℕ) : ℤ) = ((rest.length + 1 : ℕ) : ℤ)
          · have hieq : i = rest.length := by omega
            subst hieq
            rw [ite_eq_left hi]
            by_cases hj : j = k
            · subst hj
              rw [readTrack_setTrack_self (hrep.2.1 rest.length), Function.update_self, hSk]
              simp
            · rw [readTrack_setTrack_ne (hrep.2.1 rest.length) hj, Function.update_of_ne hj]
              exact hrep.2.2 j rest.length
          · have hine : i ≠ rest.length := by omega
            rw [ite_eq_right hi, hrep.2.2 j i]
            by_cases hj : j = k
            · subst hj
              rw [Function.update_self, hSk, List.tail_cons, List.reverse_cons]
              by_cases hlt : i < rest.length
              · rw [List.getElem?_append_left (by simp; omega)]
              · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
            · rw [Function.update_of_ne hj]
      have hrew := rewind_loop aux qNext (f v (some top.val)) T' hrep'.1 hrep'.2.1 (rest.length + 1)
      have hall := evals_step s0 (evals_trans hseek (evals_step s_left (evals_step s_rd hrew)))
      rw [hSk] at hrep'
      exact ⟨T', hrep', evals_mono hall (by simp [hlen]; omega)⟩

/-! ## Cost and Structural Simulation of TM2.stepAux -/

def stmtCost {tm : FinTM2} : TM2.Stmt tm.Γ tm.Λ tm.σ → ℕ
  | .push _ _ q => stmtCost q + 1
  | .peek _ _ q => stmtCost q + 1
  | .pop _ _ q => stmtCost q + 1
  | .load _ q => stmtCost q + 1
  | .branch _ q₁ q₂ => max (stmtCost q₁) (stmtCost q₂) + 1
  | .goto _ => 1
  | .halt => 1

noncomputable def maxStmtCost (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup (fun l => stmtCost (tm.m l)) + 1

lemma stmtCost_le_max (tm : FinTM2) (l : tm.Λ) : stmtCost (tm.m l) ≤ maxStmtCost tm := by
  have := Finset.le_sup (f := fun j => stmtCost (tm.m j)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
  unfold maxStmtCost; omega

lemma sim_stmt {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B) :
    ∀ (qRaw : TM2.Stmt aux.tm.Γ aux.tm.Λ aux.tm.σ) (hq : qRaw ∈ allStmts aux.tm)
      (v : aux.tm.σ) (T : Tape (Sym A B aux.tm)) (S : ∀ k, List (Reach aux.tm k)),
      Represents T S →
      letI : DecidableEq aux.tm.K := aux.tm.kDecidableEq
      let cfg := TM2.stepAux qRaw v (liftStk S)
      ∃ (S' : ∀ k, List (Reach aux.tm k)) (T' : Tape (Sym A B aux.tm))
        (qOut : SubStmt aux.tm),
        liftStk S' = cfg.stk ∧
        Represents T' S' ∧
        maxDepth S' ≤ maxDepth S + stmtCost qRaw ∧
        (match cfg.l with
          | some l' => qOut = ⟨aux.tm.m l', mem_allStmts_m aux.tm l'⟩
          | none => qOut.val = .halt) ∧
        Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
          ⟨.exec ⟨qRaw, hq⟩ v, T⟩ (some ⟨.exec qOut cfg.var, T'⟩)
          (stmtCost qRaw * (2 * (maxDepth S + stmtCost qRaw) + 4))) := by
  intro qRaw
  let _ : DecidableEq aux.tm.K := aux.tm.kDecidableEq
  induction qRaw with
  | push k f q' ih =>
      intro hq v T S hrep
      obtain ⟨T1, hrep1, hev1⟩ := push_run aux ⟨.push k f q', hq⟩ k f q' rfl v T S hrep
      let sym : Reach aux.tm k := ⟨f v, mem_reachSet_push aux.tm hq v⟩
      let S1 := Function.update S k (sym :: S k)
      have hlift1 : liftStk S1 = Function.update (liftStk S) k (f v :: liftStk S k) := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [S1, liftStk, sym]
        · simp [S1, liftStk, Function.update_of_ne hj]
      have hmd1 : maxDepth S1 ≤ maxDepth S + 1 := maxDepth_update_cons S k sym
      obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
        ih (sub_push aux.tm hq) v T1 S1 hrep1
      rw [hlift1] at hlift' hqOut hev2
      refine ⟨S', T', qOut, hlift', hrep', by simp only [stmtCost]; omega, hqOut, ?_⟩
      have hcomb := evals_trans hev1 hev2
      apply evals_mono hcomb
      have hlk : (S k).length ≤ maxDepth S := length_le_maxDepth S k
      simp only [stmtCost]
      nlinarith
  | peek k f q' ih =>
      intro hq v T S hrep
      have hev1 := peek_run aux ⟨.peek k f q', hq⟩ k f q' rfl v T S hrep
      obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
        ih (sub_peek aux.tm hq) (f v (liftStk S k).head?) T S hrep
      refine ⟨S', T', qOut, hlift', hrep', by simp only [stmtCost]; omega, hqOut, ?_⟩
      have hcomb := evals_trans hev1 hev2
      apply evals_mono hcomb
      have hlk : (S k).length ≤ maxDepth S := length_le_maxDepth S k
      simp only [stmtCost]
      nlinarith
  | pop k f q' ih =>
      intro hq v T S hrep
      obtain ⟨T1, hrep1, hev1⟩ := pop_run aux ⟨.pop k f q', hq⟩ k f q' rfl v T S hrep
      let S1 := Function.update S k (S k).tail
      have hlift1 : liftStk S1 = Function.update (liftStk S) k (liftStk S k).tail := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [S1, liftStk]
        · simp [S1, liftStk, Function.update_of_ne hj]
      have hmd1 : maxDepth S1 ≤ maxDepth S := maxDepth_update_tail S k
      obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
        ih (sub_pop aux.tm hq) (f v (liftStk S k).head?) T1 S1 hrep1
      rw [hlift1] at hlift' hqOut hev2
      refine ⟨S', T', qOut, hlift', hrep', by simp only [stmtCost]; omega, hqOut, ?_⟩
      have hcomb := evals_trans hev1 hev2
      apply evals_mono hcomb
      have hlk : (S k).length ≤ maxDepth S := length_le_maxDepth S k
      simp only [stmtCost]
      nlinarith
  | load a q' ih =>
      intro hq v T S hrep
      let qNext : SubStmt aux.tm := ⟨q', sub_load aux.tm hq⟩
      have s1 : (simMachine aux).step ⟨.exec ⟨.load a q', hq⟩ v, T⟩ =
          some ⟨.exec qNext (a v), T⟩ := by
        rw [step_write rfl]
        congr 2; rw [← hrep.1]; exact Tape.write_self T
      obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
        ih (sub_load aux.tm hq) (a v) T S hrep
      refine ⟨S', T', qOut, hlift', hrep', by simp only [stmtCost]; omega, hqOut, ?_⟩
      have hcomb := evals_step s1 hev2
      apply evals_mono hcomb
      simp only [stmtCost]
      nlinarith
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro hq v T S hrep
      cases hfv : f v with
      | false =>
          let qNext : SubStmt aux.tm := ⟨q₂, sub_branch_right aux.tm hq⟩
          have s1 : (simMachine aux).step ⟨.exec ⟨.branch f q₁ q₂, hq⟩ v, T⟩ =
              some ⟨.exec qNext v, T⟩ := by
            rw [step_write (by simp only [simDelta, hfv, Bool.false_eq_true, ↓reduceIte]; rfl)]
            congr 2; rw [← hrep.1]; exact Tape.write_self T
          obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
            ih₂ (sub_branch_right aux.tm hq) v T S hrep
          have hcfg : TM2.stepAux (TM2.Stmt.branch f q₁ q₂) v (liftStk S) =
              TM2.stepAux q₂ v (liftStk S) := by simp [TM2.stepAux, hfv]
          have hle : stmtCost q₂ ≤ max (stmtCost q₁) (stmtCost q₂) := le_max_right _ _
          refine ⟨S', T', qOut, by rw [hcfg]; exact hlift', hrep',
            by simp only [stmtCost]; omega, by rw [hcfg]; exact hqOut, ?_⟩
          rw [hcfg]
          have hcomb := evals_step s1 hev2
          apply evals_mono hcomb
          simp only [stmtCost]
          nlinarith
      | true =>
          let qNext : SubStmt aux.tm := ⟨q₁, sub_branch_left aux.tm hq⟩
          have s1 : (simMachine aux).step ⟨.exec ⟨.branch f q₁ q₂, hq⟩ v, T⟩ =
              some ⟨.exec qNext v, T⟩ := by
            rw [step_write (by simp only [simDelta, hfv, ↓reduceIte]; rfl)]
            congr 2; rw [← hrep.1]; exact Tape.write_self T
          obtain ⟨S', T', qOut, hlift', hrep', hmd', hqOut, hev2⟩ :=
            ih₁ (sub_branch_left aux.tm hq) v T S hrep
          have hcfg : TM2.stepAux (TM2.Stmt.branch f q₁ q₂) v (liftStk S) =
              TM2.stepAux q₁ v (liftStk S) := by simp [TM2.stepAux, hfv]
          have hle : stmtCost q₁ ≤ max (stmtCost q₁) (stmtCost q₂) := le_max_left _ _
          refine ⟨S', T', qOut, by rw [hcfg]; exact hlift', hrep',
            by simp only [stmtCost]; omega, by rw [hcfg]; exact hqOut, ?_⟩
          rw [hcfg]
          have hcomb := evals_step s1 hev2
          apply evals_mono hcomb
          simp only [stmtCost]
          nlinarith
  | goto f =>
      intro hq v T S hrep
      let qNext : SubStmt aux.tm := ⟨aux.tm.m (f v), mem_allStmts_m aux.tm (f v)⟩
      have s1 : (simMachine aux).step ⟨.exec ⟨.goto f, hq⟩ v, T⟩ =
          some ⟨.exec qNext v, T⟩ := by
        rw [step_write rfl]
        congr 2; rw [← hrep.1]; exact Tape.write_self T
      refine ⟨S, T, qNext, rfl, hrep, by simp [stmtCost], rfl, ?_⟩
      exact evals_mono (evals_one s1) (by simp [stmtCost])
  | halt =>
      intro hq v T S hrep
      refine ⟨S, T, ⟨.halt, hq⟩, rfl, hrep, by simp [stmtCost], rfl, ?_⟩
      exact evals_mono (evals_zero _) (Nat.zero_le _)

lemma sim_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B) :
    ∀ (n : ℕ) (l : aux.tm.Λ) (v : aux.tm.σ)
      (S : ∀ k, List (Reach aux.tm k)) (T : Tape (Sym A B aux.tm)) (c_halt : aux.tm.Cfg),
      Represents T S →
      c_halt.l = none →
      (flip bind aux.tm.step)^[n] (some ⟨some l, v, liftStk S⟩) = some c_halt →
      ∃ (S_f : ∀ k, List (Reach aux.tm k)) (T_f : Tape (Sym A B aux.tm))
        (q_f : SubStmt aux.tm) (v_f : aux.tm.σ),
        liftStk S_f = c_halt.stk ∧
        Represents T_f S_f ∧
        q_f.val = .halt ∧
        maxDepth S_f ≤ maxDepth S + maxStmtCost aux.tm * n ∧
        Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
          ⟨.exec ⟨aux.tm.m l, mem_allStmts_m aux.tm l⟩ v, T⟩
          (some ⟨.exec q_f v_f, T_f⟩)
          (n * maxStmtCost aux.tm * (2 * (maxDepth S + maxStmtCost aux.tm * n) + 4))) := by
  intro n
  induction n with
  | zero =>
      intro l v S T c_halt _ hnone hrun
      have heq : (⟨some l, v, liftStk S⟩ : aux.tm.Cfg) = c_halt := Option.some.inj hrun
      rw [← heq] at hnone; cases hnone
  | succ n ih =>
      intro l v S T c_halt hrep hnone hrun
      rw [Function.iterate_succ_apply] at hrun
      have hst : flip bind aux.tm.step (some ⟨some l, v, liftStk S⟩) =
          (some (TM2.stepAux (aux.tm.m l) v (liftStk S)) : Option aux.tm.Cfg) := rfl
      rw [hst] at hrun
      obtain ⟨S1, T1, q1, hlift1, hrep1, hmd1, hq1, hev1⟩ :=
        sim_stmt aux (aux.tm.m l) (mem_allStmts_m aux.tm l) v T S hrep
      have hC : stmtCost (aux.tm.m l) ≤ maxStmtCost aux.tm := stmtCost_le_max aux.tm l
      cases hcl : (TM2.stepAux (aux.tm.m l) v (liftStk S)).l with
      | none =>
          rw [hcl] at hq1
          cases n with
          | zero =>
              have heq : TM2.stepAux (aux.tm.m l) v (liftStk S) = c_halt := Option.some.inj hrun
              refine ⟨S1, T1, q1, (TM2.stepAux (aux.tm.m l) v (liftStk S)).var,
                by rw [← heq]; exact hlift1, hrep1, hq1, by omega, ?_⟩
              apply evals_mono hev1
              nlinarith
          | succ m =>
              rw [Function.iterate_succ_apply] at hrun
              have hstep0 : flip bind aux.tm.step
                  (some (TM2.stepAux (aux.tm.m l) v (liftStk S)) : Option aux.tm.Cfg) = none := by
                change TM2.step aux.tm.m (TM2.stepAux (aux.tm.m l) v (liftStk S)) = none
                rcases hcfg : TM2.stepAux (aux.tm.m l) v (liftStk S) with ⟨ll, vv, ss⟩
                rw [hcfg] at hcl; dsimp at hcl; subst hcl; rfl
              rw [hstep0, iterate_none] at hrun
              cases hrun
      | some l1 =>
          rw [hcl] at hq1
          have hcfg1 : TM2.stepAux (aux.tm.m l) v (liftStk S) =
              ⟨some l1, (TM2.stepAux (aux.tm.m l) v (liftStk S)).var, liftStk S1⟩ := by
            rcases h : TM2.stepAux (aux.tm.m l) v (liftStk S) with ⟨ll, vv, ss⟩
            rw [h] at hcl hlift1
            dsimp at hcl hlift1
            subst hcl; rw [hlift1]
          rw [hcfg1] at hrun
          obtain ⟨S_f, T_f, q_f, v_f, hliftf, hrepf, hqf, hmdf, hev2⟩ :=
            ih l1 (TM2.stepAux (aux.tm.m l) v (liftStk S)).var S1 T1 c_halt hrep1 hnone hrun
          rw [hq1] at hev1
          have hcomb := evals_trans hev1 hev2
          refine ⟨S_f, T_f, q_f, v_f, hliftf, hrepf, hqf, ?_, ?_⟩
          · have : maxStmtCost aux.tm * (n + 1) = maxStmtCost aux.tm * n + maxStmtCost aux.tm := by
              ring
            omega
          · apply evals_mono hcomb
            have hmd1' : maxDepth S1 ≤ maxDepth S + maxStmtCost aux.tm := by omega
            have hCmul : maxStmtCost aux.tm * (n + 1) =
                maxStmtCost aux.tm * n + maxStmtCost aux.tm := by ring
            have h1 : stmtCost (aux.tm.m l) * (2 * (maxDepth S + stmtCost (aux.tm.m l)) + 4) ≤
                maxStmtCost aux.tm * (2 * (maxDepth S + maxStmtCost aux.tm * (n + 1)) + 4) := by
              apply Nat.mul_le_mul hC
              omega
            have h2 : n * maxStmtCost aux.tm * (2 * (maxDepth S1 + maxStmtCost aux.tm * n) + 4) ≤
                n * maxStmtCost aux.tm *
                  (2 * (maxDepth S + maxStmtCost aux.tm * (n + 1)) + 4) := by
              apply Nat.mul_le_mul_left
              omega
            have hsum :
                maxStmtCost aux.tm * (2 * (maxDepth S + maxStmtCost aux.tm * (n + 1)) + 4) +
                n * maxStmtCost aux.tm * (2 * (maxDepth S + maxStmtCost aux.tm * (n + 1)) + 4) =
                (n + 1) * maxStmtCost aux.tm *
                  (2 * (maxDepth S + maxStmtCost aux.tm * (n + 1)) + 4) := by ring
            omega

/-! ## Phase 3 Proof: Output Extraction from Track k₁ -/

def Phase3Inv {A B : Type} (aux : TM2ComputableAux A B)
    (outList : List (Reach aux.tm aux.tm.k₁))
    (T : Tape (Sym A B aux.tm)) (done : ℕ) : Prop :=
  let m := outList.length
  T.nth 0 = .wall ∧
  (∀ (j : ℕ) (hj : j < m - done),
    isTrackOrBlank (T.nth ((j + 1 : ℕ) : ℤ)) ∧
    readTrack (T.nth ((j + 1 : ℕ) : ℤ)) aux.tm.k₁ =
      some (outList.reverse[j]'(by simp; omega))) ∧
  (∀ j : ℕ, m - done ≤ j → j < m → T.nth ((j + 1 : ℕ) : ℤ) = .mark) ∧
  T.nth ((m + 1 : ℕ) : ℤ) = .outWall ∧
  (∀ (i : ℕ) (hi : i < done),
    ∃ (him : i < m),
      T.nth (((m + 2 + i : ℕ) : ℤ)) = .out (aux.outputAlphabet (outList[i]'him).val)) ∧
  (∀ i : ℕ, done ≤ i → isTrackOrBlank (T.nth (((m + 2 + i : ℕ) : ℤ))))

lemma p3_toEnd_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (S : ∀ k, List (Reach aux.tm k)) (hrep : Represents T S) :
    ∀ (i : ℕ), i ≤ (S aux.tm.k₁).length →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p3_toEnd, shiftZ T ((i + 1 : ℕ) : ℤ)⟩
        (some ⟨.p3_toEnd, shiftZ T (((S aux.tm.k₁).length + 1 : ℕ) : ℤ)⟩)
        ((S aux.tm.k₁).length - i)) := by
  intro i hi
  induction hd : (S aux.tm.k₁).length - i generalizing i with
  | zero =>
      have hieq : i = (S aux.tm.k₁).length := by omega
      subst hieq; exact evals_zero _
  | succ d ih =>
      have hilt : i < (S aux.tm.k₁).length := by omega
      have hsome : (readTrack (shiftZ T ((i + 1 : ℕ) : ℤ)).head aux.tm.k₁).isSome = true := by
        rw [shiftZ_head, hrep.2.2 aux.tm.k₁ i, List.getElem?_eq_getElem (by simp; omega)]
        rfl
      have s1 : (simMachine aux).step ⟨.p3_toEnd, shiftZ T ((i + 1 : ℕ) : ℤ)⟩ =
          some ⟨.p3_toEnd, shiftZ T (((i + 1) + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move (by simp only [simDelta, hsome, ↓reduceIte]; rfl), shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (i + 1) (by omega) (by omega))

lemma p3_fetch_marks {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (base : ℕ) :
    ∀ (k : ℕ),
      (∀ t : ℕ, t < k → T.nth ((base + t + 1 : ℕ) : ℤ) = .mark) →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p3_fetch, shiftZ T ((base + k : ℕ) : ℤ)⟩
        (some ⟨.p3_fetch, shiftZ T (base : ℤ)⟩) k) := by
  intro k
  induction k with
  | zero => intro _; simp; exact evals_zero _
  | succ k ih =>
      intro hmarks
      have hhead : (shiftZ T ((base + (k + 1) : ℕ) : ℤ)).head = .mark := by
        rw [shiftZ_head]
        have := hmarks k (Nat.lt_succ_self k)
        simpa [Nat.add_assoc] using this
      have s1 : (simMachine aux).step ⟨.p3_fetch, shiftZ T ((base + (k + 1) : ℕ) : ℤ)⟩ =
          some ⟨.p3_fetch, shiftZ T ((base + k : ℕ) : ℤ)⟩ := by
        rw [step_move (by rw [hhead]; rfl), shiftZ_move_left]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih fun t ht => hmarks t (by omega))

lemma p3_carryOut_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (b : B) (z₀ : ℤ) :
    ∀ (steps : ℕ),
      (∀ t : ℕ, t < steps →
        T.nth (z₀ + t) = .mark ∨ T.nth (z₀ + t) = .outWall ∨ ∃ b', T.nth (z₀ + t) = .out b') →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p3_carryOut b, shiftZ T z₀⟩
        (some ⟨.p3_carryOut b, shiftZ T (z₀ + steps)⟩) steps) := by
  intro steps
  induction steps generalizing z₀ with
  | zero => intro _; simp; exact evals_zero _
  | succ steps ih =>
      intro hok
      have h0 := hok 0 (Nat.zero_lt_succ steps)
      simp only [Nat.cast_zero, add_zero] at h0
      have hstep_eq : simDelta aux (.p3_carryOut b) (shiftZ T z₀).head =
          some (.p3_carryOut b, .move .right) := by
        rw [shiftZ_head]
        rcases h0 with h | h | ⟨b', h⟩
        · rw [h]; rfl
        · rw [h]; rfl
        · rw [h]; rfl
      have s1 : (simMachine aux).step ⟨.p3_carryOut b, shiftZ T z₀⟩ =
          some ⟨.p3_carryOut b, shiftZ T (z₀ + 1)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_right]
      have hrest := ih (z₀ + 1) (fun t ht => by
        have := hok (t + 1) (by omega)
        rw [show z₀ + 1 + (t : ℤ) = z₀ + ((t + 1 : ℕ) : ℤ) by omega]
        exact this)
      rw [show z₀ + 1 + (steps : ℤ) = z₀ + ((steps + 1 : ℕ) : ℤ) by omega] at hrest
      exact evals_step s1 hrest

lemma p3_backToOutWall_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (base : ℕ) :
    ∀ (k : ℕ),
      (∀ t : ℕ, t < k → T.nth ((base + t + 1 : ℕ) : ℤ) ≠ .outWall) →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p3_backToOutWall, shiftZ T ((base + k : ℕ) : ℤ)⟩
        (some ⟨.p3_backToOutWall, shiftZ T (base : ℤ)⟩) k) := by
  intro k
  induction k with
  | zero => intro _; simp; exact evals_zero _
  | succ k ih =>
      intro hne
      have h0 : (shiftZ T ((base + (k + 1) : ℕ) : ℤ)).head ≠ .outWall := by
        rw [shiftZ_head]
        have := hne k (Nat.lt_succ_self k)
        simpa [Nat.add_assoc] using this
      have hstep_eq : simDelta aux .p3_backToOutWall (shiftZ T ((base + (k + 1) : ℕ) : ℤ)).head =
          some (.p3_backToOutWall, .move .left) := by
        cases h : (shiftZ T ((base + (k + 1) : ℕ) : ℤ)).head with
        | outWall => exact absurd h h0
        | blank => rfl
        | inp _ => rfl
        | out _ => rfl
        | wall => rfl
        | mark => rfl
        | cell _ => rfl
      have s1 : (simMachine aux).step ⟨.p3_backToOutWall, shiftZ T ((base + (k + 1) : ℕ) : ℤ)⟩ =
          some ⟨.p3_backToOutWall, shiftZ T ((base + k : ℕ) : ℤ)⟩ := by
        rw [step_move hstep_eq, shiftZ_move_left]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih fun t ht => hne t (by omega))

lemma p3_toOutWall_walk {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (T : Tape (Sym A B aux.tm)) (m : ℕ)
    (hmarks : ∀ j : ℕ, j < m → T.nth ((j + 1 : ℕ) : ℤ) = .mark) :
    ∀ (k : ℕ), k ≤ m →
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.p3_toOutWall, shiftZ T ((k + 1 : ℕ) : ℤ)⟩
        (some ⟨.p3_toOutWall, shiftZ T ((m + 1 : ℕ) : ℤ)⟩) (m - k)) := by
  intro k hk
  induction hd : m - k generalizing k with
  | zero =>
      have hkeq : k = m := by omega
      subst hkeq; exact evals_zero _
  | succ d ih =>
      have hklt : k < m := by omega
      have hhead : (shiftZ T ((k + 1 : ℕ) : ℤ)).head = .mark := by
        rw [shiftZ_head]; exact hmarks k hklt
      have s1 : (simMachine aux).step ⟨.p3_toOutWall, shiftZ T ((k + 1 : ℕ) : ℤ)⟩ =
          some ⟨.p3_toOutWall, shiftZ T (((k + 1) + 1 : ℕ) : ℤ)⟩ := by
        rw [step_move (by rw [hhead]; rfl), shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      exact evals_step s1 (ih (k + 1) (by omega) (by omega))

lemma p3_loop {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (outList : List (Reach aux.tm aux.tm.k₁)) :
    ∀ (done : ℕ) (T : Tape (Sym A B aux.tm)),
      done ≤ outList.length →
      Phase3Inv aux outList T done →
      ∃ c_halt : (simMachine aux).Cfg,
        Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
          ⟨.p3_fetch, shiftZ T (outList.length : ℤ)⟩ (some c_halt)
          ((outList.length - done) * (4 * outList.length + 6) + 2 * outList.length + 2)) ∧
        (simMachine aux).step c_halt = none ∧
        (simMachine aux).Shows c_halt (outList.map fun y => aux.outputAlphabet y.val) := by
  intro done T hle hinv
  let m := outList.length
  induction hd : m - done generalizing done T with
  | zero =>
      have hdeq : done = m := by omega
      subst hdeq
      rcases hinv with ⟨h0, _, hmarks, houtW, houts, hrestTB⟩
      have hfetch := p3_fetch_marks aux T 0 m (fun t ht => by
        simpa using hmarks t (by omega) ht)
      rw [Nat.zero_add] at hfetch
      have s_wall : (simMachine aux).step ⟨.p3_fetch, shiftZ T 0⟩ =
          some ⟨.p3_toOutWall, shiftZ T 1⟩ := by
        have hw : (shiftZ T 0).head = .wall := by rw [shiftZ_head]; exact h0
        rw [step_move (by rw [hw]; rfl), shiftZ_move_right]
        congr 2
      have htoW := p3_toOutWall_walk aux T m (fun j hj => hmarks j (by omega) hj) 0 (Nat.zero_le _)
      have s_fin : (simMachine aux).step ⟨.p3_toOutWall, shiftZ T ((m + 1 : ℕ) : ℤ)⟩ =
          some ⟨.halt, shiftZ T ((m + 2 : ℕ) : ℤ)⟩ := by
        have how : (shiftZ T ((m + 1 : ℕ) : ℤ)).head = .outWall := by rw [shiftZ_head]; exact houtW
        rw [step_move (by rw [how]; rfl), shiftZ_move_right]
        exact cfg_shiftZ_eq _ T (by omega)
      have hall := evals_trans hfetch (evals_step s_wall (evals_trans htoW (evals_one s_fin)))
      refine ⟨⟨.halt, shiftZ T ((m + 2 : ℕ) : ℤ)⟩, evals_mono hall (by simp; omega), rfl, ?_⟩
      constructor
      · intro i hi
        change (shiftZ T ((m + 2 : ℕ) : ℤ)).right₀.nth i =
          Sym.out ((outList.map fun y => aux.outputAlphabet y.val)[i]'hi)
        rw [shiftZ_right₀_nth]
        have him : i < m := by simpa [m] using hi
        rcases houts i him with ⟨_, hti⟩
        rw [show (i : ℤ) + ((m + 2 : ℕ) : ℤ) = ((m + 2 + i : ℕ) : ℤ) by omega, hti]
        simp
      · intro b'
        change (shiftZ T ((m + 2 : ℕ) : ℤ)).right₀.nth
          (outList.map fun y => aux.outputAlphabet y.val).length ≠ Sym.out b'
        rw [shiftZ_right₀_nth]
        have hlen : (outList.map fun y => aux.outputAlphabet y.val).length = m := by simp [m]
        rw [hlen, show (m : ℤ) + ((m + 2 : ℕ) : ℤ) = ((m + 2 + m : ℕ) : ℤ) by omega]
        have htb := hrestTB m le_rfl
        cases hc : T.nth ((m + 2 + m : ℕ) : ℤ) <;> rw [hc] at htb
        · intro e; cases e
        · cases htb
        · cases htb
        · cases htb
        · cases htb
        · cases htb
        · intro e; cases e
  | succ d ih =>
      have hdlt : done < m := by omega
      rcases hinv with ⟨h0, hrem, hmarks, houtW, houts, hrestTB⟩
      have hfetch := p3_fetch_marks aux T (m - done) done (fun t ht => by
        have := hmarks (m - done + t) (by omega) (by omega)
        simpa [Nat.add_assoc] using this)
      have hsum1 : m - done + done = m := by omega
      rw [hsum1] at hfetch
      have hpos_j : m - done = (m - done - 1) + 1 := by omega
      have hjlt : m - done - 1 < m - done := by omega
      rcases hrem (m - done - 1) hjlt with ⟨htb_j, hrt_j⟩
      let y : Reach aux.tm aux.tm.k₁ := outList[done]'hdlt
      have hy_eq : (outList.reverse[m - done - 1]'(by simp [m]; omega)) = y := by
        rw [List.getElem_reverse]
        congr 1; simp only [m]; omega
      rw [hy_eq] at hrt_j
      let b : B := aux.outputAlphabet y.val
      let T1 := tapeWriteZ T ((m - done : ℕ) : ℤ) .mark
      have s_mark : (simMachine aux).step ⟨.p3_fetch, shiftZ T ((m - done : ℕ) : ℤ)⟩ =
          some ⟨.p3_carryOut b, shiftZ T1 ((m - done : ℕ) : ℤ)⟩ := by
        have hhead : (shiftZ T ((m - done : ℕ) : ℤ)).head = T.nth ((m - done - 1 + 1 : ℕ) : ℤ) := by
          rw [shiftZ_head]; congr 1; omega
        have hstep_eq : simDelta aux (.p3_fetch) (shiftZ T ((m - done : ℕ) : ℤ)).head =
            some (.p3_carryOut b, .write .mark) := by
          rw [hhead]
          cases hgc : T.nth ((m - done - 1 + 1 : ℕ) : ℤ) <;> rw [hgc] at htb_j hrt_j
          · simp [readTrack] at hrt_j
          · cases htb_j
          · cases htb_j
          · cases htb_j
          · cases htb_j
          · cases htb_j
          · simp [simDelta, readTrack] at hrt_j ⊢
            rw [hrt_j]
        rw [step_write hstep_eq, shiftZ_write]
      have hcarry := p3_carryOut_walk aux T1 b ((m - done : ℕ) : ℤ) (2 * done + 2) (fun t ht => by
        rw [tapeWriteZ_nth]
        by_cases ht0 : ((m - done : ℕ) : ℤ) + t = ((m - done : ℕ) : ℤ)
        · rw [ite_eq_left ht0]; exact Or.inl rfl
        · rw [ite_eq_right ht0]
          by_cases hlt1 : m - done + t < m + 1
          · have hidx : ∃ j : ℕ, m - done ≤ j ∧ j < m ∧
                ((m - done : ℕ) : ℤ) + t = ((j + 1 : ℕ) : ℤ) :=
              ⟨m - done + t - 1, by omega, by omega, by omega⟩
            rcases hidx with ⟨j, hj1, hj2, hjeq⟩
            rw [hjeq, hmarks j hj1 hj2]; exact Or.inl rfl
          · by_cases heq1 : m - done + t = m + 1
            · rw [show ((m - done : ℕ) : ℤ) + t = ((m + 1 : ℕ) : ℤ) by omega, houtW]
              exact Or.inr (Or.inl rfl)
            · have hidx : ∃ i : ℕ, i < done ∧
                  ((m - done : ℕ) : ℤ) + t = ((m + 2 + i : ℕ) : ℤ) :=
                ⟨m - done + t - (m + 2), by omega, by omega⟩
              rcases hidx with ⟨i, hi, hieq⟩
              rcases houts i hi with ⟨him, hti⟩
              rw [hieq, hti]; exact Or.inr (Or.inr ⟨_, rfl⟩))
      have hpos2 : ((m - done : ℕ) : ℤ) + ((2 * done + 2 : ℕ) : ℤ) =
          ((m + 2 + done : ℕ) : ℤ) := by omega
      rw [hpos2] at hcarry
      let T2 := tapeWriteZ T1 ((m + 2 + done : ℕ) : ℤ) (.out b)
      have s_out : (simMachine aux).step ⟨.p3_carryOut b, shiftZ T1 ((m + 2 + done : ℕ) : ℤ)⟩ =
          some ⟨.p3_backToOutWall, shiftZ T2 ((m + 2 + done : ℕ) : ℤ)⟩ := by
        have htb := hrestTB done le_rfl
        have hhead : (shiftZ T1 ((m + 2 + done : ℕ) : ℤ)).head =
            T.nth ((m + 2 + done : ℕ) : ℤ) := by
          rw [shiftZ_head, tapeWriteZ_nth, ite_eq_right (by omega)]
        have hstep_eq : simDelta aux (.p3_carryOut b) (shiftZ T1 ((m + 2 + done : ℕ) : ℤ)).head =
            some (.p3_backToOutWall, .write (.out b)) := by
          rw [hhead]
          cases hc : T.nth ((m + 2 + done : ℕ) : ℤ) <;> rw [hc] at htb
          · rfl
          · cases htb
          · cases htb
          · cases htb
          · cases htb
          · cases htb
          · rfl
        rw [step_write hstep_eq, shiftZ_write]
      have hback := p3_backToOutWall_walk aux T2 (m + 1) (done + 1) (fun t ht => by
        rw [tapeWriteZ_nth]
        by_cases hte : ((m + 1 + t + 1 : ℕ) : ℤ) = ((m + 2 + done : ℕ) : ℤ)
        · rw [ite_eq_left hte]; intro h; cases h
        · rw [ite_eq_right hte, tapeWriteZ_nth, ite_eq_right (by omega)]
          have htlt : t < done := by omega
          rcases houts t htlt with ⟨_, hti⟩
          rw [show ((m + 1 + t + 1 : ℕ) : ℤ) = ((m + 2 + t : ℕ) : ℤ) by omega, hti]
          intro h; cases h)
      have hpos3 : ((m + 1 + (done + 1) : ℕ) : ℤ) = ((m + 2 + done : ℕ) : ℤ) := by omega
      rw [hpos3] at hback
      have s_left : (simMachine aux).step ⟨.p3_backToOutWall, shiftZ T2 ((m + 1 : ℕ) : ℤ)⟩ =
          some ⟨.p3_fetch, shiftZ T2 (m : ℤ)⟩ := by
        have how2 : (shiftZ T2 ((m + 1 : ℕ) : ℤ)).head = .outWall := by
          rw [shiftZ_head, tapeWriteZ_nth, ite_eq_right (by omega),
              tapeWriteZ_nth, ite_eq_right (by omega)]
          exact houtW
        rw [step_move (by rw [how2]; rfl), shiftZ_move_left]
        exact cfg_shiftZ_eq _ T2 (by omega)
      have hinv2 : Phase3Inv aux outList T2 (done + 1) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact h0
        · intro j hj
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hrem j (by omega)
        · intro j hj1 hj2
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth]
          by_cases hje : ((j + 1 : ℕ) : ℤ) = ((m - done : ℕ) : ℤ)
          · rw [ite_eq_left hje]
          · rw [ite_eq_right hje]; exact hmarks j (by omega) hj2
        · rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact houtW
        · intro i hi
          rw [tapeWriteZ_nth]
          by_cases hie : ((m + 2 + i : ℕ) : ℤ) = ((m + 2 + done : ℕ) : ℤ)
          · have hid : i = done := by omega
            subst hid
            refine ⟨hdlt, ?_⟩
            rw [ite_eq_left hie]
          · rw [ite_eq_right hie, tapeWriteZ_nth, ite_eq_right (by omega)]
            exact houts i (by omega)
        · intro i hge
          rw [tapeWriteZ_nth, ite_eq_right (by omega), tapeWriteZ_nth, ite_eq_right (by omega)]
          exact hrestTB i (by omega)
      obtain ⟨c_halt, hrest, hstop, hshows⟩ := ih (done + 1) T2 (by omega) hinv2 (by omega)
      have hall := evals_trans hfetch (evals_step s_mark (evals_trans hcarry
        (evals_step s_out (evals_trans hback (evals_step s_left hrest)))))
      refine ⟨c_halt, evals_mono hall ?_, hstop, hshows⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega

lemma phase3_run {A B : Type} [Fintype A] [Fintype B] (aux : TM2ComputableAux A B)
    (q_f : SubStmt aux.tm) (hqf : q_f.val = .halt) (v_f : aux.tm.σ)
    (S_f : ∀ k, List (Reach aux.tm k)) (T_f : Tape (Sym A B aux.tm))
    (hrep : Represents T_f S_f) :
    let m := (S_f aux.tm.k₁).length
    ∃ c_halt : (simMachine aux).Cfg,
      Nonempty (StateTransition.EvalsToInTime (simMachine aux).step
        ⟨.exec q_f v_f, T_f⟩ (some c_halt) (4 * m * m + 9 * m + 5)) ∧
      (simMachine aux).step c_halt = none ∧
      (simMachine aux).Shows c_halt ((S_f aux.tm.k₁).map fun y => aux.outputAlphabet y.val) := by
  intro m
  have s0 : (simMachine aux).step ⟨.exec q_f v_f, T_f⟩ =
      some ⟨.p3_toEnd, shiftZ T_f ((0 + 1 : ℕ) : ℤ)⟩ := by
    have hstep_eq : simDelta aux (.exec q_f v_f) T_f.head = some (.p3_toEnd, .move .right) := by
      simp only [simDelta]
      split
      all_goals first | rfl | (rename_i h; rw [hqf] at h; cases h)
    rw [step_move hstep_eq, show T_f.move .right = shiftZ T_f ((0 + 1 : ℕ) : ℤ) by
      rw [← shiftZ_zero T_f, shiftZ_move_right]; rfl]
  have h1 := p3_toEnd_loop aux T_f S_f hrep 0 (Nat.zero_le _)
  let T0 := tapeWriteZ T_f ((m + 1 : ℕ) : ℤ) .outWall
  have s1 : (simMachine aux).step ⟨.p3_toEnd, shiftZ T_f ((m + 1 : ℕ) : ℤ)⟩ =
      some ⟨.p3_startFetch, shiftZ T0 ((m + 1 : ℕ) : ℤ)⟩ := by
    have hnone : (readTrack (shiftZ T_f ((m + 1 : ℕ) : ℤ)).head aux.tm.k₁).isSome = false := by
      rw [shiftZ_head, hrep.2.2 aux.tm.k₁ m, List.getElem?_eq_none (by simp [m])]
      rfl
    rw [step_write (by simp only [simDelta, hnone, Bool.false_eq_true, ↓reduceIte]; rfl),
      shiftZ_write]
  have s2 : (simMachine aux).step ⟨.p3_startFetch, shiftZ T0 ((m + 1 : ℕ) : ℤ)⟩ =
      some ⟨.p3_fetch, shiftZ T0 (m : ℤ)⟩ := by
    rw [step_move rfl, shiftZ_move_left]
    exact cfg_shiftZ_eq _ T0 (by omega)
  have hinv0 : Phase3Inv aux (S_f aux.tm.k₁) T0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tapeWriteZ_nth, ite_eq_right (by omega)]; exact hrep.1
    · intro j hj
      rw [tapeWriteZ_nth, ite_eq_right (by omega)]
      refine ⟨hrep.2.1 j, ?_⟩
      rw [hrep.2.2 aux.tm.k₁ j, List.getElem?_eq_getElem (by simp; omega)]
    · intro j hj1 hj2; omega
    · rw [tapeWriteZ_nth, ite_eq_left rfl]
    · intro i hi; omega
    · intro i _
      rw [tapeWriteZ_nth, ite_eq_right (by omega)]
      rw [show (((S_f aux.tm.k₁).length + 2 + i : ℕ) : ℤ) =
        ((((S_f aux.tm.k₁).length + 1 + i) + 1 : ℕ) : ℤ) by omega]
      exact hrep.2.1 ((S_f aux.tm.k₁).length + 1 + i)
  obtain ⟨c_halt, hloop, hstop, hshows⟩ := p3_loop aux (S_f aux.tm.k₁) 0 T0 (Nat.zero_le _) hinv0
  have hall := evals_step s0 (evals_trans h1 (evals_step s1 (evals_step s2 hloop)))
  refine ⟨c_halt, evals_mono hall ?_, hstop, hshows⟩
  simp only [Nat.sub_zero, m]
  nlinarith

end PvsNP.Units.m1_tm2_to_st

/-- Any function computable in polynomial time by a FinTM2 is computable in polynomial time
on PvsNP.SingleTape. -/
theorem PvsNP.Units.m1_tm2_to_st :
    ∀ {α β A B : Type} [Finite B] (ea : α → List A) (eb : β → List B) (f : α → β),
      PvsNP.PolyTimeComputable ea eb f → PvsNP.SingleTape.PolyTimeComputable ea eb f := by
  intro α β A B _ ea eb f hpoly
  obtain ⟨M⟩ := hpoly
  let _ : Fintype A := @Fintype.ofEquiv _ _ M.tm.Γk₀Fin M.inputAlphabet
  let _ : Fintype B := Fintype.ofFinite B
  let C : ℕ := PvsNP.Units.m1_tm2_to_st.maxStmtCost M.tm
  let D : Polynomial ℕ := Polynomial.X + Polynomial.C C * M.time
  let Tpoly : Polynomial ℕ :=
    (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X + Polynomial.C 4) +
    (M.time * Polynomial.C C * (Polynomial.C 2 * D + Polynomial.C 4)) +
    (Polynomial.C 4 * D ^ 2 + Polynomial.C 9 * D + Polynomial.C 5)
  refine ⟨PvsNP.Units.m1_tm2_to_st.simMachine M.toTM2ComputableAux, Tpoly, fun a => ?_⟩
  let x := ea a
  obtain ⟨T1, hrep1, hp1⟩ :=
    PvsNP.Units.m1_tm2_to_st.phase1_run M.toTM2ComputableAux x
  have hout := M.outputsFun a
  have hinit_eq : Turing.initList M.tm (x.map M.inputAlphabet.invFun) =
      ⟨some M.tm.main, M.tm.initialState,
        PvsNP.Units.m1_tm2_to_st.liftStk
          (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x)⟩ := by
    rw [PvsNP.Units.m1_tm2_to_st.liftStk_initReachStk]; rfl
  have hrun : (flip bind M.tm.step)^[hout.steps]
      (some ⟨some M.tm.main, M.tm.initialState,
        PvsNP.Units.m1_tm2_to_st.liftStk
          (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x)⟩) =
      some (Turing.haltList M.tm ((eb (f a)).map M.outputAlphabet.invFun)) :=
    (congrArg (fun c => (flip bind M.tm.step)^[hout.steps] (some c)) hinit_eq.symm).trans
      hout.evals_in_steps
  obtain ⟨S_f, T_f, q_f, v_f, hliftf, hrepf, hqf, hmdf, hp2⟩ :=
    PvsNP.Units.m1_tm2_to_st.sim_run M.toTM2ComputableAux hout.steps
      M.tm.main M.tm.initialState
      (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x)
      T1 (Turing.haltList M.tm ((eb (f a)).map M.outputAlphabet.invFun))
      hrep1 rfl hrun
  obtain ⟨c_halt, hp3, hstop, hshows⟩ :=
    PvsNP.Units.m1_tm2_to_st.phase3_run M.toTM2ComputableAux q_f hqf v_f S_f T_f hrepf
  have hout_eq : (S_f M.tm.k₁).map (fun y => M.outputAlphabet y.val) = eb (f a) := by
    have hk1 : (PvsNP.Units.m1_tm2_to_st.liftStk S_f) M.tm.k₁ =
        (eb (f a)).map M.outputAlphabet.invFun := by
      rw [hliftf]
      let _ : DecidableEq M.tm.K := M.tm.kDecidableEq
      simp [Turing.haltList]
    have hmap : ((S_f M.tm.k₁).map Subtype.val).map M.outputAlphabet =
        ((eb (f a)).map M.outputAlphabet.invFun).map M.outputAlphabet :=
      congrArg (List.map M.outputAlphabet) hk1
    rw [List.map_map, List.map_map] at hmap
    have hright : ((eb (f a)).map (M.outputAlphabet ∘ M.outputAlphabet.invFun)) = eb (f a) := by
      simp [Function.comp_def]
    rw [hright] at hmap
    exact hmap
  rw [hout_eq] at hshows
  have hall := PvsNP.Units.m1_tm2_to_st.evals_trans
    (PvsNP.Units.m1_tm2_to_st.evals_trans hp1 hp2) hp3
  refine ⟨c_halt, ?_, hstop, hshows⟩
  apply PvsNP.Units.m1_tm2_to_st.evals_mono hall
  have hsteps_le : hout.steps ≤ M.time.eval x.length := hout.steps_le_m
  have hmd0 : PvsNP.Units.m1_tm2_to_st.maxDepth
      (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x) ≤ x.length :=
    PvsNP.Units.m1_tm2_to_st.maxDepth_initReachStk M.toTM2ComputableAux x
  have hlen_f : (S_f M.tm.k₁).length ≤ PvsNP.Units.m1_tm2_to_st.maxDepth S_f :=
    PvsNP.Units.m1_tm2_to_st.length_le_maxDepth S_f M.tm.k₁
  have hDF : PvsNP.Units.m1_tm2_to_st.maxDepth S_f ≤ D.eval x.length := by
    simp only [D, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hmul : C * hout.steps ≤ C * M.time.eval x.length := Nat.mul_le_mul_left C hsteps_le
    exact le_trans hmdf (Nat.add_le_add hmd0 hmul)
  have hD0 : PvsNP.Units.m1_tm2_to_st.maxDepth
      (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x) + C * hout.steps ≤
      D.eval x.length := by
    simp only [D, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hmul : C * hout.steps ≤ C * M.time.eval x.length := Nat.mul_le_mul_left C hsteps_le
    exact Nat.add_le_add hmd0 hmul
  have hp2_le : hout.steps * C * (2 * (PvsNP.Units.m1_tm2_to_st.maxDepth
        (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x) + C * hout.steps) + 4) ≤
      M.time.eval x.length * C * (2 * D.eval x.length + 4) := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_right C hsteps_le
    · omega
  have hp3_le : 4 * (S_f M.tm.k₁).length * (S_f M.tm.k₁).length + 9 * (S_f M.tm.k₁).length + 5 ≤
      4 * (D.eval x.length) ^ 2 + 9 * D.eval x.length + 5 := by
    have hml : (S_f M.tm.k₁).length ≤ D.eval x.length := le_trans hlen_f hDF
    have hsq : (S_f M.tm.k₁).length * (S_f M.tm.k₁).length ≤ D.eval x.length ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul hml hml
    rw [Nat.mul_assoc]
    omega
  simp only [Tpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  have hp1_eq : 4 * x.length * x.length + 9 * x.length + 4 =
      4 * x.length ^ 2 + 9 * x.length + 4 := by ring
  change (4 * x.length * x.length + 9 * x.length + 4) +
      (hout.steps * C * (2 * (PvsNP.Units.m1_tm2_to_st.maxDepth
        (PvsNP.Units.m1_tm2_to_st.initReachStk M.toTM2ComputableAux x) + C * hout.steps) + 4)) +
      (4 * (S_f M.tm.k₁).length * (S_f M.tm.k₁).length + 9 * (S_f M.tm.k₁).length + 5) ≤
      (4 * x.length ^ 2 + 9 * x.length + 4) +
      (M.time.eval x.length * C * (2 * D.eval x.length + 4)) +
      (4 * (D.eval x.length) ^ 2 + 9 * D.eval x.length + 5)
  omega
