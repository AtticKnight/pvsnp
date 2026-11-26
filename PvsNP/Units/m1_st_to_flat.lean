import Mathlib
import PvsNP.Defs
import CookLevin

/-
A single-tape machine of the campaign (Mathlib's TM0, a tape infinite both ways) simulated by a
one-tape machine of the vendored Cook-Levin model (a tape infinite to the right only).

The Cook-Levin tape keeps the marker of cell 0 as a wall. Every later cell holds a pair of symbols
of the simulated machine: the first parts, read from cell 1 rightwards, are the simulated tape to
the left of the head (nearest cell first), and the second parts are the simulated tape from the
head rightwards. So the simulated head always stands on cell 1. A write changes cell 1. A move
shifts one track one cell to the right in a sweep to the end of the tape and the other track one
cell to the left in the sweep back. When the simulated machine halts its output already starts at
cell 1, and one last sweep rewrites it in the output letters of the Cook-Levin model.
-/

namespace PvsNP.Units.m1_st_to_flat

open Turing

/-! ### A one-tape Cook-Levin machine given by a transition function -/

section table

variable {St Sy : Type} [Fintype St] [Fintype Sy]

/-- The number of a state. -/
noncomputable def encS (s : St) : ℕ := (Fintype.equivFin St s).val

theorem encS_inj {s s' : St} (h : encS s = encS s') : s = s' :=
  (Fintype.equivFin St).injective (Fin.ext h)

theorem encS_lt (s : St) : encS s < Fintype.card St := (Fintype.equivFin St s).isLt

variable (encY : Sy → ℕ) (sig : ℕ) (δ : St → Option Sy → Option (St × Option Sy × TMMove))
  (hlt : St → Bool) (s0 : St)

/-- The table entry of one transition. -/
noncomputable def entryOf (s : St) (o : Option Sy) (r : St × Option Sy × TMMove) :
    FlatTMTransEntry where
  src_state := encS s
  src_tape_vals := [o.map encY]
  dst_state := encS r.1
  dst_write_vals := [r.2.1.map encY]
  move_dirs := [r.2.2]

/-- The transition table. -/
noncomputable def table : List FlatTMTransEntry :=
  (Finset.univ : Finset St).toList.flatMap fun s =>
    (none :: (Finset.univ : Finset Sy).toList.map some).filterMap fun o =>
      (δ s o).map (entryOf encY s o)

/-- The machine. -/
noncomputable def mach : FlatTM where
  sig := sig
  tapes := 1
  states := Fintype.card St
  trans := table encY δ
  start := encS s0
  halt := (List.range (Fintype.card St)).map fun i =>
    @decide (∃ s : St, encS s = i ∧ hlt s = true) (Classical.propDecidable _)

theorem mem_opts (o : Option Sy) : o ∈ none :: (Finset.univ : Finset Sy).toList.map some := by
  cases o with
  | none => exact List.mem_cons_self
  | some y =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨y, Finset.mem_toList.mpr (Finset.mem_univ y), rfl⟩)

theorem mem_table (e : FlatTMTransEntry) :
    e ∈ table encY δ ↔ ∃ s o r, δ s o = some r ∧ e = entryOf encY s o r := by
  unfold table
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, -, he⟩
    rw [List.mem_filterMap] at he
    obtain ⟨o, -, ho⟩ := he
    cases hr : δ s o with
    | none => rw [hr] at ho; exact absurd ho (by simp)
    | some r =>
      rw [hr] at ho
      exact ⟨s, o, r, hr, (Option.some.inj ho).symm⟩
  · rintro ⟨s, o, r, hr, rfl⟩
    refine ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), ?_⟩
    rw [List.mem_filterMap]
    exact ⟨o, mem_opts o, by rw [hr]; rfl⟩

theorem mach_valid (hY : ∀ y, encY y < sig) : validFlatTM (mach encY sig δ hlt s0) := by
  refine ⟨encS_lt s0, by simp [mach], ?_⟩
  intro e he
  obtain ⟨s, o, r, -, rfl⟩ := (mem_table encY δ e).mp he
  refine ⟨encS_lt s, encS_lt r.1, rfl, rfl, rfl, ?_, ?_⟩
  · intro x hx
    have hx' : x = o.map encY := by simpa [entryOf] using hx
    subst hx'
    cases o with
    | none => trivial
    | some y => exact hY y
  · intro x hx
    have hx' : x = r.2.1.map encY := by simpa [entryOf] using hx
    subst hx'
    cases r.2.1 with
    | none => trivial
    | some y => exact hY y

theorem mach_halting (s : St) (tp : List (List ℕ × ℕ × List ℕ)) :
    haltingStateReached (mach encY sig δ hlt s0) ⟨encS s, tp⟩ = hlt s := by
  have h1 : haltingStateReached (mach encY sig δ hlt s0) ⟨encS s, tp⟩ =
      @decide (∃ s' : St, encS s' = encS s ∧ hlt s' = true) (Classical.propDecidable _) := by
    simp [haltingStateReached, mach, List.getD_eq_getElem?_getD, encS_lt]
  rw [h1]
  cases h : hlt s with
  | false =>
    refine @decide_eq_false _ (Classical.propDecidable _) ?_
    rintro ⟨s', he, ht⟩
    rw [encS_inj he, h] at ht
    exact absurd ht (by simp)
  | true => exact @decide_eq_true _ (Classical.propDecidable _) ⟨s, rfl, h⟩

theorem find_unique {α : Type} (p : α → Bool) (l : List α) (e : α) (he : e ∈ l)
    (hp : p e = true) (hu : ∀ e' ∈ l, p e' = true → e' = e) : l.find? p = some e := by
  cases h : l.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h e he)
  | some e' =>
    have h1 : p e' = true := List.find?_some h
    have h2 : e' ∈ l := List.mem_of_find?_eq_some h
    rw [hu e' h2 h1]

theorem mach_step (hYinj : Function.Injective encY) (s : St) (o : Option Sy)
    (r : St × Option Sy × TMMove) (hr : δ s o = some r) (tp : List ℕ × ℕ × List ℕ)
    (hcur : currentTapeSymbol tp = o.map encY) :
    stepFlatTM (mach encY sig δ hlt s0) ⟨encS s, [tp]⟩ =
      some ⟨encS r.1, [tapeStep tp (r.2.1.map encY) r.2.2]⟩ := by
  have hfind : (table encY δ).find? (fun e => entryMatchesConfig e ⟨encS s, [tp]⟩) =
      some (entryOf encY s o r) := by
    refine find_unique _ _ _ ((mem_table encY δ _).mpr ⟨s, o, r, hr, rfl⟩) ?_ ?_
    · simp [entryMatchesConfig, entryOf, hcur]
    · intro e' he' hm
      obtain ⟨s', o', r', hr', rfl⟩ := (mem_table encY δ e').mp he'
      simp only [entryMatchesConfig, entryOf, hcur, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      obtain ⟨h1, h2⟩ := hm
      have e1 := encS_inj h1
      subst e1
      have e2 : o' = o := Option.map_injective hYinj h2
      subst e2
      rw [hr] at hr'
      have e3 := Option.some.inj hr'
      subst e3
      rfl
  have hstep : stepFlatTM (mach encY sig δ hlt s0) ⟨encS s, [tp]⟩ =
      applyTransitionEntry ⟨encS s, [tp]⟩ (entryOf encY s o r) := by
    show Option.bind ((table encY δ).find? (fun e => entryMatchesConfig e ⟨encS s, [tp]⟩)) _ = _
    rw [hfind]
    rfl
  rw [hstep]
  simp [applyTransitionEntry, entryOf]

end table

/-! ### The tape of the Cook-Levin model -/

theorem cur_mid (lft : List ℕ) (A : List ℕ) (c : ℕ) (Bs : List ℕ) :
    currentTapeSymbol (lft, A.length, A ++ c :: Bs) = some c := by
  simp [currentTapeSymbol]

theorem cur_end (lft : List ℕ) (A : List ℕ) : currentTapeSymbol (lft, A.length, A) = none := by
  simp [currentTapeSymbol]

theorem wr_mid (lft : List ℕ) (A : List ℕ) (c v : ℕ) (Bs : List ℕ) :
    writeCurrentTapeSymbol (lft, A.length, A ++ c :: Bs) (some v) =
      (lft, A.length, A ++ v :: Bs) := by
  simp [writeCurrentTapeSymbol]

theorem wr_end (lft : List ℕ) (A : List ℕ) (v : ℕ) :
    writeCurrentTapeSymbol (lft, A.length, A) (some v) = (lft, A.length, A ++ [v]) := by
  simp [writeCurrentTapeSymbol]

/-- A run of exactly `n` steps, none of them from a halting state. -/
inductive Steps (Mx : FlatTM) : ℕ → FlatTMConfig → FlatTMConfig → Prop
  | refl (c : FlatTMConfig) : Steps Mx 0 c c
  | step {n : ℕ} {c c1 c' : FlatTMConfig} : haltingStateReached Mx c = false →
      stepFlatTM Mx c = some c1 → Steps Mx n c1 c' → Steps Mx (n + 1) c c'

theorem Steps.trans {Mx : FlatTM} {n m : ℕ} {a b c : FlatTMConfig} (h₁ : Steps Mx n a b)
    (h₂ : Steps Mx m b c) : Steps Mx (n + m) a c := by
  induction h₁ with
  | refl c => rw [Nat.zero_add]; exact h₂
  | step hh hs _ ih =>
    rw [Nat.add_right_comm]
    exact Steps.step hh hs (ih h₂)

theorem Steps.cast {Mx : FlatTM} {n m : ℕ} {a b : FlatTMConfig} (h : Steps Mx n a b)
    (e : n = m) : Steps Mx m a b := e ▸ h

theorem Steps.run {Mx : FlatTM} {n : ℕ} {a b : FlatTMConfig} (h : Steps Mx n a b) :
    runFlatTM n Mx a = some b := by
  induction h with
  | refl c => rfl
  | @step k c c1 c' hh hs _ ih =>
    show (if haltingStateReached Mx c = true then some c
      else match stepFlatTM Mx c with
        | none => some c
        | some cfg' => runFlatTM k Mx cfg') = some c'
    rw [if_neg (by rw [hh]; decide), hs]
    exact ih

/-! ### The simulating machine -/

/-- The kinds of states of the simulating machine. -/
inductive Tag
  | i0 | i1 | i2 | ret | main | fw | bw | fwr | bwl | out | done
  deriving DecidableEq

instance : Fintype Tag where
  elems := {Tag.i0, Tag.i1, Tag.i2, Tag.ret, Tag.main, Tag.fw, Tag.bw, Tag.fwr, Tag.bwl, Tag.out,
    Tag.done}
  complete := by intro x; cases x <;> decide

section sim

variable (M : PvsNP.SingleTape.Machine Bool Bool)

instance instFintypeΓ : Fintype M.Γ := M.fintypeΓ

instance instFintypeΛ : Fintype M.Λ := M.fintypeΛ

noncomputable instance instDecEqΓ : DecidableEq M.Γ := Classical.decEq _

/-- A state: its kind, a state of the simulated machine and a carried symbol. -/
abbrev St : Type := Tag × M.Λ × M.Γ

/-- A cell: one of the four symbols of the string convention, or a pair of simulated symbols. -/
abbrev Sy : Type := Fin 4 ⊕ (M.Γ × M.Γ)

abbrev Tr : Type := St M × Option (Sy M) × TMMove

/-- The number of a cell symbol. -/
noncomputable def encY : Sy M → ℕ
  | Sum.inl i => i.val
  | Sum.inr p => 4 + (Fintype.equivFin (M.Γ × M.Γ) p).val

noncomputable def sigOf : ℕ := 4 + Fintype.card (M.Γ × M.Γ)

theorem encY_lt (y : Sy M) : encY M y < sigOf M := by
  cases y with
  | inl i => have := i.isLt; simp only [encY, sigOf]; omega
  | inr p => have := (Fintype.equivFin (M.Γ × M.Γ) p).isLt; simp only [encY, sigOf]; omega

theorem encY_inj : Function.Injective (encY M) := by
  intro y y' h
  cases y with
  | inl i =>
    cases y' with
    | inl j => exact congrArg Sum.inl (Fin.ext h)
    | inr p => have := i.isLt; simp only [encY] at h; omega
  | inr p =>
    cases y' with
    | inl j => have := j.isLt; simp only [encY] at h; omega
    | inr p' =>
      simp only [encY] at h
      have h' : (Fintype.equivFin (M.Γ × M.Γ) p).val = (Fintype.equivFin (M.Γ × M.Γ) p').val := by
        omega
      exact congrArg Sum.inr ((Fintype.equivFin _).injective (Fin.ext h'))

/-- The wall of cell 0. -/
abbrev W : Sy M := Sum.inl 3

/-- Writing the output: from cell 1 rightwards, as long as the second part is an output letter. -/
noncomputable def outTr (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (_, r)) =>
    if r = M.out true then some ((Tag.out, default, default), some (Sum.inl 2), TMMove.Rmove)
    else if r = M.out false then
      some ((Tag.out, default, default), some (Sum.inl 1), TMMove.Rmove)
    else some ((Tag.done, default, default), some (Sum.inl 0), TMMove.Nmove)
  | none => some ((Tag.done, default, default), some (Sum.inl 0), TMMove.Nmove)
  | some (Sum.inl _) => none

noncomputable def i1Tr (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inl i) =>
    if i = 1 then
      some ((Tag.i1, default, default), some (Sum.inr (default, M.inp false)), TMMove.Rmove)
    else if i = 2 then
      some ((Tag.i1, default, default), some (Sum.inr (default, M.inp true)), TMMove.Rmove)
    else if i = 0 then
      some ((Tag.i2, default, default), some (Sum.inr (default, default)), TMMove.Rmove)
    else none
  | _ => none

noncomputable def i2Tr (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inl i) =>
    if i = 3 then
      some ((Tag.ret, default, default), some (Sum.inr (default, default)), TMMove.Lmove)
    else none
  | _ => none

noncomputable def retTr (q : M.Λ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inl _) => some ((Tag.main, q, default), none, TMMove.Rmove)
  | _ => some ((Tag.ret, q, default), none, TMMove.Lmove)

noncomputable def mainTr (q : M.Λ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (l, r)) =>
    match M.δ q r with
    | none => outTr M o
    | some (q', TM0.Stmt.write b) =>
      some ((Tag.main, q', default), some (Sum.inr (l, b)), TMMove.Nmove)
    | some (q', TM0.Stmt.move Dir.right) =>
      some ((Tag.fw, q', l), some (Sum.inr (r, r)), TMMove.Rmove)
    | some (q', TM0.Stmt.move Dir.left) =>
      some ((Tag.fwr, q', r), some (Sum.inr (l, l)), TMMove.Rmove)
  | _ => none

noncomputable def fwTr (q : M.Λ) (c : M.Γ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (l, r)) => some ((Tag.fw, q, l), some (Sum.inr (c, r)), TMMove.Rmove)
  | none => some ((Tag.bw, q, default), some (Sum.inr (c, default)), TMMove.Nmove)
  | _ => none

noncomputable def bwTr (q : M.Λ) (c : M.Γ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (l, r)) => some ((Tag.bw, q, r), some (Sum.inr (l, c)), TMMove.Lmove)
  | some (Sum.inl _) => some ((Tag.main, q, default), none, TMMove.Rmove)
  | none => none

noncomputable def fwrTr (q : M.Λ) (c : M.Γ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (l, r)) => some ((Tag.fwr, q, r), some (Sum.inr (l, c)), TMMove.Rmove)
  | none => some ((Tag.bwl, q, default), some (Sum.inr (default, c)), TMMove.Nmove)
  | _ => none

noncomputable def bwlTr (q : M.Λ) (c : M.Γ) (o : Option (Sy M)) : Option (Tr M) :=
  match o with
  | some (Sum.inr (l, r)) => some ((Tag.bwl, q, l), some (Sum.inr (c, r)), TMMove.Lmove)
  | some (Sum.inl _) => some ((Tag.main, q, default), none, TMMove.Rmove)
  | none => none

/-- The transition function of the simulating machine. -/
noncomputable def δm : St M → Option (Sy M) → Option (Tr M)
  | (Tag.i0, _, _), _ => some ((Tag.i1, default, default), none, TMMove.Rmove)
  | (Tag.i1, _, _), o => i1Tr M o
  | (Tag.i2, _, _), o => i2Tr M o
  | (Tag.ret, q, _), o => retTr M q o
  | (Tag.main, q, _), o => mainTr M q o
  | (Tag.fw, q, c), o => fwTr M q c o
  | (Tag.bw, q, c), o => bwTr M q c o
  | (Tag.fwr, q, c), o => fwrTr M q c o
  | (Tag.bwl, q, c), o => bwlTr M q c o
  | (Tag.out, _, _), o => outTr M o
  | (Tag.done, _, _), _ => none

def hltm (s : St M) : Bool := decide (s.1 = Tag.done)

/-- The simulating machine. -/
noncomputable abbrev FM : FlatTM :=
  mach (encY M) (sigOf M) (δm M) (hltm M) (Tag.i0, default, default)

/-- A configuration: the state, the head and the cells. -/
noncomputable def C (s : St M) (h : ℕ) (cells : List (Sy M)) : FlatTMConfig :=
  ⟨encS s, [([], h, cells.map (encY M))]⟩

def mvh : TMMove → ℕ → ℕ
  | TMMove.Lmove, h => h - 1
  | TMMove.Rmove, h => h + 1
  | TMMove.Nmove, h => h

theorem stepC_mid (s : St M) (c : Sy M) (A Bs : List (Sy M)) (s' : St M) (w : Option (Sy M))
    (mv : TMMove) (hδ : δm M s (some c) = some (s', w, mv)) (hs : s.1 ≠ Tag.done) :
    Steps (FM M) 1 (C M s A.length (A ++ c :: Bs))
      (C M s' (mvh mv A.length) (A ++ w.getD c :: Bs)) := by
  refine Steps.step ?_ ?_ (Steps.refl _)
  · unfold C
    rw [mach_halting]
    simp [hltm, hs]
  · have hcur : currentTapeSymbol (([] : List ℕ), A.length, (A ++ c :: Bs).map (encY M)) =
        (some c).map (encY M) := by
      rw [List.map_append, List.map_cons]
      have h0 := cur_mid [] (A.map (encY M)) (encY M c) (Bs.map (encY M))
      rwa [List.length_map] at h0
    unfold C
    rw [mach_step (encY M) (sigOf M) (δm M) (hltm M) _ (encY_inj M) s (some c) (s', w, mv) hδ _
      hcur]
    cases w with
    | none => cases mv <;> rfl
    | some y =>
      have hw := wr_mid [] (A.map (encY M)) (encY M c) (encY M y) (Bs.map (encY M))
      rw [List.length_map] at hw
      simp only [tapeStep, Option.map_some, List.map_append, List.map_cons, hw, Option.getD_some]
      cases mv <;> rfl

theorem stepC_end (s : St M) (A : List (Sy M)) (s' : St M) (y : Sy M)
    (mv : TMMove) (hδ : δm M s none = some (s', some y, mv)) (hs : s.1 ≠ Tag.done) :
    Steps (FM M) 1 (C M s A.length A) (C M s' (mvh mv A.length) (A ++ [y])) := by
  refine Steps.step ?_ ?_ (Steps.refl _)
  · unfold C
    rw [mach_halting]
    simp [hltm, hs]
  · have hcur : currentTapeSymbol (([] : List ℕ), A.length, A.map (encY M)) =
        (none : Option (Sy M)).map (encY M) := by
      have h0 := cur_end [] (A.map (encY M))
      rwa [List.length_map] at h0
    unfold C
    rw [mach_step (encY M) (sigOf M) (δm M) (hltm M) _ (encY_inj M) s none (s', some y, mv) hδ _
      hcur]
    have hw := wr_end [] (A.map (encY M)) (encY M y)
    rw [List.length_map] at hw
    simp only [tapeStep, Option.map_some, List.map_append, List.map_cons, List.map_nil, hw]
    cases mv <;> rfl

/-! ### The sweeps -/

theorem fw_sweep (q : M.Λ) : ∀ (Bs : List (M.Γ × M.Γ)) (A : List (Sy M)) (c : M.Γ),
    ∃ B' : List (M.Γ × M.Γ),
      Steps (FM M) (Bs.length + 1) (C M (Tag.fw, q, c) A.length (A ++ Bs.map Sum.inr))
        (C M (Tag.bw, q, default) (A.length + Bs.length) (A ++ B'.map Sum.inr)) ∧
      B'.map Prod.fst = c :: Bs.map Prod.fst ∧ B'.map Prod.snd = Bs.map Prod.snd ++ [default] := by
  intro Bs
  induction Bs with
  | nil =>
    intro A c
    refine ⟨[(c, default)], ?_, rfl, rfl⟩
    simpa [mvh] using stepC_end M (Tag.fw, q, c) A _ _ _ rfl (by simp)
  | cons p Bs ih =>
    intro A c
    obtain ⟨l, r⟩ := p
    obtain ⟨B', h2, hf, hs⟩ := ih (A ++ [Sum.inr (c, r)]) l
    have h1 := stepC_mid M (Tag.fw, q, c) (Sum.inr (l, r)) A (Bs.map Sum.inr) _ _ _ rfl
      (by simp)
    refine ⟨(c, r) :: B', ?_, by simp [hf], by simp [hs]⟩
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append] at h2
    have e : A.length + (0 + 1) + Bs.length = A.length + (Bs.length + 1) := by omega
    rw [e] at h2
    exact (h1.trans h2).cast (by simp only [List.length_cons]; omega)


theorem bw_sweep (q : M.Λ) : ∀ (X : List (M.Γ × M.Γ)) (Y : List (Sy M)) (c : M.Γ),
    ∃ X' : List (M.Γ × M.Γ),
      Steps (FM M) (X.length + 1) (C M (Tag.bw, q, c) X.length (W M :: (X.map Sum.inr ++ Y)))
        (C M (Tag.main, q, default) 1 (W M :: (X'.map Sum.inr ++ Y))) ∧
      X'.map Prod.fst = X.map Prod.fst ∧ X'.map Prod.snd = (X.map Prod.snd ++ [c]).tail := by
  intro X
  induction X using List.reverseRecOn with
  | nil =>
    intro Y c
    refine ⟨[], ?_, rfl, rfl⟩
    simpa [mvh] using stepC_mid M (Tag.bw, q, c) (W M) [] Y _ _ _ rfl (by simp)
  | append_singleton X p ih =>
    intro Y c
    obtain ⟨l, r⟩ := p
    obtain ⟨X', h2, hf, hs⟩ := ih (Sum.inr (l, c) :: Y) r
    have h1 := stepC_mid M (Tag.bw, q, c) (Sum.inr (l, r)) (W M :: X.map Sum.inr) Y _ _ _ rfl
      (by simp)
    refine ⟨X' ++ [(l, c)], ?_, by simp [hf], ?_⟩
    · have h1' : Steps (FM M) 1
          (C M (Tag.bw, q, c) (X ++ [(l, r)]).length
            (W M :: ((X ++ [(l, r)]).map Sum.inr ++ Y)))
          (C M (Tag.bw, q, r) X.length (W M :: (X.map Sum.inr ++ Sum.inr (l, c) :: Y))) := by
        simpa [mvh] using h1
      have h2' : Steps (FM M) (X.length + 1)
          (C M (Tag.bw, q, r) X.length (W M :: (X.map Sum.inr ++ Sum.inr (l, c) :: Y)))
          (C M (Tag.main, q, default) 1 (W M :: ((X' ++ [(l, c)]).map Sum.inr ++ Y))) := by
        simpa using h2
      exact (h1'.trans h2').cast (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
    · rw [List.map_append, hs, List.map_append]
      exact (List.tail_append_of_ne_nil (by simp)).symm

theorem fwr_sweep (q : M.Λ) : ∀ (Bs : List (M.Γ × M.Γ)) (A : List (Sy M)) (c : M.Γ),
    ∃ B' : List (M.Γ × M.Γ),
      Steps (FM M) (Bs.length + 1) (C M (Tag.fwr, q, c) A.length (A ++ Bs.map Sum.inr))
        (C M (Tag.bwl, q, default) (A.length + Bs.length) (A ++ B'.map Sum.inr)) ∧
      B'.map Prod.snd = c :: Bs.map Prod.snd ∧ B'.map Prod.fst = Bs.map Prod.fst ++ [default] := by
  intro Bs
  induction Bs with
  | nil =>
    intro A c
    refine ⟨[(default, c)], ?_, rfl, rfl⟩
    simpa [mvh] using stepC_end M (Tag.fwr, q, c) A _ _ _ rfl (by simp)
  | cons p Bs ih =>
    intro A c
    obtain ⟨l, r⟩ := p
    obtain ⟨B', h2, hf, hs⟩ := ih (A ++ [Sum.inr (l, c)]) r
    have h1 := stepC_mid M (Tag.fwr, q, c) (Sum.inr (l, r)) A (Bs.map Sum.inr) _ _ _ rfl
      (by simp)
    refine ⟨(l, c) :: B', ?_, by simp [hf], by simp [hs]⟩
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append] at h2
    have e : A.length + (0 + 1) + Bs.length = A.length + (Bs.length + 1) := by omega
    rw [e] at h2
    exact (h1.trans h2).cast (by simp only [List.length_cons]; omega)

theorem bwl_sweep (q : M.Λ) : ∀ (X : List (M.Γ × M.Γ)) (Y : List (Sy M)) (c : M.Γ),
    ∃ X' : List (M.Γ × M.Γ),
      Steps (FM M) (X.length + 1) (C M (Tag.bwl, q, c) X.length (W M :: (X.map Sum.inr ++ Y)))
        (C M (Tag.main, q, default) 1 (W M :: (X'.map Sum.inr ++ Y))) ∧
      X'.map Prod.snd = X.map Prod.snd ∧ X'.map Prod.fst = (X.map Prod.fst ++ [c]).tail := by
  intro X
  induction X using List.reverseRecOn with
  | nil =>
    intro Y c
    refine ⟨[], ?_, rfl, rfl⟩
    simpa [mvh] using stepC_mid M (Tag.bwl, q, c) (W M) [] Y _ _ _ rfl (by simp)
  | append_singleton X p ih =>
    intro Y c
    obtain ⟨l, r⟩ := p
    obtain ⟨X', h2, hf, hs⟩ := ih (Sum.inr (c, r) :: Y) l
    have h1 := stepC_mid M (Tag.bwl, q, c) (Sum.inr (l, r)) (W M :: X.map Sum.inr) Y _ _ _ rfl
      (by simp)
    refine ⟨X' ++ [(c, r)], ?_, by simp [hf], ?_⟩
    · have h1' : Steps (FM M) 1
          (C M (Tag.bwl, q, c) (X ++ [(l, r)]).length
            (W M :: ((X ++ [(l, r)]).map Sum.inr ++ Y)))
          (C M (Tag.bwl, q, l) X.length (W M :: (X.map Sum.inr ++ Sum.inr (c, r) :: Y))) := by
        simpa [mvh] using h1
      have h2' : Steps (FM M) (X.length + 1)
          (C M (Tag.bwl, q, l) X.length (W M :: (X.map Sum.inr ++ Sum.inr (c, r) :: Y)))
          (C M (Tag.main, q, default) 1 (W M :: ((X' ++ [(c, r)]).map Sum.inr ++ Y))) := by
        simpa using h2
      exact (h1'.trans h2').cast (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
    · rw [List.map_append, hs, List.map_append]
      exact (List.tail_append_of_ne_nil (by simp)).symm

theorem ret_sweep (q : M.Λ) : ∀ (X : List (M.Γ × M.Γ)) (Y : List (Sy M)),
    Steps (FM M) (X.length + 1) (C M (Tag.ret, q, default) X.length (W M :: (X.map Sum.inr ++ Y)))
      (C M (Tag.main, q, default) 1 (W M :: (X.map Sum.inr ++ Y))) := by
  intro X
  induction X using List.reverseRecOn with
  | nil =>
    intro Y
    simpa [mvh] using stepC_mid M (Tag.ret, q, default) (W M) [] Y _ _ _ rfl (by simp)
  | append_singleton X p ih =>
    intro Y
    have h2 := ih (Sum.inr p :: Y)
    have h1 := stepC_mid M (Tag.ret, q, default) (Sum.inr p) (W M :: X.map Sum.inr) Y _ _ _ rfl
      (by simp)
    have h1' : Steps (FM M) 1
        (C M (Tag.ret, q, default) (X ++ [p]).length (W M :: ((X ++ [p]).map Sum.inr ++ Y)))
        (C M (Tag.ret, q, default) X.length (W M :: (X.map Sum.inr ++ Sum.inr p :: Y))) := by
      simpa [mvh] using h1
    have h2' : Steps (FM M) (X.length + 1)
        (C M (Tag.ret, q, default) X.length (W M :: (X.map Sum.inr ++ Sum.inr p :: Y)))
        (C M (Tag.main, q, default) 1 (W M :: ((X ++ [p]).map Sum.inr ++ Y))) := by
      simpa using h2
    exact (h1'.trans h2').cast (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)

/-! ### One simulated step -/

theorem mk_append_blank (l : List M.Γ) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n default) = ListBlank.mk l :=
  (Quotient.sound' (Or.inl ⟨n, rfl⟩)).symm

/-- The simulated tape the pairs stand for. -/
noncomputable def tapeOf (ps : List (M.Γ × M.Γ)) : Tape M.Γ :=
  Tape.mk' (ListBlank.mk (ps.map Prod.fst)) (ListBlank.mk (ps.map Prod.snd))

theorem tm0_step_eq (q : M.Λ) (T : Tape M.Γ) (p : Option (M.Λ × TM0.Stmt M.Γ))
    (hδ : M.δ q T.head = p) :
    TM0.step M.δ ⟨q, T⟩ =
      p.map fun x => ⟨x.1, match x.2 with
        | TM0.Stmt.move dir => T.move dir
        | TM0.Stmt.write a => T.write a⟩ := by
  subst hδ
  show Option.map _ (M.δ q T.head) = _
  congr 1
  funext x
  obtain ⟨q', a⟩ := x
  cases a <;> rfl

theorem sim_step (q : M.Λ) (ps : List (M.Γ × M.Γ)) (hps : ps ≠ []) (c' : TM0.Cfg M.Γ M.Λ)
    (h : TM0.step M.δ ⟨q, tapeOf M ps⟩ = some c') :
    ∃ (N : ℕ) (ps' : List (M.Γ × M.Γ)),
      Steps (FM M) N (C M (Tag.main, q, default) 1 (W M :: ps.map Sum.inr))
        (C M (Tag.main, c'.q, default) 1 (W M :: ps'.map Sum.inr)) ∧
      c'.Tape = tapeOf M ps' ∧ ps' ≠ [] ∧ ps'.length ≤ ps.length + 1 ∧
      N ≤ 2 * ps.length + 3 := by
  cases ps with
  | nil => exact absurd rfl hps
  | cons p rest =>
    obtain ⟨l, r⟩ := p
    have hhead : (tapeOf M ((l, r) :: rest)).head = r := by
      unfold tapeOf
      rw [Tape.mk'_head, ListBlank.head_mk]
      rfl
    cases hδ : M.δ q r with
    | none =>
      rw [tm0_step_eq M q _ none (by rw [hhead]; exact hδ)] at h
      exact absurd h (by simp)
    | some x =>
      obtain ⟨q', a⟩ := x
      rw [tm0_step_eq M q _ (some (q', a)) (by rw [hhead]; exact hδ)] at h
      cases a with
      | write b =>
        have e : (⟨q', (tapeOf M ((l, r) :: rest)).write b⟩ : TM0.Cfg M.Γ M.Λ) = c' :=
          Option.some.inj h
        subst e
        have hδm : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
            some ((Tag.main, q', default), some (Sum.inr (l, b)), TMMove.Nmove) := by
          have e0 : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
              mainTr M q (some (Sum.inr (l, r))) := rfl
          rw [e0]
          simp only [mainTr, hδ]
        have h1 := stepC_mid M (Tag.main, q, default) (Sum.inr (l, r)) [W M]
          (rest.map Sum.inr) _ _ _ hδm (by simp)
        refine ⟨1, (l, b) :: rest, by simpa [mvh] using h1, ?_, by simp, by simp, by omega⟩
        show (tapeOf M ((l, r) :: rest)).write b = tapeOf M ((l, b) :: rest)
        unfold tapeOf
        rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]
        rfl
      | move dir =>
        cases dir with
        | right =>
          have e : (⟨q', (tapeOf M ((l, r) :: rest)).move Dir.right⟩ : TM0.Cfg M.Γ M.Λ) = c' :=
            Option.some.inj h
          subst e
          have hδm : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
              some ((Tag.fw, q', l), some (Sum.inr (r, r)), TMMove.Rmove) := by
            have e0 : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
                mainTr M q (some (Sum.inr (l, r))) := rfl
            rw [e0]
            simp only [mainTr, hδ]
          have h1 := stepC_mid M (Tag.main, q, default) (Sum.inr (l, r)) [W M]
            (rest.map Sum.inr) _ _ _ hδm (by simp)
          obtain ⟨B', h2, hf2, hs2⟩ := fw_sweep M q' rest [W M, Sum.inr (r, r)] l
          obtain ⟨X', h3, hf3, hs3⟩ := bw_sweep M q' ((r, r) :: B') [] default
          have hB : B'.length = rest.length + 1 := by
            have := congrArg List.length hf2
            simpa using this
          have hX : X'.length = rest.length + 2 := by
            have := congrArg List.length hf3
            simp only [List.length_map, List.length_cons] at this
            omega
          have h1' : Steps (FM M) 1
              (C M (Tag.main, q, default) 1 (W M :: ((l, r) :: rest).map Sum.inr))
              (C M (Tag.fw, q', l) [W M, Sum.inr (r, r)].length
                ([W M, Sum.inr (r, r)] ++ rest.map Sum.inr)) := by
            simpa [mvh] using h1
          have h3' : Steps (FM M) (rest.length + 3)
              (C M (Tag.bw, q', default) ([W M, Sum.inr (r, r)].length + rest.length)
                ([W M, Sum.inr (r, r)] ++ B'.map Sum.inr))
              (C M (Tag.main, q', default) 1 (W M :: X'.map Sum.inr)) := by
            have e1 : [W M, Sum.inr (r, r)].length + rest.length = ((r, r) :: B').length := by
              simp only [List.length_cons, List.length_nil, hB]; omega
            rw [e1]
            have e2 : ((r, r) :: B').length + 1 = rest.length + 3 := by
              simp only [List.length_cons, hB]
            have h3c := h3.cast e2
            simpa using h3c
          refine ⟨_, X', (h1'.trans h2).trans h3', ?_, ?_, ?_, ?_⟩
          · show (tapeOf M ((l, r) :: rest)).move Dir.right = tapeOf M X'
            unfold tapeOf
            rw [Tape.move_right_mk', ListBlank.tail_mk, ListBlank.head_mk, ListBlank.cons_mk,
              hf3, hs3]
            simp only [List.map_cons, hf2, hs2, List.headI, List.tail_cons, List.cons_append,
              List.append_assoc]
            exact congrArg _ (mk_append_blank M (rest.map Prod.snd) 2).symm
          · intro hnil
            rw [hnil] at hX
            simp at hX
          · rw [hX]; simp only [List.length_cons]; omega
          · simp only [List.length_cons]; omega
        | left =>
          have e : (⟨q', (tapeOf M ((l, r) :: rest)).move Dir.left⟩ : TM0.Cfg M.Γ M.Λ) = c' :=
            Option.some.inj h
          subst e
          have hδm : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
              some ((Tag.fwr, q', r), some (Sum.inr (l, l)), TMMove.Rmove) := by
            have e0 : δm M (Tag.main, q, default) (some (Sum.inr (l, r))) =
                mainTr M q (some (Sum.inr (l, r))) := rfl
            rw [e0]
            simp only [mainTr, hδ]
          have h1 := stepC_mid M (Tag.main, q, default) (Sum.inr (l, r)) [W M]
            (rest.map Sum.inr) _ _ _ hδm (by simp)
          obtain ⟨B', h2, hs2, hf2⟩ := fwr_sweep M q' rest [W M, Sum.inr (l, l)] r
          obtain ⟨X', h3, hs3, hf3⟩ := bwl_sweep M q' ((l, l) :: B') [] default
          have hB : B'.length = rest.length + 1 := by
            have := congrArg List.length hs2
            simpa using this
          have hX : X'.length = rest.length + 2 := by
            have := congrArg List.length hs3
            simp only [List.length_map, List.length_cons] at this
            omega
          have h1' : Steps (FM M) 1
              (C M (Tag.main, q, default) 1 (W M :: ((l, r) :: rest).map Sum.inr))
              (C M (Tag.fwr, q', r) [W M, Sum.inr (l, l)].length
                ([W M, Sum.inr (l, l)] ++ rest.map Sum.inr)) := by
            simpa [mvh] using h1
          have h3' : Steps (FM M) (rest.length + 3)
              (C M (Tag.bwl, q', default) ([W M, Sum.inr (l, l)].length + rest.length)
                ([W M, Sum.inr (l, l)] ++ B'.map Sum.inr))
              (C M (Tag.main, q', default) 1 (W M :: X'.map Sum.inr)) := by
            have e1 : [W M, Sum.inr (l, l)].length + rest.length = ((l, l) :: B').length := by
              simp only [List.length_cons, List.length_nil, hB]; omega
            rw [e1]
            have e2 : ((l, l) :: B').length + 1 = rest.length + 3 := by
              simp only [List.length_cons, hB]
            have h3c := h3.cast e2
            simpa using h3c
          refine ⟨_, X', (h1'.trans h2).trans h3', ?_, ?_, ?_, ?_⟩
          · show (tapeOf M ((l, r) :: rest)).move Dir.left = tapeOf M X'
            unfold tapeOf
            rw [Tape.move_left_mk', ListBlank.tail_mk, ListBlank.head_mk, ListBlank.cons_mk,
              hf3, hs3]
            simp only [List.map_cons, hf2, hs2, List.headI, List.tail_cons, List.cons_append,
              List.append_assoc]
            exact congrArg (fun z => Tape.mk' z _) (mk_append_blank M (rest.map Prod.fst) 2).symm
          · intro hnil
            rw [hnil] at hX
            simp at hX
          · rw [hX]; simp only [List.length_cons]; omega
          · simp only [List.length_cons]; omega


/-! ### The whole run -/

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem sim_run : ∀ (k : ℕ) (q : M.Λ) (ps : List (M.Γ × M.Γ)) (c' : TM0.Cfg M.Γ M.Λ), ps ≠ [] →
    (flip bind (TM0.step M.δ))^[k] (some ⟨q, tapeOf M ps⟩) = some c' →
    ∃ (N : ℕ) (ps' : List (M.Γ × M.Γ)),
      Steps (FM M) N (C M (Tag.main, q, default) 1 (W M :: ps.map Sum.inr))
        (C M (Tag.main, c'.q, default) 1 (W M :: ps'.map Sum.inr)) ∧
      c'.Tape = tapeOf M ps' ∧ ps' ≠ [] ∧ ps'.length ≤ ps.length + k ∧
      N ≤ k * (2 * (ps.length + k) + 3) := by
  intro k
  induction k with
  | zero =>
    intro q ps c' hps h
    have h' : (⟨q, tapeOf M ps⟩ : TM0.Cfg M.Γ M.Λ) = c' := Option.some.inj h
    subst h'
    exact ⟨0, ps, Steps.refl _, rfl, hps, Nat.le_refl _, Nat.zero_le _⟩
  | succ k ih =>
    intro q ps c' hps h
    rw [Function.iterate_succ_apply] at h
    cases hs : TM0.step M.δ ⟨q, tapeOf M ps⟩ with
    | none =>
      have e : flip bind (TM0.step M.δ) (some ⟨q, tapeOf M ps⟩) = none := hs
      rw [e, iterate_none] at h
      exact absurd h (by simp)
    | some c1 =>
      have e : flip bind (TM0.step M.δ) (some ⟨q, tapeOf M ps⟩) = some c1 := hs
      rw [e] at h
      obtain ⟨N1, ps1, hst, ht, hne, hlen, hN1⟩ := sim_step M q ps hps c1 hs
      obtain ⟨q1, T1⟩ := c1
      change T1 = tapeOf M ps1 at ht
      subst ht
      obtain ⟨N2, ps2, hr, ht2, hne2, hlen2, hN2⟩ := ih q1 ps1 c' hne h
      refine ⟨N1 + N2, ps2, hst.trans hr, ht2, hne2, by omega, ?_⟩
      have hmono : k * (2 * (ps1.length + k) + 3) ≤ k * (2 * (ps.length + (k + 1)) + 3) :=
        Nat.mul_le_mul_left k (by omega)
      have hexp : (k + 1) * (2 * (ps.length + (k + 1)) + 3) =
          k * (2 * (ps.length + (k + 1)) + 3) + (2 * (ps.length + (k + 1)) + 3) := by ring
      omega

theorem enc_code (b : Bool) :
    encY M (Sum.inl (if b then 2 else 1)) = if b then 2 else 1 := by
  cases b <;> rfl

theorem init_tape (x : List Bool) :
    (W M :: ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
      [Sum.inl 0, Sum.inl 3])).map (encY M) = CookLevin.stringTape x := by
  simp [CookLevin.stringTape, CookLevin.symbolsOf, encY, List.map_map, Function.comp_def]

theorem i1_code (b : Bool) :
    δm M (Tag.i1, default, default) (some (Sum.inl (if b then 2 else 1))) =
      some ((Tag.i1, default, default), some (Sum.inr (default, M.inp b)), TMMove.Rmove) := by
  cases b <;> rfl

theorem i1_loop : ∀ (xs : List Bool) (A Z : List (Sy M)),
    Steps (FM M) xs.length
      (C M (Tag.i1, default, default) A.length
        (A ++ (xs.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Z))
      (C M (Tag.i1, default, default) (A.length + xs.length)
        (A ++ (xs.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++ Z)) := by
  intro xs
  induction xs with
  | nil => intro A Z; exact Steps.refl _
  | cons b xs ih =>
    intro A Z
    have h1 := stepC_mid M (Tag.i1, default, default) (Sum.inl (if b then 2 else 1)) A
      ((xs.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Z) _ _ _ (i1_code M b)
      (by simp)
    have h2 := ih (A ++ [Sum.inr (default, M.inp b)]) Z
    have e1 : (A ++ [(Sum.inr (default, M.inp b) : Sy M)]).length + xs.length =
        A.length + (b :: xs).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [e1] at h2
    have h1' : Steps (FM M) 1
        (C M (Tag.i1, default, default) A.length
          (A ++ ((b :: xs).map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Z))
        (C M (Tag.i1, default, default) (A ++ [(Sum.inr (default, M.inp b) : Sy M)]).length
          (A ++ [Sum.inr (default, M.inp b)] ++
            (xs.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Z)) := by
      simpa [mvh] using h1
    have h2' : Steps (FM M) xs.length
        (C M (Tag.i1, default, default) (A ++ [(Sum.inr (default, M.inp b) : Sy M)]).length
          (A ++ [Sum.inr (default, M.inp b)] ++
            (xs.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Z))
        (C M (Tag.i1, default, default) (A.length + (b :: xs).length)
          (A ++ ((b :: xs).map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++ Z)) := by
      simpa using h2
    exact (h1'.trans h2').cast (by
      simp only [List.length_cons]
      omega)

theorem init_run (x : List Bool) :
    Steps (FM M) (2 * x.length + 5) (initFlatConfig (FM M) [CookLevin.stringTape x])
      (C M (Tag.main, default, default) 1
        (W M :: (x.map (fun b => ((default : M.Γ), M.inp b)) ++
          [(default, default), (default, default)]).map Sum.inr)) := by
  have e0 : initFlatConfig (FM M) [CookLevin.stringTape x] =
      C M (Tag.i0, default, default) 0
        (W M :: ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3])) := by
    unfold C
    rw [init_tape]
    rfl
  rw [e0]
  have h1 := stepC_mid M (Tag.i0, default, default) (W M) []
    ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ [Sum.inl 0, Sum.inl 3]) _ _ _ rfl
    (by simp)
  have h2 := i1_loop M x [W M] [Sum.inl 0, Sum.inl 3]
  have h3 := stepC_mid M (Tag.i1, default, default) (Sum.inl 0)
    (W M :: x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) [Sum.inl 3] _ _ _ rfl (by simp)
  have h4 := stepC_mid M (Tag.i2, default, default) (Sum.inl 3)
    (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
      [Sum.inr (default, default)])) [] _ _ _ rfl (by simp)
  have h5 := ret_sweep M default
    (x.map (fun b => ((default : M.Γ), M.inp b)) ++ [(default, default)])
    [Sum.inr (default, default)]
  have h1' : Steps (FM M) 1
      (C M (Tag.i0, default, default) 0
        (W M :: ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3])))
      (C M (Tag.i1, default, default) 1
        (W M :: ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3]))) := by
    simpa [mvh] using h1
  have h2' : Steps (FM M) x.length
      (C M (Tag.i1, default, default) 1
        (W M :: ((x.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3])))
      (C M (Tag.i1, default, default) (x.length + 1)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3]))) := by
    simpa [Nat.add_comm] using h2
  have h3' : Steps (FM M) 1
      (C M (Tag.i1, default, default) (x.length + 1)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inl 0, Sum.inl 3])))
      (C M (Tag.i2, default, default) (x.length + 2)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inr (default, default), Sum.inl 3]))) := by
    simpa [mvh] using h3
  have h4' : Steps (FM M) 1
      (C M (Tag.i2, default, default) (x.length + 2)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inr (default, default), Sum.inl 3])))
      (C M (Tag.ret, default, default) (x.length + 1)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inr (default, default), Sum.inr (default, default)]))) := by
    simpa [mvh] using h4
  have h5' : Steps (FM M) (x.length + 2)
      (C M (Tag.ret, default, default) (x.length + 1)
        (W M :: ((x.map fun b => (Sum.inr (default, M.inp b) : Sy M)) ++
          [Sum.inr (default, default), Sum.inr (default, default)])))
      (C M (Tag.main, default, default) 1
        (W M :: (x.map (fun b => ((default : M.Γ), M.inp b)) ++
          [(default, default), (default, default)]).map Sum.inr)) := by
    simpa [List.map_map, Function.comp_def] using h5
  exact ((((h1'.trans h2').trans h3').trans h4').trans h5').cast (by omega)

theorem out_run : ∀ (w : List Bool) (s : St M) (A : List (Sy M)) (ps : List (M.Γ × M.Γ))
    (rest : List M.Γ), s.1 ≠ Tag.done →
    (∀ o, o = (ps.map (Sum.inr : M.Γ × M.Γ → Sy M)).head? → δm M s o = outTr M o) →
    ps.map Prod.snd = w.map M.out ++ rest → (∀ b, rest.head? ≠ some (M.out b)) →
    ∃ tl : List (Sy M), Steps (FM M) (w.length + 1) (C M s A.length (A ++ ps.map Sum.inr))
      (C M (Tag.done, default, default) (A.length + w.length)
        (A ++ (w.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++ Sum.inl 0 :: tl)) := by
  intro w
  induction w with
  | nil =>
    intro s A ps rest hs hso hsnd hrest
    cases ps with
    | nil =>
      refine ⟨[], ?_⟩
      have hδ : δm M s none =
          some ((Tag.done, default, default), some (Sum.inl 0), TMMove.Nmove) := by
        rw [hso none rfl]
        rfl
      simpa [mvh] using stepC_end M s A _ _ _ hδ hs
    | cons p t =>
      obtain ⟨l, r⟩ := p
      have hr : rest.head? = some r := by
        have h0 := congrArg List.head? hsnd
        simpa using h0.symm
      have h1 : r ≠ M.out true := fun e => hrest true (by rw [hr, e])
      have h2 : r ≠ M.out false := fun e => hrest false (by rw [hr, e])
      have hδ : δm M s (some (Sum.inr (l, r))) =
          some ((Tag.done, default, default), some (Sum.inl 0), TMMove.Nmove) := by
        have e := hso (some (Sum.inr (l, r))) rfl
        rw [e]
        simp [outTr, h1, h2]
      refine ⟨t.map Sum.inr, ?_⟩
      simpa [mvh] using stepC_mid M s (Sum.inr (l, r)) A (t.map Sum.inr) _ _ _ hδ hs
  | cons b w ih =>
    intro s A ps rest hs hso hsnd hrest
    cases ps with
    | nil => exact absurd hsnd (by simp)
    | cons p t =>
      obtain ⟨l, r⟩ := p
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hsnd
      obtain ⟨hr, ht⟩ := hsnd
      subst hr
      have hδ : δm M s (some (Sum.inr (l, M.out b))) =
          some ((Tag.out, default, default), some (Sum.inl (if b then 2 else 1)),
            TMMove.Rmove) := by
        have e := hso (some (Sum.inr (l, M.out b))) rfl
        rw [e]
        cases b with
        | true => simp [outTr]
        | false =>
          have hne : M.out false ≠ M.out true := fun e => absurd (M.out_injective e) (by simp)
          simp [outTr, hne]
      obtain ⟨tl, h2⟩ := ih (Tag.out, default, default)
        (A ++ [Sum.inl (if b then 2 else 1)]) t rest (by simp) (fun o _ => rfl) ht hrest
      have h1 := stepC_mid M s (Sum.inr (l, M.out b)) A (t.map Sum.inr) _ _ _ hδ hs
      refine ⟨tl, ?_⟩
      have h1' : Steps (FM M) 1 (C M s A.length (A ++ ((l, M.out b) :: t).map Sum.inr))
          (C M (Tag.out, default, default)
            (A ++ [(Sum.inl (if b then 2 else 1) : Sy M)]).length
            (A ++ [Sum.inl (if b then 2 else 1)] ++ t.map Sum.inr)) := by
        simpa [mvh] using h1
      have e1 : (A ++ [(Sum.inl (if b then 2 else 1) : Sy M)]).length + w.length =
          A.length + (b :: w).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [e1] at h2
      have h2' : Steps (FM M) (w.length + 1)
          (C M (Tag.out, default, default)
            (A ++ [(Sum.inl (if b then 2 else 1) : Sy M)]).length
            (A ++ [Sum.inl (if b then 2 else 1)] ++ t.map Sum.inr))
          (C M (Tag.done, default, default) (A.length + (b :: w).length)
            (A ++ ((b :: w).map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
              Sum.inl 0 :: tl)) := by
        simpa using h2
      exact (h1'.trans h2').cast (by
        simp only [List.length_cons]
        omega)

/-- A right part that shows `w` is `w` followed by a rest that starts with no output letter. -/
theorem shows_split : ∀ (w : List Bool) (r : List M.Γ),
    (∀ (i : ℕ) (h : i < w.length), r.getI i = M.out (w[i]'h)) →
    (∀ b : Bool, r.getI w.length ≠ M.out b) →
    ∃ rest, r = w.map M.out ++ rest ∧ ∀ b, rest.head? ≠ some (M.out b) := by
  intro w
  induction w with
  | nil =>
    intro r _ h2
    refine ⟨r, rfl, ?_⟩
    intro b hb
    apply h2 b
    cases r with
    | nil => exact absurd hb (by simp)
    | cons x r =>
      have hx : x = M.out b := Option.some.inj hb
      rw [hx]
      exact List.getI_cons_zero _ _
  | cons b w ih =>
    intro r h1 h2
    cases r with
    | nil =>
      have h0 := h1 0 (Nat.succ_pos _)
      rw [List.getI_nil] at h0
      exact absurd h0.symm (M.out_ne_blank b)
    | cons x r =>
      have hx : x = M.out b := by
        have h0 := h1 0 (Nat.succ_pos _)
        rw [List.getI_cons_zero] at h0
        exact h0
      have h1' : ∀ (i : ℕ) (h : i < w.length), r.getI i = M.out (w[i]'h) := by
        intro i h
        have hi := h1 (i + 1) (Nat.succ_lt_succ h)
        rw [List.getI_cons_succ] at hi
        exact hi
      have h2' : ∀ b' : Bool, r.getI w.length ≠ M.out b' := by
        intro b'
        have hi := h2 b'
        rw [List.length_cons, List.getI_cons_succ] at hi
        exact hi
      obtain ⟨rest, hr, ho⟩ := ih r h1' h2'
      refine ⟨rest, ?_, ho⟩
      rw [hx, hr]
      rfl

theorem out_read (w : List Bool) (tl : List ℕ) :
    ((((w.map fun (b : Bool) => (if b then 2 else 1 : ℕ)) ++ 0 :: tl).takeWhile (· != 3)).takeWhile
      (· != 0)).map (· == 2) = w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simpa using ih

theorem map_fst_blank (x : List Bool) :
    (x.map fun b => ((default : M.Γ), M.inp b)).map Prod.fst = List.replicate x.length default := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [List.replicate_succ, ih]

theorem flat_run (x w : List Bool) (t : ℕ) (h : M.OutputsInTime x w t) :
    ∃ (N : ℕ) (cfg : FlatTMConfig),
      N ≤ 3 * x.length + 9 + t + t * (2 * (x.length + 2 + t) + 3) ∧
      Steps (FM M) N (initFlatConfig (FM M) [CookLevin.stringTape x]) cfg ∧
      haltingStateReached (FM M) cfg = true ∧ CookLevin.outputString cfg = w := by
  obtain ⟨c, ⟨ev⟩, hhalt, hshow⟩ := h
  have hps0 : ∃ ps0 : List (M.Γ × M.Γ), ps0 = x.map (fun b => ((default : M.Γ), M.inp b)) ++
      [(default, default), (default, default)] := ⟨_, rfl⟩
  obtain ⟨ps0, hps0⟩ := hps0
  have hlen0 : ps0.length = x.length + 2 := by simp [hps0]
  have hne0 : ps0 ≠ [] := by
    intro e
    rw [e] at hlen0
    simp at hlen0
  have htape0 : tapeOf M ps0 = Tape.mk₁ (x.map M.inp) := by
    unfold tapeOf Tape.mk₁ Tape.mk₂
    have e1 : ps0.map Prod.fst =
        (([] : List M.Γ) ++ List.replicate x.length default) ++ List.replicate 2 default := by
      rw [hps0, List.map_append, map_fst_blank]
      rfl
    have e2 : ps0.map Prod.snd = x.map M.inp ++ List.replicate 2 default := by
      rw [hps0, List.map_append, List.map_map]
      rfl
    rw [e1, e2, mk_append_blank, mk_append_blank, mk_append_blank]
  have hrun : (flip bind (TM0.step M.δ))^[ev.steps] (some ⟨default, tapeOf M ps0⟩) = some c := by
    rw [htape0]
    exact ev.evals_in_steps
  obtain ⟨N2, ps', hsim, htape, hne, hlen, hN2⟩ := sim_run M ev.steps default ps0 c hne0 hrun
  have hle := ev.steps_le_m
  obtain ⟨qc, Tc⟩ := c
  change Tc = tapeOf M ps' at htape
  subst htape
  have hr0 : (tapeOf M ps').right₀ = ListBlank.mk (ps'.map Prod.snd) := Tape.mk'_right₀ _ _
  have hs1 : ∀ (i : ℕ) (h : i < w.length), (ps'.map Prod.snd).getI i = M.out (w[i]'h) := by
    intro i hi
    have h0 := hshow.1 i hi
    change (tapeOf M ps').right₀.nth i = _ at h0
    rw [hr0, ListBlank.nth_mk] at h0
    exact h0
  have hs2 : ∀ b : Bool, (ps'.map Prod.snd).getI w.length ≠ M.out b := by
    intro b
    have h0 := hshow.2 b
    change (tapeOf M ps').right₀.nth w.length ≠ _ at h0
    rw [hr0, ListBlank.nth_mk] at h0
    exact h0
  obtain ⟨rest, hsnd, hrest⟩ := shows_split M w (ps'.map Prod.snd) hs1 hs2
  have hδnone : M.δ qc (tapeOf M ps').head = none := by
    have e := tm0_step_eq M qc (tapeOf M ps') _ rfl
    have hh : TM0.step M.δ ⟨qc, tapeOf M ps'⟩ = none := hhalt
    rw [e] at hh
    exact Option.map_eq_none_iff.mp hh
  have hso : ∀ o, o = (ps'.map (Sum.inr : M.Γ × M.Γ → Sy M)).head? →
      δm M (Tag.main, qc, default) o = outTr M o := by
    intro o ho
    cases ps' with
    | nil => exact absurd rfl hne
    | cons p t' =>
      obtain ⟨l, r⟩ := p
      subst ho
      have hh : (tapeOf M ((l, r) :: t')).head = r := by
        unfold tapeOf
        rw [Tape.mk'_head, ListBlank.head_mk]
        rfl
      rw [hh] at hδnone
      have e0 : δm M (Tag.main, qc, default) (some (Sum.inr (l, r))) =
          mainTr M qc (some (Sum.inr (l, r))) := rfl
      show δm M (Tag.main, qc, default) (some (Sum.inr (l, r))) = _
      rw [e0]
      simp only [mainTr, hδnone]
      rfl
  obtain ⟨tl, hout⟩ := out_run M w (Tag.main, qc, default) [W M] ps' rest (by simp) hso hsnd
    hrest
  have hinit := init_run M x
  have hsim' : Steps (FM M) N2
      (C M (Tag.main, default, default) 1
        (W M :: (x.map (fun b => ((default : M.Γ), M.inp b)) ++
          [(default, default), (default, default)]).map Sum.inr))
      (C M (Tag.main, qc, default) [W M].length ([W M] ++ ps'.map Sum.inr)) := by
    rw [← hps0]
    exact hsim
  have hwlen : w.length ≤ ps'.length := by
    have h0 := congrArg List.length hsnd
    simp only [List.length_map, List.length_append] at h0
    omega
  have hmul : ev.steps * (2 * (ps0.length + ev.steps) + 3) ≤
      t * (2 * (x.length + 2 + t) + 3) := Nat.mul_le_mul hle (by omega)
  refine ⟨_, _, ?_, (hinit.trans hsim').trans hout, ?_, ?_⟩
  · omega
  · unfold C
    rw [mach_halting]
    rfl
  · unfold C CookLevin.outputString
    have e : (([W M] ++ (w.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
        Sum.inl 0 :: tl).map (encY M)).tail =
        (w.map fun (b : Bool) => (if b then 2 else 1 : ℕ)) ++ 0 :: tl.map (encY M) := by
      simp [encY, List.map_map, Function.comp_def]
    show ((((([W M] ++ (w.map fun b => (Sum.inl (if b then 2 else 1) : Sy M)) ++
        Sum.inl 0 :: tl).map (encY M)).tail.takeWhile (· != 3)).takeWhile (· != 0)).map
          (· == 2)) = w
    rw [e]
    exact out_read w _

theorem inOPoly_eval (p : Polynomial ℕ) : inOPoly (fun n => p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using inOPoly_add hp hq
  | monomial k a =>
    have h : inOPoly (fun n => a * n ^ k) :=
      inOPoly_mul (inOPoly_const a) ⟨k, 1, 0, fun n _ => by simp⟩
    simpa [Polynomial.eval_monomial] using h

theorem flat_computes (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hM : ∀ a : List Bool, M.OutputsInTime (PvsNP.encodeString a) (PvsNP.encodeString (f a))
      (p.eval (PvsNP.encodeString a).length)) :
    ∃ (t : ℕ → ℕ) (M' : FlatTM), inOPoly t ∧ validFlatTM M' ∧ M'.tapes = 1 ∧
      CookLevin.computesInTime M' f t := by
  refine ⟨fun n => 3 * n + 9 + p.eval n + p.eval n * (2 * (n + 2 + p.eval n) + 3), FM M, ?_,
    mach_valid _ _ _ _ _ (encY_lt M), rfl, ?_⟩
  · have hp := inOPoly_eval p
    exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 3) inOPoly_id)
      (inOPoly_const 9)) hp) (inOPoly_mul hp (inOPoly_add (inOPoly_mul (inOPoly_const 2)
        (inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const 2)) hp)) (inOPoly_const 3)))
  · intro x
    obtain ⟨N, cfg, hN, hsteps, hhalt, hout⟩ := flat_run M x (f x) _ (hM x)
    refine ⟨cfg, ?_, hhalt, hout⟩
    have hrun := hsteps.run
    have hN' : N ≤ 3 * x.length + 9 + p.eval x.length +
        p.eval x.length * (2 * (x.length + 2 + p.eval x.length) + 3) := hN
    have hext := runFlatTM_extend (k := 3 * x.length + 9 + p.eval x.length +
        p.eval x.length * (2 * (x.length + 2 + p.eval x.length) + 3) - N) hrun hhalt
    rw [Nat.add_sub_cancel' hN'] at hext
    exact hext

end sim

end PvsNP.Units.m1_st_to_flat

/-- A function a single-tape machine computes in polynomial time is computed in polynomial time
by a one-tape machine of the Cook-Levin model: its cells hold pairs of simulated symbols, the
simulated tape to the left of the head and from the head rightwards. -/
theorem PvsNP.Units.m1_st_to_flat :
    ∀ f : List Bool → List Bool,
      PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        ∃ (t : ℕ → ℕ) (M : FlatTM), inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧
          CookLevin.computesInTime M f t := by
  intro f h
  obtain ⟨M, p, hM⟩ := h
  exact PvsNP.Units.m1_st_to_flat.flat_computes M f p hM
