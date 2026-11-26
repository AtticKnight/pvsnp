import Mathlib
import PvsNP.Defs
import CookLevin

/-
A one-tape machine of the vendored Cook-Levin model (a tape infinite to the right only, whose
unwritten cells differ from every symbol) simulated by a single-tape machine of the campaign
(Mathlib's TM0, a tape infinite both ways).

The simulating machine first rewrites its input as the string tape of the Cook-Levin model, with a
wall to the left of cell 0. It then follows the Cook-Levin machine step by step: the unwritten
cells are its blanks, a write on a blank cell is kept only when the cell to the left is written,
and a move to the left bounces off the wall. When the Cook-Levin machine halts, the simulating
machine walks back to cell 1 and rewrites the output in its own output letters.
-/

namespace PvsNP.Units.m1_flat_to_st

open Turing

/-- `a` as an element of `Fin (n + 1)`, cut at `n`. -/
def toFin (n a : ℕ) : Fin (n + 1) := ⟨min a n, Nat.lt_succ_of_le (Nat.min_le_right a n)⟩

theorem toFin_val {n a : ℕ} (h : a ≤ n) : (toFin n a).val = a := Nat.min_eq_left h

/-- The kinds of states of the simulating machine. -/
inductive Tag
  | i0 | i1 | i2 | i3 | i4 | i5 | i6 | rd | ft | wr | mvd | lw | o0 | o1 | o2 | o3 | o4
  deriving DecidableEq

instance : Fintype Tag where
  elems := {Tag.i0, Tag.i1, Tag.i2, Tag.i3, Tag.i4, Tag.i5, Tag.i6, Tag.rd, Tag.ft, Tag.wr,
    Tag.mvd, Tag.lw, Tag.o0, Tag.o1, Tag.o2, Tag.o3, Tag.o4}
  complete := by intro x; cases x <;> decide

instance : Inhabited Tag := ⟨Tag.i0⟩

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

section sim

variable (Mf : FlatTM)

/-- A written cell holds a number up to `Mf.sig + 3`. -/
abbrev Sym : Type := Fin (Mf.sig + 3 + 1)

/-- The tape alphabet: the blank, a written cell, an input letter, an output letter, the wall. -/
abbrev Γ₀ : Type := Option (Sym Mf ⊕ (Bool ⊕ Bool) ⊕ Unit)

/-- A state: its kind, a state of the simulated machine, a symbol to write and a move. -/
abbrev Λ₀ : Type := Tag × Fin (Mf.states + 1) × Sym Mf × Fin 3

def sy (v : ℕ) : Γ₀ Mf := some (Sum.inl (toFin (Mf.sig + 3) v))

def inpL (b : Bool) : Γ₀ Mf := some (Sum.inr (Sum.inl (Sum.inl b)))

def outL (b : Bool) : Γ₀ Mf := some (Sum.inr (Sum.inl (Sum.inr b)))

def wall : Γ₀ Mf := some (Sum.inr (Sum.inr ()))

def mvCode : TMMove → Fin 3
  | TMMove.Nmove => 0
  | TMMove.Lmove => 1
  | TMMove.Rmove => 2

/-- The table entry the simulated machine applies in state `q` on the cell content `o`. -/
def look (q : ℕ) (o : Option ℕ) : Option FlatTMTransEntry :=
  Mf.trans.find? fun e => e.src_state == q && decide (e.src_tape_vals = [o])

abbrev Act : Type := Λ₀ Mf × TM0.Stmt (Γ₀ Mf)

abbrev st0 (t : Tag) : Λ₀ Mf := (t, default, default, default)

/-- The number a cell holds. -/
def numOf (a : Γ₀ Mf) : Option ℕ :=
  match a with
  | some (Sum.inl u) => some u.val
  | _ => none

def rdTr (q : Fin (Mf.states + 1)) (a : Γ₀ Mf) : Option (Act Mf) :=
  if Mf.halt.getD q.val false = true then some (st0 Mf Tag.o0, TM0.Stmt.write a)
  else
    match look Mf q.val (numOf Mf a) with
    | none => none
    | some e =>
      match e.dst_write_vals.headD none with
      | none =>
        some ((Tag.mvd, toFin Mf.states e.dst_state, default,
          mvCode (e.move_dirs.headD TMMove.Nmove)), TM0.Stmt.write a)
      | some v =>
        match a with
        | none =>
          some ((Tag.ft, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v,
            mvCode (e.move_dirs.headD TMMove.Nmove)), TM0.Stmt.move Dir.left)
        | some _ =>
          some ((Tag.mvd, toFin Mf.states e.dst_state, default,
            mvCode (e.move_dirs.headD TMMove.Nmove)), TM0.Stmt.write (sy Mf v))

def i0Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inr (Sum.inl (Sum.inl b))) =>
    some (st0 Mf Tag.i0, TM0.Stmt.write (sy Mf (if b then 2 else 1)))
  | some (Sum.inl _) => some (st0 Mf Tag.i0, TM0.Stmt.move Dir.right)
  | none => some (st0 Mf Tag.i1, TM0.Stmt.write (sy Mf 0))
  | _ => none

def i1Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inl _) => some (st0 Mf Tag.i2, TM0.Stmt.move Dir.right)
  | _ => none

def i2Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | none => some (st0 Mf Tag.i3, TM0.Stmt.write (sy Mf 3))
  | _ => none

def i3Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inl _) => some (st0 Mf Tag.i3, TM0.Stmt.move Dir.left)
  | none => some (st0 Mf Tag.i4, TM0.Stmt.write (sy Mf 3))
  | _ => none

def i4Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inl _) => some (st0 Mf Tag.i5, TM0.Stmt.move Dir.left)
  | _ => none

def i5Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | none => some (st0 Mf Tag.i6, TM0.Stmt.write (wall Mf))
  | _ => none

def i6Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inr (Sum.inr _)) =>
    some ((Tag.rd, toFin Mf.states Mf.start, default, default), TM0.Stmt.move Dir.right)
  | _ => none

def ftTr (q : Fin (Mf.states + 1)) (v : Sym Mf) (m : Fin 3) (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | none => some ((Tag.mvd, q, default, m), TM0.Stmt.move Dir.right)
  | some _ => some ((Tag.wr, q, v, m), TM0.Stmt.move Dir.right)

def wrTr (q : Fin (Mf.states + 1)) (v : Sym Mf) (m : Fin 3) : Option (Act Mf) :=
  some ((Tag.mvd, q, default, m), TM0.Stmt.write (some (Sum.inl v)))

def mvdTr (q : Fin (Mf.states + 1)) (m : Fin 3) (a : Γ₀ Mf) : Option (Act Mf) :=
  if m = 1 then some ((Tag.lw, q, default, default), TM0.Stmt.move Dir.left)
  else if m = 2 then some ((Tag.rd, q, default, default), TM0.Stmt.move Dir.right)
  else some ((Tag.rd, q, default, default), TM0.Stmt.write a)

def lwTr (q : Fin (Mf.states + 1)) (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inr (Sum.inr _)) => some ((Tag.rd, q, default, default), TM0.Stmt.move Dir.right)
  | _ => some ((Tag.rd, q, default, default), TM0.Stmt.write a)

def o0Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inr (Sum.inr _)) => some (st0 Mf Tag.o1, TM0.Stmt.move Dir.right)
  | _ => some (st0 Mf Tag.o0, TM0.Stmt.move Dir.left)

def o2Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inl u) =>
    if u.val = 0 ∨ u.val = 3 then some (st0 Mf Tag.o3, TM0.Stmt.move Dir.left)
    else some (st0 Mf Tag.o2, TM0.Stmt.write (outL Mf (u.val == 2)))
  | some (Sum.inr (Sum.inl (Sum.inr _))) => some (st0 Mf Tag.o2, TM0.Stmt.move Dir.right)
  | _ => some (st0 Mf Tag.o3, TM0.Stmt.move Dir.left)

def o3Tr (a : Γ₀ Mf) : Option (Act Mf) :=
  match a with
  | some (Sum.inr (Sum.inl (Sum.inr _))) => some (st0 Mf Tag.o3, TM0.Stmt.move Dir.left)
  | _ => some (st0 Mf Tag.o4, TM0.Stmt.move Dir.right)

/-- The transition function of the simulating machine. -/
def δ₀ : Λ₀ Mf → Γ₀ Mf → Option (Act Mf)
  | (Tag.i0, _, _, _), a => i0Tr Mf a
  | (Tag.i1, _, _, _), a => i1Tr Mf a
  | (Tag.i2, _, _, _), a => i2Tr Mf a
  | (Tag.i3, _, _, _), a => i3Tr Mf a
  | (Tag.i4, _, _, _), a => i4Tr Mf a
  | (Tag.i5, _, _, _), a => i5Tr Mf a
  | (Tag.i6, _, _, _), a => i6Tr Mf a
  | (Tag.rd, q, _, _), a => rdTr Mf q a
  | (Tag.ft, q, v, m), a => ftTr Mf q v m a
  | (Tag.wr, q, v, m), _ => wrTr Mf q v m
  | (Tag.mvd, q, _, m), a => mvdTr Mf q m a
  | (Tag.lw, q, _, _), a => lwTr Mf q a
  | (Tag.o0, _, _, _), a => o0Tr Mf a
  | (Tag.o1, _, _, _), _ => some (st0 Mf Tag.o2, TM0.Stmt.move Dir.right)
  | (Tag.o2, _, _, _), a => o2Tr Mf a
  | (Tag.o3, _, _, _), a => o3Tr Mf a
  | (Tag.o4, _, _, _), _ => none

/-- The simulating machine. -/
def Mst : PvsNP.SingleTape.Machine Bool Bool where
  Γ := Γ₀ Mf
  Λ := Λ₀ Mf
  inp := inpL Mf
  out := outL Mf
  inp_injective := by
    intro a b h
    simpa [inpL] using h
  out_injective := by
    intro a b h
    simpa [outL] using h
  inp_ne_blank := fun _ => Option.some_ne_none _
  out_ne_blank := fun _ => Option.some_ne_none _
  δ := δ₀ Mf

/-- `n` steps of the simulating machine lead from `c` to `c'`. -/
def Reach (n : ℕ) (c c' : TM0.Cfg (Γ₀ Mf) (Λ₀ Mf)) : Prop :=
  (flip bind (TM0.step (δ₀ Mf)))^[n] (some c) = some c'

variable {Mf}

theorem Reach.refl (c : TM0.Cfg (Γ₀ Mf) (Λ₀ Mf)) : Reach Mf 0 c c := rfl

theorem Reach.trans {n m : ℕ} {a b c : TM0.Cfg (Γ₀ Mf) (Λ₀ Mf)} (h₁ : Reach Mf n a b)
    (h₂ : Reach Mf m b c) : Reach Mf (n + m) a c := by
  unfold Reach at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h₁, h₂]

theorem Reach.cast {n m : ℕ} {a b : TM0.Cfg (Γ₀ Mf) (Λ₀ Mf)} (h : Reach Mf n a b)
    (e : n = m) : Reach Mf m a b := e ▸ h

variable (Mf)

theorem step_write (s s' : Λ₀ Mf) (T : Tape (Γ₀ Mf)) (b : Γ₀ Mf)
    (h : δ₀ Mf s T.head = some (s', TM0.Stmt.write b)) :
    Reach Mf 1 ⟨s, T⟩ ⟨s', T.write b⟩ := by
  show Option.map _ (δ₀ Mf s T.head) = _
  rw [h]
  rfl

theorem step_move (s s' : Λ₀ Mf) (T : Tape (Γ₀ Mf)) (d : Dir)
    (h : δ₀ Mf s T.head = some (s', TM0.Stmt.move d)) :
    Reach Mf 1 ⟨s, T⟩ ⟨s', T.move d⟩ := by
  show Option.map _ (δ₀ Mf s T.head) = _
  rw [h]
  rfl

/-! ### The tape -/

theorem mk_append_blank (l : List (Γ₀ Mf)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n default) = ListBlank.mk l :=
  (Quotient.sound' (Or.inl ⟨n, rfl⟩)).symm

/-- The content of cell `i`: blank when the cell is not written. -/
def cell (right : List ℕ) (i : ℕ) : Γ₀ Mf :=
  match right[i]? with
  | some v => sy Mf v
  | none => none

/-- The cells to the left of the head, nearest first, then the wall. -/
def leftOf (h : ℕ) (right : List ℕ) : List (Γ₀ Mf) :=
  (List.range h).reverse.map (cell Mf right) ++ [wall Mf]

/-- The tape of the simulating machine for the head `h` and the cells `right`. -/
def tapeOf (h : ℕ) (right : List ℕ) : Tape (Γ₀ Mf) :=
  Tape.mk' (ListBlank.mk (leftOf Mf h right)) (ListBlank.mk ((right.drop h).map (sy Mf)))

theorem headI_drop (h : ℕ) (right : List ℕ) :
    ((right.drop h).map (sy Mf)).headI = cell Mf right h := by
  by_cases hh : h < right.length
  · rw [List.drop_eq_getElem_cons hh]
    unfold cell
    rw [List.getElem?_eq_getElem hh]
    rfl
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hh)]
    unfold cell
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hh)]
    rfl

theorem tapeOf_head (h : ℕ) (right : List ℕ) : (tapeOf Mf h right).head = cell Mf right h := by
  unfold tapeOf
  rw [Tape.mk'_head, ListBlank.head_mk, headI_drop]

theorem leftOf_succ (h : ℕ) (right : List ℕ) :
    leftOf Mf (h + 1) right = cell Mf right h :: leftOf Mf h right := by
  simp [leftOf, List.range_succ]

theorem tapeOf_right (h : ℕ) (right : List ℕ) :
    (tapeOf Mf h right).move Dir.right = tapeOf Mf (h + 1) right := by
  unfold tapeOf
  rw [Tape.move_right_mk', ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, headI_drop,
    leftOf_succ]
  simp

theorem tapeOf_left (h : ℕ) (right : List ℕ) :
    (tapeOf Mf (h + 1) right).move Dir.left = tapeOf Mf h right := by
  unfold tapeOf
  rw [Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, leftOf_succ]
  simp only [List.headI, List.tail_cons]
  congr 1
  by_cases hh : h < right.length
  · rw [List.drop_eq_getElem_cons hh]
    unfold cell
    rw [List.getElem?_eq_getElem hh]
    rfl
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hh),
      List.drop_eq_nil_of_le (by omega : right.length ≤ h + 1)]
    have e : cell Mf right h = none := by
      unfold cell
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hh)]
    rw [e]
    exact mk_append_blank Mf [] 1

theorem tapeOf_left_head_zero (right : List ℕ) :
    ((tapeOf Mf 0 right).move Dir.left).head = wall Mf := by
  unfold tapeOf
  rw [Tape.move_left_mk', Tape.mk'_head, ListBlank.head_cons, ListBlank.head_mk]
  rfl

theorem cell_set (h : ℕ) (right : List ℕ) (v : ℕ) (i : ℕ) (hi : i < h) (hh : h < right.length) :
    cell Mf (right.take h ++ v :: right.drop (h + 1)) i = cell Mf right i := by
  have e : (right.take h ++ v :: right.drop (h + 1))[i]? = right[i]? := by
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hi]
  simp [cell, e]

theorem leftOf_congr (h : ℕ) (r r' : List ℕ) (hc : ∀ i, i < h → cell Mf r' i = cell Mf r i) :
    leftOf Mf h r' = leftOf Mf h r := by
  unfold leftOf
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hc i (by simpa using hi)

theorem tapeOf_write_in (h : ℕ) (right : List ℕ) (v : ℕ) (hh : h < right.length) :
    (tapeOf Mf h right).write (sy Mf v) =
      tapeOf Mf h (right.take h ++ v :: right.drop (h + 1)) := by
  unfold tapeOf
  rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk,
    leftOf_congr Mf h right _ (fun i hi => cell_set Mf h right v i hi hh)]
  congr 2
  rw [List.drop_left' (by simp; omega)]
  simp

theorem tapeOf_write_end (right : List ℕ) (v : ℕ) :
    (tapeOf Mf right.length right).write (sy Mf v) = tapeOf Mf right.length (right ++ [v]) := by
  unfold tapeOf
  rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk,
    leftOf_congr Mf right.length right (right ++ [v]) (fun i hi => by
      have e : (right ++ [v])[i]? = right[i]? := List.getElem?_append_left hi
      simp [cell, e])]
  congr 2
  simp


/-! ### One step of the simulated machine -/

theorem cur_eq (lft : List ℕ) (h : ℕ) (right : List ℕ) :
    currentTapeSymbol (lft, h, right) = right[h]? := by
  by_cases hh : h < right.length
  · simp [currentTapeSymbol, hh]
  · simp [currentTapeSymbol, hh]

theorem step_eq (q : ℕ) (tp : List ℕ × ℕ × List ℕ) :
    stepFlatTM Mf ⟨q, [tp]⟩ =
      (look Mf q (currentTapeSymbol tp)).bind (applyTransitionEntry ⟨q, [tp]⟩) := rfl

theorem numOf_cell (right : List ℕ) (hb : ∀ v ∈ right, v ≤ Mf.sig + 3) (h : ℕ) :
    numOf Mf (cell Mf right h) = right[h]? := by
  unfold cell
  cases hr : right[h]? with
  | none => rfl
  | some v =>
    have hv : v ≤ Mf.sig + 3 := hb v (List.mem_of_getElem? hr)
    show some (toFin (Mf.sig + 3) v).val = some v
    rw [toFin_val hv]

theorem rd_none (q : ℕ) (hq : q ≤ Mf.states) (a : Γ₀ Mf) (hnh : Mf.halt.getD q false = false)
    (e : FlatTMTransEntry) (hl : look Mf q (numOf Mf a) = some e) (mv : TMMove)
    (hw : e.dst_write_vals = [none]) (hmv : e.move_dirs = [mv]) :
    δ₀ Mf (Tag.rd, toFin Mf.states q, default, default) a =
      some ((Tag.mvd, toFin Mf.states e.dst_state, default, mvCode mv), TM0.Stmt.write a) := by
  show rdTr Mf (toFin Mf.states q) a = _
  simp only [rdTr, toFin_val hq, hnh, hl, hw, hmv, List.headD_cons, Bool.false_eq_true,
    ite_false]

theorem rd_blank (q : ℕ) (hq : q ≤ Mf.states) (hnh : Mf.halt.getD q false = false)
    (e : FlatTMTransEntry) (hl : look Mf q (numOf Mf none) = some e) (v : ℕ) (mv : TMMove)
    (hw : e.dst_write_vals = [some v]) (hmv : e.move_dirs = [mv]) :
    δ₀ Mf (Tag.rd, toFin Mf.states q, default, default) none =
      some ((Tag.ft, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v, mvCode mv),
        TM0.Stmt.move Dir.left) := by
  show rdTr Mf (toFin Mf.states q) none = _
  simp only [rdTr, toFin_val hq, hnh, hl, hw, hmv, List.headD_cons, Bool.false_eq_true,
    ite_false]

theorem rd_sym (q : ℕ) (hq : q ≤ Mf.states) (u : ℕ) (hnh : Mf.halt.getD q false = false)
    (e : FlatTMTransEntry) (hl : look Mf q (numOf Mf (sy Mf u)) = some e) (v : ℕ) (mv : TMMove)
    (hw : e.dst_write_vals = [some v]) (hmv : e.move_dirs = [mv]) :
    δ₀ Mf (Tag.rd, toFin Mf.states q, default, default) (sy Mf u) =
      some ((Tag.mvd, toFin Mf.states e.dst_state, default, mvCode mv),
        TM0.Stmt.write (sy Mf v)) := by
  show rdTr Mf (toFin Mf.states q) (some (Sum.inl (toFin (Mf.sig + 3) u))) = _
  have hl2 : look Mf q (numOf Mf (some (Sum.inl (toFin (Mf.sig + 3) u)))) = some e := hl
  simp only [rdTr, toFin_val hq, hnh, hl2, hw, hmv, List.headD_cons, Bool.false_eq_true,
    ite_false]

theorem cell_of_lt (right : List ℕ) (h : ℕ) (hh : h < right.length) :
    cell Mf right h = sy Mf right[h] := by
  unfold cell
  rw [List.getElem?_eq_getElem hh]

theorem cell_of_ge (right : List ℕ) (h : ℕ) (hh : right.length ≤ h) :
    cell Mf right h = none := by
  unfold cell
  rw [List.getElem?_eq_none hh]

theorem write_phase (q : ℕ) (hq : q ≤ Mf.states) (lft : List ℕ) (h : ℕ) (right : List ℕ)
    (hb : ∀ v ∈ right, v ≤ Mf.sig + 3) (hne : right ≠ [])
    (hnh : Mf.halt.getD q false = false) (e : FlatTMTransEntry)
    (hl : look Mf q right[h]? = some e) (w : Option ℕ) (mv : TMMove)
    (hw : e.dst_write_vals = [w]) (hmv : e.move_dirs = [mv])
    (hwb : ∀ v, w = some v → v ≤ Mf.sig + 3) :
    ∃ (n : ℕ) (r1 : List ℕ), n ≤ 3 ∧ writeCurrentTapeSymbol (lft, h, right) w = (lft, h, r1) ∧
      Reach Mf n ⟨(Tag.rd, toFin Mf.states q, default, default), tapeOf Mf h right⟩
        ⟨(Tag.mvd, toFin Mf.states e.dst_state, default, mvCode mv), tapeOf Mf h r1⟩ ∧
      (∀ v ∈ r1, v ≤ Mf.sig + 3) ∧ r1 ≠ [] ∧ r1.length ≤ right.length + 1 := by
  have hl' : look Mf q (numOf Mf (cell Mf right h)) = some e := by
    rw [numOf_cell Mf right hb h]
    exact hl
  cases w with
  | none =>
    refine ⟨1, right, by omega, rfl, ?_, hb, hne, by omega⟩
    have h0 := step_write Mf (Tag.rd, toFin Mf.states q, default, default) _ (tapeOf Mf h right)
      (cell Mf right h) (by
        rw [tapeOf_head]
        exact rd_none Mf q hq _ hnh e hl' mv hw hmv)
    have e1 : (tapeOf Mf h right).write (cell Mf right h) = tapeOf Mf h right := by
      rw [← tapeOf_head]
      exact Tape.write_self _
    rw [e1] at h0
    exact h0
  | some v =>
    have hvb : v ≤ Mf.sig + 3 := hwb v rfl
    by_cases hh : h < right.length
    · refine ⟨1, right.take h ++ v :: right.drop (h + 1), by omega, ?_, ?_, ?_, by simp, ?_⟩
      · simp [writeCurrentTapeSymbol, hh]
      · have hc := cell_of_lt Mf right h hh
        rw [hc] at hl'
        have h0 := step_write Mf (Tag.rd, toFin Mf.states q, default, default) _
          (tapeOf Mf h right) (sy Mf v) (by
            rw [tapeOf_head, hc]
            exact rd_sym Mf q hq _ hnh e hl' v mv hw hmv)
        rw [tapeOf_write_in Mf h right v hh] at h0
        exact h0
      · intro x hx
        rw [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · exact hb x (List.mem_of_mem_take hx)
        · rw [hx]; exact hvb
        · exact hb x (List.mem_of_mem_drop hx)
      · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
        omega
    · have hge : right.length ≤ h := Nat.le_of_not_lt hh
      have hlen : 0 < right.length := List.length_pos_iff.mpr hne
      obtain ⟨h0, rfl⟩ : ∃ h0, h = h0 + 1 := ⟨h - 1, by omega⟩
      have hc := cell_of_ge Mf right (h0 + 1) hge
      rw [hc] at hl'
      have s1 := step_move Mf (Tag.rd, toFin Mf.states q, default, default) _
        (tapeOf Mf (h0 + 1) right) Dir.left (by
          rw [tapeOf_head, hc]
          exact rd_blank Mf q hq hnh e hl' v mv hw hmv)
      rw [tapeOf_left] at s1
      by_cases hf : h0 < right.length
      · have hfe : h0 + 1 = right.length := by omega
        have s2 := step_move Mf (Tag.ft, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v,
          mvCode mv) (Tag.wr, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v, mvCode mv)
          (tapeOf Mf h0 right) Dir.right (by
            rw [tapeOf_head, cell_of_lt Mf right h0 hf]
            rfl)
        rw [tapeOf_right] at s2
        have s3 := step_write Mf (Tag.wr, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v,
          mvCode mv) (Tag.mvd, toFin Mf.states e.dst_state, default, mvCode mv)
          (tapeOf Mf (h0 + 1) right) (sy Mf v) rfl
        rw [hfe, tapeOf_write_end] at s3
        refine ⟨3, right ++ [v], by omega, ?_, ?_, ?_, by simp, by simp⟩
        · simp [writeCurrentTapeSymbol, hfe]
        · rw [hfe] at s1 s2
          rw [hfe]
          exact (s1.trans s2).trans s3
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact hb x hx
          · rw [hx]; exact hvb
      · have s2 := step_move Mf (Tag.ft, toFin Mf.states e.dst_state, toFin (Mf.sig + 3) v,
          mvCode mv) (Tag.mvd, toFin Mf.states e.dst_state, default, mvCode mv)
          (tapeOf Mf h0 right) Dir.right (by
            rw [tapeOf_head, cell_of_ge Mf right h0 (Nat.le_of_not_lt hf)]
            rfl)
        rw [tapeOf_right] at s2
        refine ⟨2, right, by omega, ?_, s1.trans s2, hb, hne, by omega⟩
        have h1 : ¬ h0 + 1 < right.length := by omega
        have h2 : ¬ h0 + 1 = right.length := by omega
        simp [writeCurrentTapeSymbol, h1, h2]

theorem lw_cell (Q : Fin (Mf.states + 1)) (right : List ℕ) (i : ℕ) :
    δ₀ Mf (Tag.lw, Q, default, default) (cell Mf right i) =
      some ((Tag.rd, Q, default, default), TM0.Stmt.write (cell Mf right i)) := by
  unfold cell
  cases right[i]? <;> rfl

theorem move_phase (Q : Fin (Mf.states + 1)) (mv : TMMove) (lft : List ℕ) (h : ℕ)
    (r : List ℕ) :
    ∃ n : ℕ, n ≤ 2 ∧ Reach Mf n ⟨(Tag.mvd, Q, default, mvCode mv), tapeOf Mf h r⟩
      ⟨(Tag.rd, Q, default, default), tapeOf Mf (moveTapeHead (lft, h, r) mv).2.1 r⟩ := by
  cases mv with
  | Nmove =>
    refine ⟨1, by omega, ?_⟩
    have h0 := step_write Mf (Tag.mvd, Q, default, mvCode TMMove.Nmove)
      (Tag.rd, Q, default, default) (tapeOf Mf h r) (tapeOf Mf h r).head rfl
    rw [Tape.write_self] at h0
    exact h0
  | Rmove =>
    refine ⟨1, by omega, ?_⟩
    have h0 := step_move Mf (Tag.mvd, Q, default, mvCode TMMove.Rmove)
      (Tag.rd, Q, default, default) (tapeOf Mf h r) Dir.right rfl
    rw [tapeOf_right] at h0
    exact h0
  | Lmove =>
    have s1 := step_move Mf (Tag.mvd, Q, default, mvCode TMMove.Lmove)
      (Tag.lw, Q, default, default) (tapeOf Mf h r) Dir.left rfl
    cases h with
    | zero =>
      have s2 := step_move Mf (Tag.lw, Q, default, default) (Tag.rd, Q, default, default)
        ((tapeOf Mf 0 r).move Dir.left) Dir.right (by
          rw [tapeOf_left_head_zero]
          rfl)
      rw [Tape.move_left_right] at s2
      exact ⟨2, by omega, s1.trans s2⟩
    | succ h0 =>
      rw [tapeOf_left] at s1
      have s2 := step_write Mf (Tag.lw, Q, default, default) (Tag.rd, Q, default, default)
        (tapeOf Mf h0 r) (cell Mf r h0) (by
          rw [tapeOf_head]
          exact lw_cell Mf Q r h0)
      have e1 : (tapeOf Mf h0 r).write (cell Mf r h0) = tapeOf Mf h0 r := by
        rw [← tapeOf_head]
        exact Tape.write_self _
      rw [e1] at s2
      exact ⟨2, by omega, s1.trans s2⟩

theorem sim_step (hv : validFlatTM Mf) (h1 : Mf.tapes = 1) (q : ℕ) (lft : List ℕ) (h : ℕ)
    (right : List ℕ) (cfg' : FlatTMConfig) (hq : q ≤ Mf.states)
    (hb : ∀ v ∈ right, v ≤ Mf.sig + 3) (hne : right ≠ [])
    (hnh : haltingStateReached Mf ⟨q, [(lft, h, right)]⟩ = false)
    (hstep : stepFlatTM Mf ⟨q, [(lft, h, right)]⟩ = some cfg') :
    ∃ (n q' : ℕ) (lft' : List ℕ) (h' : ℕ) (right' : List ℕ),
      cfg' = ⟨q', [(lft', h', right')]⟩ ∧ n ≤ 5 ∧
      Reach Mf n ⟨(Tag.rd, toFin Mf.states q, default, default), tapeOf Mf h right⟩
        ⟨(Tag.rd, toFin Mf.states q', default, default), tapeOf Mf h' right'⟩ ∧
      q' ≤ Mf.states ∧ (∀ v ∈ right', v ≤ Mf.sig + 3) ∧ right' ≠ [] ∧ h' ≤ h + 1 ∧
      right'.length ≤ right.length + 1 := by
  rw [step_eq, cur_eq] at hstep
  cases hl : look Mf q right[h]? with
  | none =>
    rw [hl] at hstep
    exact absurd hstep (by simp)
  | some e =>
    rw [hl] at hstep
    have hmem : e ∈ Mf.trans := List.mem_of_find?_eq_some hl
    obtain ⟨-, hdst, -, hl2, hl3, -, hb2⟩ := hv.2.2 e hmem
    rw [h1] at hl2 hl3
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hl2
    obtain ⟨mv, hmv⟩ := List.length_eq_one_iff.mp hl3
    have hwb : ∀ v, w = some v → v ≤ Mf.sig + 3 := by
      intro v hv'
      have h0 := hb2 w (by rw [hw]; exact List.mem_singleton_self _)
      rw [hv'] at h0
      have h0' : v < Mf.sig := h0
      omega
    obtain ⟨n1, r1, hn1, hwr, hr1, hb1, hne1, hlen1⟩ := write_phase Mf q hq lft h right hb hne
      hnh e hl w mv hw hmv hwb
    obtain ⟨n2, hn2, hr2⟩ := move_phase Mf (toFin Mf.states e.dst_state) mv lft h r1
    have hcfg : cfg' = ⟨e.dst_state, [moveTapeHead (lft, h, r1) mv]⟩ := by
      have h0 : applyTransitionEntry ⟨q, [(lft, h, right)]⟩ e =
          some ⟨e.dst_state, [tapeStep (lft, h, right) w mv]⟩ := by
        simp [applyTransitionEntry, hw, hmv]
      have h2 : (some e).bind (applyTransitionEntry ⟨q, [(lft, h, right)]⟩) =
          applyTransitionEntry ⟨q, [(lft, h, right)]⟩ e := rfl
      rw [h2, h0] at hstep
      have h3 := (Option.some.inj hstep).symm
      rw [h3]
      show (⟨e.dst_state, [moveTapeHead (writeCurrentTapeSymbol (lft, h, right) w) mv]⟩ :
        FlatTMConfig) = _
      rw [hwr]
    have hmvh : (moveTapeHead (lft, h, r1) mv).2.1 ≤ h + 1 := by
      cases mv
      · show h - 1 ≤ h + 1
        omega
      · show h + 1 ≤ h + 1
        omega
      · show h ≤ h + 1
        omega
    have hmvf : moveTapeHead (lft, h, r1) mv = (lft, (moveTapeHead (lft, h, r1) mv).2.1, r1) := by
      cases mv <;> rfl
    refine ⟨n1 + n2, e.dst_state, lft, (moveTapeHead (lft, h, r1) mv).2.1, r1, ?_, by omega,
      hr1.trans hr2, by omega, hb1, hne1, hmvh, hlen1⟩
    rw [hcfg, ← hmvf]


/-! ### The run of the simulated machine -/

theorem run_chain (hv : validFlatTM Mf) (h1 : Mf.tapes = 1) : ∀ (k q : ℕ) (lft : List ℕ) (h : ℕ)
    (right : List ℕ) (cfg : FlatTMConfig), q ≤ Mf.states → (∀ v ∈ right, v ≤ Mf.sig + 3) →
    right ≠ [] → runFlatTM k Mf ⟨q, [(lft, h, right)]⟩ = some cfg →
    haltingStateReached Mf cfg = true →
    ∃ (n q' : ℕ) (lft' : List ℕ) (h' : ℕ) (right' : List ℕ),
      cfg = ⟨q', [(lft', h', right')]⟩ ∧ n ≤ 5 * k ∧
      Reach Mf n ⟨(Tag.rd, toFin Mf.states q, default, default), tapeOf Mf h right⟩
        ⟨(Tag.rd, toFin Mf.states q', default, default), tapeOf Mf h' right'⟩ ∧
      q' ≤ Mf.states ∧ (∀ v ∈ right', v ≤ Mf.sig + 3) ∧ right' ≠ [] ∧ h' ≤ h + k ∧
      right'.length ≤ right.length + k := by
  intro k
  induction k with
  | zero =>
    intro q lft h right cfg hq hb hne hrun _
    have e : (⟨q, [(lft, h, right)]⟩ : FlatTMConfig) = cfg := Option.some.inj hrun
    exact ⟨0, q, lft, h, right, e.symm, by omega, Reach.refl _, hq, hb, hne, by omega, by omega⟩
  | succ k ih =>
    intro q lft h right cfg hq hb hne hrun hhalt
    by_cases hh : haltingStateReached Mf ⟨q, [(lft, h, right)]⟩ = true
    · rw [runFlatTM_of_halting Mf _ (k + 1) hh] at hrun
      have e : (⟨q, [(lft, h, right)]⟩ : FlatTMConfig) = cfg := Option.some.inj hrun
      exact ⟨0, q, lft, h, right, e.symm, by omega, Reach.refl _, hq, hb, hne, by omega,
        by omega⟩
    · have hh' : haltingStateReached Mf ⟨q, [(lft, h, right)]⟩ = false := by
        cases hx : haltingStateReached Mf ⟨q, [(lft, h, right)]⟩ with
        | true => exact absurd hx hh
        | false => rfl
      have e0 : runFlatTM (k + 1) Mf ⟨q, [(lft, h, right)]⟩ =
          (if haltingStateReached Mf ⟨q, [(lft, h, right)]⟩ = true then
            some ⟨q, [(lft, h, right)]⟩
          else match stepFlatTM Mf ⟨q, [(lft, h, right)]⟩ with
            | none => some ⟨q, [(lft, h, right)]⟩
            | some c' => runFlatTM k Mf c') := rfl
      rw [e0, hh'] at hrun
      cases hs : stepFlatTM Mf ⟨q, [(lft, h, right)]⟩ with
      | none =>
        rw [hs] at hrun
        have e : (⟨q, [(lft, h, right)]⟩ : FlatTMConfig) = cfg := Option.some.inj hrun
        rw [← e, hh'] at hhalt
        exact absurd hhalt (by simp)
      | some c1 =>
        rw [hs] at hrun
        have hrun' : runFlatTM k Mf c1 = some cfg := hrun
        obtain ⟨n1, q1, lft1, hd1, r1, hc1, hn1, hr1, hq1, hb1, hne1, hh1, hl1⟩ :=
          sim_step Mf hv h1 q lft h right c1 hq hb hne hh' hs
        subst hc1
        obtain ⟨n2, q2, lft2, hd2, r2, hc2, hn2, hr2, hq2, hb2, hne2, hh2, hl2⟩ :=
          ih q1 lft1 hd1 r1 cfg hq1 hb1 hne1 hrun' hhalt
        exact ⟨n1 + n2, q2, lft2, hd2, r2, hc2, by omega, hr1.trans hr2, hq2, hb2, hne2,
          by omega, by omega⟩

/-! ### Writing the input and reading the output -/

/-- A tape given by the cells to the left of the head and the cells from the head on. -/
def tp (Ls Rs : List (Γ₀ Mf)) : Tape (Γ₀ Mf) :=
  Tape.mk' (ListBlank.mk Ls) (ListBlank.mk Rs)

theorem tp_head (Ls Rs : List (Γ₀ Mf)) : (tp Mf Ls Rs).head = Rs.headI := by
  unfold tp
  rw [Tape.mk'_head, ListBlank.head_mk]

theorem tp_write (Ls Rs : List (Γ₀ Mf)) (b : Γ₀ Mf) :
    (tp Mf Ls Rs).write b = tp Mf Ls (b :: Rs.tail) := by
  unfold tp
  rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]

theorem tp_right (Ls Rs : List (Γ₀ Mf)) :
    (tp Mf Ls Rs).move Dir.right = tp Mf (Rs.headI :: Ls) Rs.tail := by
  unfold tp
  rw [Tape.move_right_mk', ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

theorem tp_left (Ls Rs : List (Γ₀ Mf)) :
    (tp Mf Ls Rs).move Dir.left = tp Mf Ls.tail (Ls.headI :: Rs) := by
  unfold tp
  rw [Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

theorem i0_loop : ∀ (xs : List Bool) (Ls : List (Γ₀ Mf)),
    Reach Mf (2 * xs.length) ⟨st0 Mf Tag.i0, tp Mf Ls (xs.map (inpL Mf))⟩
      ⟨st0 Mf Tag.i0,
        tp Mf ((xs.map fun b => sy Mf (if b then 2 else 1)).reverse ++ Ls) []⟩ := by
  intro xs
  induction xs with
  | nil => intro Ls; exact Reach.refl _
  | cons b xs ih =>
    intro Ls
    have s1 := step_write Mf (st0 Mf Tag.i0) (st0 Mf Tag.i0)
      (tp Mf Ls (inpL Mf b :: xs.map (inpL Mf))) (sy Mf (if b then 2 else 1)) (by
        rw [tp_head]
        rfl)
    rw [tp_write] at s1
    have s2 := step_move Mf (st0 Mf Tag.i0) (st0 Mf Tag.i0)
      (tp Mf Ls (sy Mf (if b then 2 else 1) :: xs.map (inpL Mf))) Dir.right (by
        rw [tp_head]
        rfl)
    rw [tp_right] at s2
    have s3 := ih (sy Mf (if b then 2 else 1) :: Ls)
    have e : (xs.map fun b => sy Mf (if b then 2 else 1)).reverse ++
        sy Mf (if b then 2 else 1) :: Ls =
        ((b :: xs).map fun b => sy Mf (if b then 2 else 1)).reverse ++ Ls := by
      simp
    rw [e] at s3
    exact ((s1.trans s2).trans s3).cast (by
      simp only [List.length_cons]
      omega)

theorem i3_loop : ∀ (Ls : List ℕ) (c : ℕ) (Rs : List (Γ₀ Mf)),
    Reach Mf (Ls.length + 1) ⟨st0 Mf Tag.i3, tp Mf (Ls.map (sy Mf)) (sy Mf c :: Rs)⟩
      ⟨st0 Mf Tag.i3, tp Mf [] (none :: (Ls.reverse.map (sy Mf) ++ sy Mf c :: Rs))⟩ := by
  intro Ls
  induction Ls with
  | nil =>
    intro c Rs
    have s1 := step_move Mf (st0 Mf Tag.i3) (st0 Mf Tag.i3) (tp Mf [] (sy Mf c :: Rs)) Dir.left
      (by
        rw [tp_head]
        rfl)
    rw [tp_left] at s1
    exact s1
  | cons a Ls ih =>
    intro c Rs
    have s1 := step_move Mf (st0 Mf Tag.i3) (st0 Mf Tag.i3)
      (tp Mf ((a :: Ls).map (sy Mf)) (sy Mf c :: Rs)) Dir.left (by
        rw [tp_head]
        rfl)
    rw [tp_left] at s1
    have s2 := ih a (sy Mf c :: Rs)
    have e : Ls.reverse.map (sy Mf) ++ sy Mf a :: sy Mf c :: Rs =
        (a :: Ls).reverse.map (sy Mf) ++ sy Mf c :: Rs := by
      simp
    rw [e] at s2
    exact (s1.trans s2).cast (by
      simp only [List.length_cons]
      omega)

theorem init_run (x : List Bool) :
    Reach Mf (3 * x.length + 9) ⟨st0 Mf Tag.i0, tp Mf [] (x.map (inpL Mf))⟩
      ⟨(Tag.rd, toFin Mf.states Mf.start, default, default),
        tapeOf Mf 0 (CookLevin.stringTape x)⟩ := by
  have s1 := i0_loop Mf x []
  have e1 : (x.map fun b => sy Mf (if b then 2 else 1)).reverse ++ [] =
      ((x.map fun b => if b then 2 else 1).reverse).map (sy Mf) := by
    simp [List.map_reverse]
  rw [e1] at s1
  have s2 := step_write Mf (st0 Mf Tag.i0) (st0 Mf Tag.i1)
    (tp Mf (((x.map fun b => if b then 2 else 1).reverse).map (sy Mf)) []) (sy Mf 0) (by
      rw [tp_head]
      rfl)
  rw [tp_write] at s2
  have s3 := step_move Mf (st0 Mf Tag.i1) (st0 Mf Tag.i2)
    (tp Mf (((x.map fun b => if b then 2 else 1).reverse).map (sy Mf)) [sy Mf 0]) Dir.right (by
      rw [tp_head]
      rfl)
  rw [tp_right] at s3
  have s4 := step_write Mf (st0 Mf Tag.i2) (st0 Mf Tag.i3)
    (tp Mf (sy Mf 0 :: ((x.map fun b => if b then 2 else 1).reverse).map (sy Mf)) [])
    (sy Mf 3) (by
      rw [tp_head]
      rfl)
  rw [tp_write] at s4
  have s5 := i3_loop Mf (0 :: (x.map fun b => if b then 2 else 1).reverse) 3 []
  have s6 := step_write Mf (st0 Mf Tag.i3) (st0 Mf Tag.i4)
    (tp Mf [] (none :: ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++
      [sy Mf 3]))) (sy Mf 3) (by
      rw [tp_head]
      rfl)
  rw [tp_write] at s6
  have s7 := step_move Mf (st0 Mf Tag.i4) (st0 Mf Tag.i5)
    (tp Mf [] (sy Mf 3 ::
      ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++ [sy Mf 3])))
    Dir.left (by
      rw [tp_head]
      rfl)
  rw [tp_left] at s7
  have s8 := step_write Mf (st0 Mf Tag.i5) (st0 Mf Tag.i6)
    (tp Mf [] (none :: sy Mf 3 ::
      ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++ [sy Mf 3])))
    (wall Mf) (by
      rw [tp_head]
      rfl)
  rw [tp_write] at s8
  have s9 := step_move Mf (st0 Mf Tag.i6) (Tag.rd, toFin Mf.states Mf.start, default, default)
    (tp Mf [] (wall Mf :: sy Mf 3 ::
      ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++ [sy Mf 3])))
    Dir.right (by
      rw [tp_head]
      rfl)
  rw [tp_right] at s9
  have e9 : tp Mf [wall Mf] (sy Mf 3 ::
      ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++ [sy Mf 3])) =
      tapeOf Mf 0 (CookLevin.stringTape x) := by
    unfold tapeOf tp leftOf CookLevin.stringTape CookLevin.symbolsOf
    simp
  have s9' : Reach Mf 1 ⟨st0 Mf Tag.i6, tp Mf [] (wall Mf :: sy Mf 3 ::
      ((0 :: (x.map fun b => if b then 2 else 1).reverse).reverse.map (sy Mf) ++ [sy Mf 3]))⟩
      ⟨(Tag.rd, toFin Mf.states Mf.start, default, default),
        tapeOf Mf 0 (CookLevin.stringTape x)⟩ := by
    rw [← e9]
    exact s9
  exact ((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans
    s9').cast (by
      simp only [List.length_cons, List.length_reverse, List.length_map]
      omega)

theorem rd_halt (q : ℕ) (hq : q ≤ Mf.states) (a : Γ₀ Mf) (hh : Mf.halt.getD q false = true) :
    δ₀ Mf (Tag.rd, toFin Mf.states q, default, default) a =
      some (st0 Mf Tag.o0, TM0.Stmt.write a) := by
  show rdTr Mf (toFin Mf.states q) a = _
  simp only [rdTr, toFin_val hq, hh, ite_true]

theorem o0_cell (right : List ℕ) (i : ℕ) :
    δ₀ Mf (st0 Mf Tag.o0) (cell Mf right i) = some (st0 Mf Tag.o0, TM0.Stmt.move Dir.left) := by
  unfold cell
  cases right[i]? <;> rfl

theorem o0_loop (right : List ℕ) : ∀ h : ℕ,
    Reach Mf (h + 2) ⟨st0 Mf Tag.o0, tapeOf Mf h right⟩ ⟨st0 Mf Tag.o1, tapeOf Mf 0 right⟩ := by
  intro h
  induction h with
  | zero =>
    have s1 := step_move Mf (st0 Mf Tag.o0) (st0 Mf Tag.o0) (tapeOf Mf 0 right) Dir.left (by
      rw [tapeOf_head]
      exact o0_cell Mf right 0)
    have s2 := step_move Mf (st0 Mf Tag.o0) (st0 Mf Tag.o1) ((tapeOf Mf 0 right).move Dir.left)
      Dir.right (by
        rw [tapeOf_left_head_zero]
        rfl)
    rw [Tape.move_left_right] at s2
    exact s1.trans s2
  | succ h ih =>
    have s1 := step_move Mf (st0 Mf Tag.o0) (st0 Mf Tag.o0) (tapeOf Mf (h + 1) right) Dir.left (by
      rw [tapeOf_head]
      exact o0_cell Mf right (h + 1))
    rw [tapeOf_left] at s1
    exact (s1.trans ih).cast (by omega)

/-- The cells the output is read from. -/
def tw (l : List ℕ) : List ℕ := (l.takeWhile (· != 3)).takeWhile (· != 0)

theorem tw_stop (v : ℕ) (l : List ℕ) (h : v = 0 ∨ v = 3) : tw (v :: l) = [] := by
  rcases h with h | h <;> subst h <;> simp [tw]

theorem tw_cons (v : ℕ) (l : List ℕ) (h : ¬ (v = 0 ∨ v = 3)) : tw (v :: l) = v :: tw l := by
  have h0 : v ≠ 0 := fun e => h (Or.inl e)
  have h3 : v ≠ 3 := fun e => h (Or.inr e)
  simp [tw, h0, h3]

theorem tw_length (l : List ℕ) : (tw l).length ≤ l.length := by
  unfold tw
  exact (List.takeWhile_sublist _).length_le.trans (List.takeWhile_sublist _).length_le

theorem sy_ne_out (v : ℕ) (b : Bool) : sy Mf v ≠ outL Mf b := by
  intro h
  simp [sy, outL] at h

theorem o2_loop : ∀ (l : List ℕ), (∀ v ∈ l, v ≤ Mf.sig + 3) → ∀ (Ls : List (Γ₀ Mf)),
    ∃ Rr : List (Γ₀ Mf), (∀ b, Rr.headI ≠ outL Mf b) ∧
      Reach Mf (2 * (tw l).length + 1) ⟨st0 Mf Tag.o2, tp Mf Ls (l.map (sy Mf))⟩
        ⟨st0 Mf Tag.o3,
          (tp Mf ((((tw l).map (· == 2)).map (outL Mf)).reverse ++ Ls) Rr).move Dir.left⟩ := by
  intro l
  induction l with
  | nil =>
    intro _ Ls
    refine ⟨[], (fun b h => by cases h), ?_⟩
    exact step_move Mf (st0 Mf Tag.o2) (st0 Mf Tag.o3) (tp Mf Ls []) Dir.left (by
      rw [tp_head]
      rfl)
  | cons v l ih =>
    intro hl Ls
    have hvb : v ≤ Mf.sig + 3 := hl v List.mem_cons_self
    by_cases hv : v = 0 ∨ v = 3
    · refine ⟨(v :: l).map (sy Mf), fun b => sy_ne_out Mf v b, ?_⟩
      rw [tw_stop v l hv]
      exact step_move Mf (st0 Mf Tag.o2) (st0 Mf Tag.o3) (tp Mf Ls ((v :: l).map (sy Mf)))
        Dir.left (by
          rw [tp_head]
          show o2Tr Mf (sy Mf v) = _
          simp only [o2Tr, sy, toFin_val hvb, hv, ite_true])
    · obtain ⟨Rr, hRr, hr⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
        (outL Mf (v == 2) :: Ls)
      refine ⟨Rr, hRr, ?_⟩
      have s1 := step_write Mf (st0 Mf Tag.o2) (st0 Mf Tag.o2)
        (tp Mf Ls ((v :: l).map (sy Mf))) (outL Mf (v == 2)) (by
          rw [tp_head]
          show o2Tr Mf (sy Mf v) = _
          simp only [o2Tr, sy, toFin_val hvb, hv, ite_false])
      rw [tp_write] at s1
      have s2 := step_move Mf (st0 Mf Tag.o2) (st0 Mf Tag.o2)
        (tp Mf Ls (outL Mf (v == 2) :: l.map (sy Mf))) Dir.right (by
          rw [tp_head]
          rfl)
      rw [tp_right] at s2
      rw [tw_cons v l hv]
      have e : (((tw l).map (· == 2)).map (outL Mf)).reverse ++ outL Mf (v == 2) :: Ls =
          ((((v :: tw l).map (· == 2)).map (outL Mf)).reverse ++ Ls) := by
        simp
      rw [e] at hr
      exact ((s1.trans s2).trans hr).cast (by
        simp only [List.length_cons]
        omega)

theorem o3_nonout (a : Γ₀ Mf) (h : ∀ b, a ≠ outL Mf b) :
    δ₀ Mf (st0 Mf Tag.o3) a = some (st0 Mf Tag.o4, TM0.Stmt.move Dir.right) := by
  rcases a with _ | (u | (i | b) | u)
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (h b)
  · rfl

theorem o3_loop : ∀ (rs : List Bool) (Ls Rs : List (Γ₀ Mf)), (∀ b, Ls.headI ≠ outL Mf b) →
    Reach Mf (rs.length + 1)
      ⟨st0 Mf Tag.o3, (tp Mf (rs.map (outL Mf) ++ Ls) Rs).move Dir.left⟩
      ⟨st0 Mf Tag.o4, tp Mf Ls (rs.reverse.map (outL Mf) ++ Rs)⟩ := by
  intro rs
  induction rs with
  | nil =>
    intro Ls Rs hLs
    have s1 := step_move Mf (st0 Mf Tag.o3) (st0 Mf Tag.o4) ((tp Mf Ls Rs).move Dir.left)
      Dir.right (by
        rw [tp_left, tp_head]
        exact o3_nonout Mf _ hLs)
    rw [Tape.move_left_right] at s1
    exact s1
  | cons b rs ih =>
    intro Ls Rs hLs
    have e1 : (tp Mf ((b :: rs).map (outL Mf) ++ Ls) Rs).move Dir.left =
        tp Mf (rs.map (outL Mf) ++ Ls) (outL Mf b :: Rs) := by
      rw [tp_left]
      rfl
    rw [e1]
    have s1 := step_move Mf (st0 Mf Tag.o3) (st0 Mf Tag.o3)
      (tp Mf (rs.map (outL Mf) ++ Ls) (outL Mf b :: Rs)) Dir.left (by
        rw [tp_head]
        rfl)
    have s2 := ih Ls (outL Mf b :: Rs) hLs
    have e2 : rs.reverse.map (outL Mf) ++ outL Mf b :: Rs =
        (b :: rs).reverse.map (outL Mf) ++ Rs := by
      simp
    rw [e2] at s2
    exact (s1.trans s2).cast (by
      simp only [List.length_cons]
      omega)

theorem cell_ne_out (right : List ℕ) (i : ℕ) (b : Bool) : cell Mf right i ≠ outL Mf b := by
  unfold cell
  cases right[i]? with
  | none => intro h; cases h
  | some v => exact sy_ne_out Mf v b

theorem out_run (q : ℕ) (hq : q ≤ Mf.states) (hh : Mf.halt.getD q false = true) (h : ℕ)
    (right : List ℕ) (hb : ∀ v ∈ right, v ≤ Mf.sig + 3) :
    ∃ (Ls Rr : List (Γ₀ Mf)), (∀ b, Rr.headI ≠ outL Mf b) ∧
      Reach Mf (h + 3 * (tw right.tail).length + 6)
        ⟨(Tag.rd, toFin Mf.states q, default, default), tapeOf Mf h right⟩
        ⟨st0 Mf Tag.o4, tp Mf Ls (((tw right.tail).map (· == 2)).map (outL Mf) ++ Rr)⟩ := by
  have s0 := step_write Mf (Tag.rd, toFin Mf.states q, default, default) (st0 Mf Tag.o0)
    (tapeOf Mf h right) (tapeOf Mf h right).head (rd_halt Mf q hq _ hh)
  rw [Tape.write_self] at s0
  have s1 := o0_loop Mf right h
  have s2 := step_move Mf (st0 Mf Tag.o1) (st0 Mf Tag.o2) (tapeOf Mf 0 right) Dir.right rfl
  rw [tapeOf_right] at s2
  have e2 : tapeOf Mf (0 + 1) right =
      tp Mf [cell Mf right 0, wall Mf] (right.tail.map (sy Mf)) := by
    unfold tapeOf tp
    rw [leftOf_succ]
    simp [leftOf]
  rw [e2] at s2
  obtain ⟨Rr, hRr, s3⟩ := o2_loop Mf right.tail (fun v hv => hb v (List.mem_of_mem_tail hv))
    [cell Mf right 0, wall Mf]
  have e3 : (((tw right.tail).map (· == 2)).map (outL Mf)).reverse =
      ((tw right.tail).map (· == 2)).reverse.map (outL Mf) := by
    rw [List.map_reverse]
  rw [e3] at s3
  have s4 := o3_loop Mf ((tw right.tail).map (· == 2)).reverse [cell Mf right 0, wall Mf] Rr
    (fun b => cell_ne_out Mf right 0 b)
  rw [List.reverse_reverse] at s4
  refine ⟨[cell Mf right 0, wall Mf], Rr, hRr, ?_⟩
  exact ((((s0.trans s1).trans s2).trans s3).trans s4).cast (by
    simp only [List.length_reverse, List.length_map]
    omega)

theorem le_poly (t : ℕ → ℕ) (ht : inOPoly t) :
    ∃ d C D : ℕ, ∀ n, t n ≤ C * n ^ d + D := by
  obtain ⟨d, C, n0, H⟩ := ht
  refine ⟨d, C, maxPrefix t n0, fun n => ?_⟩
  by_cases hn : n0 ≤ n
  · exact (H n hn).trans (Nat.le_add_right _ _)
  · exact (le_maxPrefix t (Nat.le_of_lt (Nat.lt_of_not_le hn))).trans (Nat.le_add_left _ _)

theorem st_computes (hv : validFlatTM Mf) (h1 : Mf.tapes = 1) (f : List Bool → List Bool)
    (t : ℕ → ℕ) (ht : inOPoly t) (hc : CookLevin.computesInTime Mf f t) :
    PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f := by
  obtain ⟨d, C, D, hbound⟩ := le_poly t ht
  refine ⟨Mst Mf, Polynomial.C 6 * Polynomial.X +
    Polynomial.C 9 * (Polynomial.C C * Polynomial.X ^ d + Polynomial.C D) + Polynomial.C 24,
    fun x => ?_⟩
  obtain ⟨cfg, hrun, hhalt, hout⟩ := hc x
  have hb0 : ∀ v ∈ CookLevin.stringTape x, v ≤ Mf.sig + 3 := by
    intro v hv'
    simp only [CookLevin.stringTape, CookLevin.symbolsOf, List.mem_cons, List.mem_append,
      List.mem_map, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | ⟨b, -, rfl⟩ | rfl | rfl
    · omega
    · cases b <;> simp
    · omega
    · omega
  have hne0 : CookLevin.stringTape x ≠ [] := by simp [CookLevin.stringTape]
  have hlen0 : (CookLevin.stringTape x).length = x.length + 3 := by
    simp [CookLevin.stringTape, CookLevin.symbolsOf]
  obtain ⟨n, q', lft', h', right', hcfg, hn, hr, hq', hb', hne', hh', hl'⟩ :=
    run_chain Mf hv h1 (t x.length) Mf.start [] 0 (CookLevin.stringTape x) cfg
      (Nat.le_of_lt hv.1) hb0 hne0 hrun hhalt
  subst hcfg
  have hhalt' : Mf.halt.getD q' false = true := hhalt
  obtain ⟨Ls, Rr, hRr, hro⟩ := out_run Mf q' hq' hhalt' h' right' hb'
  have hout' : (tw right'.tail).map (· == 2) = f x := hout
  rw [hout'] at hro
  have hinit := init_run Mf x
  have htw := tw_length right'.tail
  have htl : right'.tail.length ≤ right'.length := by simp
  have hbx := hbound x.length
  refine ⟨⟨st0 Mf Tag.o4, tp Mf Ls ((f x).map (outL Mf) ++ Rr)⟩,
    ⟨⟨⟨_, (hinit.trans hr).trans hro⟩, ?_⟩⟩, rfl, ?_, ?_⟩
  · show 3 * x.length + 9 + n + (h' + 3 * (tw right'.tail).length + 6) ≤ _
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow]
    have e : (PvsNP.encodeString x).length = x.length := rfl
    rw [e]
    omega
  · intro i hi
    have hi' : i < (f x).length := hi
    show (tp Mf Ls ((f x).map (outL Mf) ++ Rr)).right₀.nth i = outL Mf ((f x)[i]'hi')
    unfold tp
    rw [Tape.mk'_right₀, ListBlank.nth_mk, List.getI_append _ _ _ (by simpa using hi'),
      List.getI_eq_getElem _ (by simpa using hi')]
    simp only [List.getElem_map]
  · intro b
    show (tp Mf Ls ((f x).map (outL Mf) ++ Rr)).right₀.nth (f x).length ≠ outL Mf b
    unfold tp
    rw [Tape.mk'_right₀, ListBlank.nth_mk, List.getI_append_right _ _ _ (by simp)]
    simp only [List.length_map, Nat.sub_self]
    rw [List.getI_zero_eq_headI]
    exact hRr b

end sim

end PvsNP.Units.m1_flat_to_st

/-- A function a one-tape Cook-Levin machine computes in polynomial time is computed in
polynomial time by a single-tape machine: it rewrites its input as the string tape of the
Cook-Levin model, follows that machine step by step and rewrites the output. -/
theorem PvsNP.Units.m1_flat_to_st :
    ∀ (f : List Bool → List Bool) (t : ℕ → ℕ) (M : FlatTM),
      inOPoly t → validFlatTM M → M.tapes = 1 → CookLevin.computesInTime M f t →
        PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f := by
  intro f t M ht hv h1 hc
  exact PvsNP.Units.m1_flat_to_st.st_computes M hv h1 f t ht hc
