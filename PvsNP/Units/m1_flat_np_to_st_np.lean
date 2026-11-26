import Mathlib
import PvsNP.Defs
import CookLevin

/-
Original proof of `PvsNP.Units.m1_flat_np_to_st_np`: given any language `L` in
`CookLevin.inNP`, simulates the valid 1-tape `FlatTM` verifier `M` on Mathlib's
single-tape `Turing.TM0` (`PvsNP.SingleTape.Machine (Bool ⊕ Bool) Bool`) over
`PvsNP.encodePair` and `PvsNP.encodeAnswer`.

Phase 1 formats `encodePair (x, c)` in place into `CookLevin.pairTape x c`
(`3 :: symbolsOf x ++ [0] ++ symbolsOf c ++ [0, 3]`) using a 1-bit carry shift
for `c` in `≤ 3 * (|x| + |c|) + 16` steps.
Phase 2 simulates each `FlatTM` step in at most `5` `TM0` steps (`≤ 5 * t(|x| + |c|) + 1`).
Phase 3 writes `[out (qf.val == acc)]` followed by `blank` in `4` steps and halts.
-/

namespace PvsNP.Units.m1_flat_np_to_st_np

open Turing StateTransition

/-! ### Tape coordinate invariant -/

def TapeAt {Γ : Type} [Inhabited Γ] (pos : ℤ) (T : Tape Γ) (f : ℤ → Γ) : Prop :=
  ∀ i : ℤ, T.nth i = f (pos + i)

theorem TapeAt.head {Γ : Type} [Inhabited Γ] {pos : ℤ} {T : Tape Γ} {f : ℤ → Γ}
    (h : TapeAt pos T f) : T.1 = f pos := by
  have := h 0
  simpa using this

theorem TapeAt.move_right {Γ : Type} [Inhabited Γ] {pos : ℤ} {T : Tape Γ} {f : ℤ → Γ}
    (h : TapeAt pos T f) : TapeAt (pos + 1) (T.move Dir.right) f := by
  intro i
  rw [Tape.move_right_nth, h]
  congr 1
  omega

theorem TapeAt.move_left {Γ : Type} [Inhabited Γ] {pos : ℤ} {T : Tape Γ} {f : ℤ → Γ}
    (h : TapeAt pos T f) : TapeAt (pos - 1) (T.move Dir.left) f := by
  intro i
  rw [Tape.move_left_nth, h]
  congr 1
  omega

theorem TapeAt.write {Γ : Type} [Inhabited Γ] {pos : ℤ} {T : Tape Γ} {f : ℤ → Γ}
    (h : TapeAt pos T f) (b : Γ) : TapeAt pos (T.write b) (Function.update f pos b) := by
  intro i
  rw [Tape.write_nth, h]
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

theorem TapeAt.congr {Γ : Type} [Inhabited Γ] {pos : ℤ} {T : Tape Γ} {f g : ℤ → Γ}
    (h : TapeAt pos T f) (hfg : ∀ z, f z = g z) : TapeAt pos T g :=
  fun i => (h i).trans (hfg _)

theorem listBlank_mk_nth {Γ : Type} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (ListBlank.mk l).nth n = l.getD n default := by
  induction n generalizing l with
  | zero => cases l <;> rfl
  | succ n ih =>
      rw [ListBlank.nth_succ, ListBlank.tail_mk, ih]
      cases l <;> rfl

theorem TapeAt.mk₁ {Γ : Type} [Inhabited Γ] (l : List Γ) :
    TapeAt 0 (Tape.mk₁ l) (fun z => if 0 ≤ z then l.getD z.toNat default else default) := by
  intro i
  cases i with
  | ofNat n =>
      show (Tape.mk' (ListBlank.mk []) (ListBlank.mk l)).nth n = _
      rw [Tape.mk'_nth_nat, listBlank_mk_nth]
      simp
  | negSucc n =>
      show (ListBlank.mk ([] : List Γ)).nth n = _
      rw [listBlank_mk_nth]
      have hneg : ¬ (0 : ℤ) ≤ Int.negSucc n := by omega
      simp [hneg]

/-! ### Step-counting helpers -/

theorem evals_refl {σ : Type} {f : σ → Option σ} (a : σ) :
    Nonempty (EvalsToInTime f a (some a) 0) :=
  ⟨EvalsToInTime.refl f a⟩

theorem evals_single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    Nonempty (EvalsToInTime f a (some b) 1) :=
  ⟨⟨⟨1, by simpa [Function.iterate_one, flip] using h⟩, le_rfl⟩⟩

theorem evals_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m₁ m₂ : ℕ}
    (h : Nonempty (EvalsToInTime f a b m₁)) (hle : m₁ ≤ m₂) :
    Nonempty (EvalsToInTime f a b m₂) :=
  let ⟨h⟩ := h
  ⟨⟨h.toEvalsTo, le_trans h.steps_le_m hle⟩⟩

theorem evals_trans {σ : Type} {f : σ → Option σ} {a b c : σ} {m₁ m₂ : ℕ}
    (h₁ : Nonempty (EvalsToInTime f a (some b) m₁))
    (h₂ : Nonempty (EvalsToInTime f b (some c) m₂)) :
    Nonempty (EvalsToInTime f a (some c) (m₁ + m₂)) :=
  let ⟨h₁⟩ := h₁
  let ⟨h₂⟩ := h₂
  let ht := EvalsToInTime.trans f m₁ m₂ a b (some c) h₁ h₂
  ⟨⟨ht.toEvalsTo, le_trans ht.steps_le_m (by omega)⟩⟩

/-! ### Alphabet and state space -/

inductive FlatSym (K : ℕ)
  | blank
  | wall
  | cell (v : Fin K)
  | inp (b : Bool ⊕ Bool)
  | out (b : Bool)
  deriving DecidableEq

instance (K : ℕ) : Inhabited (FlatSym K) := ⟨.blank⟩

instance (K : ℕ) : Fintype (FlatSym K) :=
  Fintype.ofEquiv (Unit ⊕ Unit ⊕ Fin K ⊕ (Bool ⊕ Bool) ⊕ Bool)
    { toFun := fun
        | .inl () => .blank
        | .inr (.inl ()) => .wall
        | .inr (.inr (.inl v)) => .cell v
        | .inr (.inr (.inr (.inl b))) => .inp b
        | .inr (.inr (.inr (.inr b))) => .out b
      invFun := fun
        | .blank => .inl ()
        | .wall => .inr (.inl ())
        | .cell v => .inr (.inr (.inl v))
        | .inp b => .inr (.inr (.inr (.inl b)))
        | .out b => .inr (.inr (.inr (.inr b)))
      left_inv := fun x => by rcases x with ⟨⟩ | ⟨⟩ | v | b | b <;> rfl
      right_inv := fun x => by cases x <;> rfl }

instance : Fintype TMMove :=
  Fintype.ofList [TMMove.Lmove, TMMove.Rmove, TMMove.Nmove] (fun x => by cases x <;> simp)

inductive FlatSt (K S : ℕ)
  | init0
  | init1
  | init2
  | init3
  | init4
  | init5
  | convX
  | convXNext
  | shiftMove (b : Bool)
  | shift (b : Bool)
  | initEnd0
  | initEnd1
  | initEnd2
  | initEnd3
  | initRew
  | sim (q : Fin S)
  | chkFront (q' : Fin S) (v : Fin K) (d : TMMove)
  | doWrite (q' : Fin S) (v : Fin K) (d : TMMove)
  | doMove (q' : Fin S) (d : TMMove)
  | chkWall (q' : Fin S)
  | writeAns (b : Bool)
  | ansMoveR
  | ansClear
  | ansBack
  | outHalt
  deriving DecidableEq

instance (K S : ℕ) : Inhabited (FlatSt K S) := ⟨.init0⟩

instance (K S : ℕ) : Fintype (FlatSt K S) := by
  let T :=
    Fin 17 ⊕ Bool ⊕ Bool ⊕ Bool ⊕ Fin S ⊕ (Fin S × Fin K × TMMove) ⊕
    (Fin S × Fin K × TMMove) ⊕ (Fin S × TMMove) ⊕ Fin S
  refine Fintype.ofEquiv T
    { toFun := fun
        | .inl i =>
            match i.val, i.isLt with
            | 0, _ => .init0
            | 1, _ => .init1
            | 2, _ => .init2
            | 3, _ => .init3
            | 4, _ => .init4
            | 5, _ => .init5
            | 6, _ => .convX
            | 7, _ => .convXNext
            | 8, _ => .initEnd0
            | 9, _ => .initEnd1
            | 10, _ => .initEnd2
            | 11, _ => .initEnd3
            | 12, _ => .initRew
            | 13, _ => .ansMoveR
            | 14, _ => .ansClear
            | 15, _ => .ansBack
            | 16, _ => .outHalt
            | _ + 17, h => absurd h (by omega)
        | .inr (.inl b) => .shiftMove b
        | .inr (.inr (.inl b)) => .shift b
        | .inr (.inr (.inr (.inl b))) => .writeAns b
        | .inr (.inr (.inr (.inr (.inl q)))) => .sim q
        | .inr (.inr (.inr (.inr (.inr (.inl (q, v, d)))))) => .chkFront q v d
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl (q, v, d))))))) => .doWrite q v d
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, d)))))))) => .doMove q d
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q))))))) => .chkWall q
      invFun := fun
        | .init0 => .inl ⟨0, by decide⟩
        | .init1 => .inl ⟨1, by decide⟩
        | .init2 => .inl ⟨2, by decide⟩
        | .init3 => .inl ⟨3, by decide⟩
        | .init4 => .inl ⟨4, by decide⟩
        | .init5 => .inl ⟨5, by decide⟩
        | .convX => .inl ⟨6, by decide⟩
        | .convXNext => .inl ⟨7, by decide⟩
        | .initEnd0 => .inl ⟨8, by decide⟩
        | .initEnd1 => .inl ⟨9, by decide⟩
        | .initEnd2 => .inl ⟨10, by decide⟩
        | .initEnd3 => .inl ⟨11, by decide⟩
        | .initRew => .inl ⟨12, by decide⟩
        | .ansMoveR => .inl ⟨13, by decide⟩
        | .ansClear => .inl ⟨14, by decide⟩
        | .ansBack => .inl ⟨15, by decide⟩
        | .outHalt => .inl ⟨16, by decide⟩
        | .shiftMove b => .inr (.inl b)
        | .shift b => .inr (.inr (.inl b))
        | .writeAns b => .inr (.inr (.inr (.inl b)))
        | .sim q => .inr (.inr (.inr (.inr (.inl q))))
        | .chkFront q v d => .inr (.inr (.inr (.inr (.inr (.inl (q, v, d))))))
        | .doWrite q v d => .inr (.inr (.inr (.inr (.inr (.inr (.inl (q, v, d)))))))
        | .doMove q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, d))))))))
        | .chkWall q => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q)))))))
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨i, hi⟩ | b | b | b | q | ⟨q, v, d⟩ | ⟨q, v, d⟩ | ⟨q, d⟩ | q
    · interval_cases i <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro x
    cases x <;> rfl

/-! ### Machine construction -/

def readSym {K : ℕ} : FlatSym K → Option ℕ
  | .cell v => some v.val
  | _ => none

def lookupEntry (M : FlatTM) (q : ℕ) (sym : Option ℕ) : Option FlatTMTransEntry :=
  M.trans.find? (fun e => e.src_state == q && decide (e.src_tape_vals = [sym]))

def mkDelta (M : FlatTM) (acc : ℕ) (hM : validFlatTM M) (hT1 : M.tapes = 1) :
    TM0.Machine (FlatSym (max M.sig 4)) (FlatSt (max M.sig 4) M.states)
  | .init0, _ => some (.init1, .move .left)
  | .init1, _ => some (.init2, .write (.cell ⟨3, by omega⟩))
  | .init2, _ => some (.init3, .move .left)
  | .init3, _ => some (.init4, .write .wall)
  | .init4, _ => some (.init5, .move .right)
  | .init5, _ => some (.convX, .move .right)
  | .convX, .inp (.inl b) =>
      some (.convXNext, .write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩)))
  | .convX, .inp (.inr b) =>
      some (.shiftMove b, .write (.cell ⟨0, by omega⟩))
  | .convX, _ => some (.initEnd0, .write (.cell ⟨0, by omega⟩))
  | .convXNext, _ => some (.convX, .move .right)
  | .shiftMove b, _ => some (.shift b, .move .right)
  | .shift b, .inp (.inr b') =>
      some (.shiftMove b', .write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩)))
  | .shift b, _ =>
      some (.initEnd0, .write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩)))
  | .initEnd0, _ => some (.initEnd1, .move .right)
  | .initEnd1, _ => some (.initEnd2, .write (.cell ⟨0, by omega⟩))
  | .initEnd2, _ => some (.initEnd3, .move .right)
  | .initEnd3, _ => some (.initRew, .write (.cell ⟨3, by omega⟩))
  | .initRew, .wall => some (.sim ⟨M.start, hM.1⟩, .move .right)
  | .initRew, _ => some (.initRew, .move .left)
  | .sim q, a =>
      if M.halt.getD q.val false then
        some (.writeAns (q.val == acc), .write a)
      else
        match hFind : lookupEntry M q.val (readSym a) with
        | none => none
        | some e =>
            have hmem : e ∈ M.trans := List.mem_of_find?_eq_some hFind
            have hval := hM.2.2 e hmem
            have hdst : e.dst_state < M.states := hval.2.1
            have hwlen : e.dst_write_vals.length = 1 := hval.2.2.2.1.trans hT1
            have hmlen : e.move_dirs.length = 1 := hval.2.2.2.2.1.trans hT1
            let wv : Option ℕ := e.dst_write_vals[0]'(by omega)
            let mv : TMMove := e.move_dirs[0]'(by omega)
            match hwv : wv with
            | none => some (.doMove ⟨e.dst_state, hdst⟩ mv, .write a)
            | some v =>
                have hvmem : some v ∈ e.dst_write_vals := by
                  rw [← hwv]; exact List.getElem_mem _
                have hv : v < max M.sig 4 :=
                  Nat.lt_of_lt_of_le (hval.2.2.2.2.2.2 (some v) hvmem) (Nat.le_max_left _ _)
                match a with
                | .cell _ => some (.doMove ⟨e.dst_state, hdst⟩ mv, .write (.cell ⟨v, hv⟩))
                | _ => some (.chkFront ⟨e.dst_state, hdst⟩ ⟨v, hv⟩ mv, .move .left)
  | .chkFront q' v d, .blank => some (.doMove q' d, .move .right)
  | .chkFront q' v d, _ => some (.doWrite q' v d, .move .right)
  | .doWrite q' v d, _ => some (.doMove q' d, .write (.cell v))
  | .doMove q' .Nmove, a => some (.sim q', .write a)
  | .doMove q' .Rmove, _ => some (.sim q', .move .right)
  | .doMove q' .Lmove, _ => some (.chkWall q', .move .left)
  | .chkWall q', .wall => some (.sim q', .move .right)
  | .chkWall q', a => some (.sim q', .write a)
  | .writeAns b, _ => some (.ansMoveR, .write (.out b))
  | .ansMoveR, _ => some (.ansClear, .move .right)
  | .ansClear, _ => some (.ansBack, .write .blank)
  | .ansBack, _ => some (.outHalt, .move .left)
  | .outHalt, _ => none

abbrev mkMachine (M : FlatTM) (acc : ℕ) (hM : validFlatTM M) (hT1 : M.tapes = 1) :
    PvsNP.SingleTape.Machine (Bool ⊕ Bool) Bool where
  Γ := FlatSym (max M.sig 4)
  Λ := FlatSt (max M.sig 4) M.states
  inp := FlatSym.inp
  out := FlatSym.out
  inp_injective := fun _ _ h => FlatSym.inp.inj h
  out_injective := fun _ _ h => FlatSym.out.inj h
  inp_ne_blank := fun _ h => by cases h
  out_ne_blank := fun _ h => by cases h
  δ := mkDelta M acc hM hT1

/-! ### Board representations -/

def flatBoard (K : ℕ) (right : List ℕ) : ℤ → FlatSym K := fun z =>
  if z = -2 then .wall
  else if h : -1 ≤ z ∧ (z + 1).toNat < right.length then
    if hv : right[(z + 1).toNat]'h.2 < K then .cell ⟨_, hv⟩ else .blank
  else .blank

theorem flatBoard_wall (K : ℕ) (right : List ℕ) : flatBoard K right (-2) = .wall := by
  simp [flatBoard]

theorem flatBoard_lt (K : ℕ) (right : List ℕ) (z : ℤ) (hz : z < -2) :
    flatBoard K right z = .blank := by
  have h1 : z ≠ -2 := by omega
  have h2 : ¬ (-1 ≤ z ∧ (z + 1).toNat < right.length) := by omega
  simp [flatBoard, h1, h2]

theorem flatBoard_ge (K : ℕ) (right : List ℕ) (z : ℤ) (hz : (right.length : ℤ) - 1 ≤ z) :
    flatBoard K right z = .blank := by
  have h1 : z ≠ -2 := by omega
  have h2 : ¬ (-1 ≤ z ∧ (z + 1).toNat < right.length) := by omega
  simp [flatBoard, h1, h2]

theorem flatBoard_at (K : ℕ) (right : List ℕ) (hr : ∀ v ∈ right, v < K) (j : ℕ)
    (hj : j < right.length) :
    flatBoard K right ((j : ℤ) - 1) = .cell ⟨right[j], hr _ (List.getElem_mem hj)⟩ := by
  have h1 : ((j : ℤ) - 1) ≠ -2 := by omega
  have h2 : -1 ≤ (j : ℤ) - 1 ∧ (((j : ℤ) - 1) + 1).toNat < right.length := by
    constructor
    · omega
    · have : (((j : ℤ) - 1) + 1).toNat = j := by omega
      rw [this]; exact hj
  have hidx : (((j : ℤ) - 1) + 1).toNat = j := by omega
  have hv : right[(((j : ℤ) - 1) + 1).toNat]'h2.2 < K := by
    simp only [hidx]; exact hr _ (List.getElem_mem hj)
  unfold flatBoard
  rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
    dite_eq_left_of_eq_true (eq_true h2),
    dite_eq_left_of_eq_true (eq_true hv)]
  congr 1
  apply Fin.ext
  simp

theorem flatBoard_readSym (K : ℕ) (right : List ℕ) (hr : ∀ v ∈ right, v < K) (h : ℕ) :
    readSym (flatBoard K right ((h : ℤ) - 1)) = currentTapeSymbol ([], h, right) := by
  unfold currentTapeSymbol
  by_cases hh : h < right.length
  · rw [flatBoard_at K right hr h hh, dite_eq_left_of_eq_true (eq_true hh)]
    rfl
  · rw [flatBoard_ge K right ((h : ℤ) - 1) (by omega), dite_eq_right_of_eq_false (eq_false hh)]
    rfl

theorem flatBoard_update_inRange (K : ℕ) (right : List ℕ) (hr : ∀ v ∈ right, v < K)
    (h : ℕ) (hh : h < right.length) (v : Fin K) :
    ∀ z, Function.update (flatBoard K right) ((h : ℤ) - 1) (.cell v) z =
      flatBoard K (right.take h ++ v.val :: right.drop (h + 1)) z := by
  intro z
  set right' := right.take h ++ v.val :: right.drop (h + 1)
  have hlen : right'.length = right.length := by
    simp [right', List.length_take, List.length_drop] <;> omega
  have hr' : ∀ u ∈ right', u < K := by
    intro u hu
    simp only [right', List.mem_append, List.mem_cons] at hu
    rcases hu with h1 | rfl | h2
    · exact hr u (List.mem_of_mem_take h1)
    · exact v.isLt
    · exact hr u (List.mem_of_mem_drop h2)
  by_cases hz : z = (h : ℤ) - 1
  · subst hz
    rw [Function.update_self, flatBoard_at K right' hr' h (by omega)]
    congr 1
    apply Fin.ext
    have hget : right'[h]'(by omega) = v.val := by
      simp only [right']
      rw [List.getElem_append_right (by simp)]
      have hzero : h - (right.take h).length = 0 := by simp <;> omega
      simp only [hzero, List.getElem_cons_zero]
    exact hget.symm
  · rw [Function.update_of_ne hz]
    by_cases hneg : z = -2
    · subst hneg; rw [flatBoard_wall, flatBoard_wall]
    · by_cases hlt : z < -2
      · rw [flatBoard_lt K right z hlt, flatBoard_lt K right' z hlt]
      · by_cases hge : (right.length : ℤ) - 1 ≤ z
        · rw [flatBoard_ge K right z hge, flatBoard_ge K right' z (by omega)]
        · have hj : ∃ j : ℕ, z = (j : ℤ) - 1 ∧ j < right.length ∧ j ≠ h :=
            ⟨(z + 1).toNat, by omega, by omega, by omega⟩
          rcases hj with ⟨j, rfl, hjl, hjne⟩
          rw [flatBoard_at K right hr j hjl, flatBoard_at K right' hr' j (by omega)]
          congr 1
          apply Fin.ext
          change right[j] = right'[j]'(by omega)
          by_cases hltj : j < h
          · simp only [right']
            rw [List.getElem_append_left (by simp <;> omega), List.getElem_take]
          · have hgtj : h < j := by omega
            simp only [right']
            rw [List.getElem_append_right (by simp <;> omega)]
            have htk : (right.take h).length = h := by simp <;> omega
            have hsub : j - (right.take h).length = (j - h - 1) + 1 := by omega
            simp only [hsub, List.getElem_cons_succ, List.getElem_drop]
            congr 1
            omega

theorem flatBoard_update_append (K : ℕ) (right : List ℕ) (hr : ∀ v ∈ right, v < K) (v : Fin K) :
    ∀ z, Function.update (flatBoard K right) ((right.length : ℤ) - 1) (.cell v) z =
      flatBoard K (right ++ [v.val]) z := by
  intro z
  have hr' : ∀ u ∈ right ++ [v.val], u < K := by
    intro u hu
    rcases List.mem_append.mp hu with h1 | h2
    · exact hr u h1
    · simp only [List.mem_singleton] at h2; subst h2; exact v.isLt
  by_cases hz : z = (right.length : ℤ) - 1
  · subst hz
    rw [Function.update_self, flatBoard_at K (right ++ [v.val]) hr' right.length (by simp)]
    congr 1; apply Fin.ext; simp
  · rw [Function.update_of_ne hz]
    by_cases hneg : z = -2
    · subst hneg; rw [flatBoard_wall, flatBoard_wall]
    · by_cases hlt : z < -2
      · rw [flatBoard_lt K right z hlt, flatBoard_lt K (right ++ [v.val]) z hlt]
      · by_cases hge : ((right ++ [v.val]).length : ℤ) - 1 ≤ z
        · rw [flatBoard_ge K right z (by simp at hge; omega),
            flatBoard_ge K (right ++ [v.val]) z hge]
        · have hj : ∃ j : ℕ, z = (j : ℤ) - 1 ∧ j < right.length :=
            ⟨(z + 1).toNat, by omega, by simp at hge; omega⟩
          rcases hj with ⟨j, rfl, hjl⟩
          rw [flatBoard_at K right hr j hjl,
            flatBoard_at K (right ++ [v.val]) hr' j (by simp <;> omega)]
          congr 1; apply Fin.ext
          exact (List.getElem_append_left hjl).symm

/-! ### Phase 1 boards for formatting `encodePair (x, c)` into `pairTape x c` -/

def convXBoard (K : ℕ) (hK : 4 ≤ K) (x c : List Bool) (i : ℕ) : ℤ → FlatSym K := fun z =>
  if z = -2 then .wall
  else if z = -1 then .cell ⟨3, by omega⟩
  else if h : 0 ≤ z ∧ z.toNat < x.length then
    if z.toNat < i then
      .cell (if x[z.toNat]'h.2 then ⟨2, by omega⟩ else ⟨1, by omega⟩)
    else
      .inp (.inl (x[z.toNat]'h.2))
  else if hc : 0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length then
    .inp (.inr ((c)[z.toNat - x.length]'hc.2.2))
  else .blank

def shiftBoard (K : ℕ) (hK : 4 ≤ K) (x c : List Bool) (j : ℕ) : ℤ → FlatSym K := fun z =>
  if z = -2 then .wall
  else if z = -1 then .cell ⟨3, by omega⟩
  else if hx : 0 ≤ z ∧ z.toNat < x.length then
    .cell (if x[z.toNat]'hx.2 then ⟨2, by omega⟩ else ⟨1, by omega⟩)
  else if z = (x.length : ℤ) then .cell ⟨0, by omega⟩
  else if hcl : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧ z.toNat < x.length + 1 + j ∧
      z.toNat - (x.length + 1) < c.length then
    .cell (if (c)[z.toNat - (x.length + 1)]'hcl.2.2.2 then ⟨2, by omega⟩ else ⟨1, by omega⟩)
  else if hcr : 0 ≤ z ∧ x.length + 1 + j ≤ z.toNat ∧ z.toNat - x.length < c.length then
    .inp (.inr ((c)[z.toNat - x.length]'hcr.2.2))
  else .blank

section sim
variable (M : FlatTM) (acc : ℕ) (hM : validFlatTM M) (hT1 : M.tapes = 1)

private abbrev FlatSM := mkMachine M acc hM hT1

theorem step_eq (q : FlatSt (max M.sig 4) M.states) (T : Tape (FlatSym (max M.sig 4))) :
    (FlatSM M acc hM hT1).step ⟨q, T⟩ =
      match mkDelta M acc hM hT1 q T.head with
      | none => none
      | some (q', .move d) => some ⟨q', T.move d⟩
      | some (q', .write a) => some ⟨q', T.write a⟩ := by
  unfold PvsNP.SingleTape.Machine.step TM0.step
  dsimp only [FlatSM, mkMachine]
  generalize mkDelta M acc hM hT1 q T.head = o
  cases o with
  | none => rfl
  | some p =>
      rcases p with ⟨q', act⟩
      cases act <;> rfl

theorem tape_write_head {Γ : Type} [Inhabited Γ] (T : Tape Γ) : T.write T.head = T :=
  Tape.write_self T

theorem tape_move_lr {Γ : Type} [Inhabited Γ] (T : Tape Γ) : (T.move .left).move .right = T :=
  Tape.move_left_right T

theorem mkDelta_sim_none (q : Fin M.states) (a : FlatSym (max M.sig 4))
    (hnh : M.halt.getD q.val false = false) (e : FlatTMTransEntry)
    (hFind : lookupEntry M q.val (readSym a) = some e)
    (mv : TMMove) (hw_eq : e.dst_write_vals = [none]) (hm_eq : e.move_dirs = [mv])
    (hdst : e.dst_state < M.states) :
    mkDelta M acc hM hT1 (.sim q) a = some (.doMove ⟨e.dst_state, hdst⟩ mv, .write a) := by
  unfold mkDelta
  simp only [hnh, Bool.false_eq_true, ite_false]
  split
  · rename_i hnone; rw [hFind] at hnone; cases hnone
  · rename_i e' hsome
    rw [hFind] at hsome
    cases Option.some.inj hsome
    split
    · rename_i hwv0
      have hmv0 : e.move_dirs[0]'(by simp [hm_eq]) = mv := by simp [hm_eq]
      simp [hmv0]
    · rename_i v hwv0
      have : e.dst_write_vals[0]'(by simp [hw_eq]) = none := by simp [hw_eq]
      rw [this] at hwv0; cases hwv0

theorem mkDelta_sim_some_cell (q : Fin M.states) (u : Fin (max M.sig 4))
    (hnh : M.halt.getD q.val false = false) (e : FlatTMTransEntry)
    (hFind : lookupEntry M q.val (readSym (.cell u)) = some e)
    (v : ℕ) (hv : v < max M.sig 4) (mv : TMMove)
    (hw_eq : e.dst_write_vals = [some v]) (hm_eq : e.move_dirs = [mv])
    (hdst : e.dst_state < M.states) :
    mkDelta M acc hM hT1 (.sim q) (.cell u) =
      some (.doMove ⟨e.dst_state, hdst⟩ mv, .write (.cell ⟨v, hv⟩)) := by
  unfold mkDelta
  simp only [hnh, Bool.false_eq_true, ite_false]
  split
  · rename_i hnone; rw [hFind] at hnone; cases hnone
  · rename_i e' hsome
    rw [hFind] at hsome
    cases Option.some.inj hsome
    split
    · rename_i hwv0
      have : e.dst_write_vals[0]'(by simp [hw_eq]) = some v := by simp [hw_eq]
      rw [this] at hwv0; cases hwv0
    · rename_i v' hwv0
      have : e.dst_write_vals[0]'(by simp [hw_eq]) = some v := by simp [hw_eq]
      rw [this] at hwv0
      cases Option.some.inj hwv0
      have hmv0 : e.move_dirs[0]'(by simp [hm_eq]) = mv := by simp [hm_eq]
      simp [hmv0]

theorem mkDelta_sim_some_blank (q : Fin M.states)
    (hnh : M.halt.getD q.val false = false) (e : FlatTMTransEntry)
    (hFind : lookupEntry M q.val (readSym (.blank : FlatSym (max M.sig 4))) = some e)
    (v : ℕ) (hv : v < max M.sig 4) (mv : TMMove)
    (hw_eq : e.dst_write_vals = [some v]) (hm_eq : e.move_dirs = [mv])
    (hdst : e.dst_state < M.states) :
    mkDelta M acc hM hT1 (.sim q) .blank =
      some (.chkFront ⟨e.dst_state, hdst⟩ ⟨v, hv⟩ mv, .move .left) := by
  unfold mkDelta
  simp only [hnh, Bool.false_eq_true, ite_false]
  split
  · rename_i hnone; rw [hFind] at hnone; cases hnone
  · rename_i e' hsome
    rw [hFind] at hsome
    cases Option.some.inj hsome
    split
    · rename_i hwv0
      have : e.dst_write_vals[0]'(by simp [hw_eq]) = some v := by simp [hw_eq]
      rw [this] at hwv0; cases hwv0
    · rename_i v' hwv0
      have : e.dst_write_vals[0]'(by simp [hw_eq]) = some v := by simp [hw_eq]
      rw [this] at hwv0
      cases Option.some.inj hwv0
      have hmv0 : e.move_dirs[0]'(by simp [hm_eq]) = mv := by simp [hm_eq]
      simp [hmv0]

/-! ### Phase 1 proofs -/

theorem encodePair_eq (x c : List Bool) :
    PvsNP.encodePair (x, c) = x.map Sum.inl ++ c.map Sum.inr := rfl

theorem phase1_preamble (x c : List Bool) :
    ∃ T : Tape (FlatSym (max M.sig 4)),
      TapeAt 0 T (convXBoard (max M.sig 4) (Nat.le_max_right _ _) x c 0) ∧
      Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step
        ((FlatSM M acc hM hT1).init (PvsNP.encodePair (x, c))) (some ⟨.convX, T⟩) 6) := by
  let inpXC : List (FlatSym (max M.sig 4)) := (x.map Sum.inl ++ c.map Sum.inr).map FlatSym.inp
  have hT0 : TapeAt 0 (Tape.mk₁ inpXC)
      (fun z => if 0 ≤ z then inpXC.getD z.toNat (.blank : FlatSym (max M.sig 4)) else .blank) :=
    TapeAt.mk₁ inpXC
  let c0 : (FlatSM M acc hM hT1).Cfg := (FlatSM M acc hM hT1).init (PvsNP.encodePair (x, c))
  let T1 := (Tape.mk₁ inpXC).move .left
  let T2 := T1.write (.cell ⟨3, by omega⟩)
  let T3 := T2.move .left
  let T4 := T3.write .wall
  let T5 := T4.move .right
  let T6 := T5.move .right
  have s1 : (FlatSM M acc hM hT1).step c0 = some ⟨.init1, T1⟩ := rfl
  have s2 : (FlatSM M acc hM hT1).step ⟨.init1, T1⟩ = some ⟨.init2, T2⟩ := rfl
  have s3 : (FlatSM M acc hM hT1).step ⟨.init2, T2⟩ = some ⟨.init3, T3⟩ := rfl
  have s4 : (FlatSM M acc hM hT1).step ⟨.init3, T3⟩ = some ⟨.init4, T4⟩ := rfl
  have s5 : (FlatSM M acc hM hT1).step ⟨.init4, T4⟩ = some ⟨.init5, T5⟩ := rfl
  have s6 : (FlatSM M acc hM hT1).step ⟨.init5, T5⟩ = some ⟨.convX, T6⟩ := rfl
  refine ⟨T6, ?_, ?_⟩
  · have h6 : TapeAt (((0 : ℤ) - 1 - 1) + 1 + 1) T6
        (Function.update (Function.update
          (fun z => if 0 ≤ z then inpXC.getD z.toNat .blank else .blank)
          (-1) (.cell ⟨3, by omega⟩)) (-2) .wall) :=
      ((((hT0.move_left.write _).move_left.write _).move_right).move_right)
    have hpos : (((0 : ℤ) - 1 - 1) + 1 + 1) = 0 := by omega
    rw [hpos] at h6
    refine h6.congr fun z => ?_
    unfold convXBoard
    by_cases h2 : z = -2
    · subst h2; simp
    · rw [Function.update_of_ne h2]
      by_cases h1 : z = -1
      · subst h1; simp
      · rw [Function.update_of_ne h1]
        simp only [h2, h1, ite_false]
        by_cases h0 : 0 ≤ z
        · rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)]
          by_cases hx : z.toNat < x.length
          · have hcx : 0 ≤ z ∧ z.toNat < x.length := ⟨h0, hx⟩
            rw [dite_eq_left_of_eq_true (eq_true hcx),
              ite_eq_right_iff.mpr (fun h => absurd h (Nat.not_lt_zero _))]
            simp only [inpXC]
            rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getElem_map,
              List.getElem_append_left (by simp [hx]), List.getElem_map]
          · have hncx : ¬ (0 ≤ z ∧ z.toNat < x.length) := fun h => hx h.2
            rw [dite_eq_right_of_eq_false (eq_false hncx)]
            by_cases hcl : z.toNat - x.length < c.length
            · have hcc : 0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length :=
                ⟨h0, by omega, hcl⟩
              rw [dite_eq_left_of_eq_true (eq_true hcc)]
              simp only [inpXC]
              rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getElem_map,
                List.getElem_append_right (by simp <;> omega)]
              simp only [List.length_map, List.getElem_map]
            · have hncc : ¬ (0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length) :=
                fun h => hcl h.2.2
              rw [dite_eq_right_of_eq_false (eq_false hncc)]
              simp only [inpXC]
              rw [List.getD_eq_default _ _ (by simp <;> omega)]
        · have hncx : ¬ (0 ≤ z ∧ z.toNat < x.length) := fun h => h0 h.1
          have hncc : ¬ (0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length) :=
            fun h => h0 h.1
          rw [ite_eq_right_iff.mpr (fun h => absurd h h0),
            dite_eq_right_of_eq_false (eq_false hncx),
            dite_eq_right_of_eq_false (eq_false hncc)]
  · exact evals_trans (evals_single s1)
      (evals_trans (evals_single s2)
        (evals_trans (evals_single s3)
          (evals_trans (evals_single s4)
            (evals_trans (evals_single s5) (evals_single s6)))))

theorem phase1_convX_loop (x c : List Bool) :
    ∀ (i : ℕ), i ≤ x.length → ∀ T : Tape (FlatSym (max M.sig 4)),
      TapeAt (i : ℤ) T (convXBoard (max M.sig 4) (Nat.le_max_right _ _) x c i) →
      ∃ T' : Tape (FlatSym (max M.sig 4)),
        TapeAt (x.length : ℤ) T' (convXBoard (max M.sig 4) (Nat.le_max_right _ _) x c x.length) ∧
        Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.convX, T⟩ (some ⟨.convX, T'⟩)
          (2 * (x.length - i))) := by
  intro i hi
  induction hrem : x.length - i generalizing i with
  | zero =>
      intro T hT
      have hieq : i = x.length := by omega
      subst hieq
      exact ⟨T, hT, evals_refl _⟩
  | succ r ih =>
      intro T hT
      have hilt : i < x.length := by omega
      have hhead : T.head = .inp (.inl (x[i]'hilt)) := by
        rw [hT.head]
        unfold convXBoard
        have h1 : (i : ℤ) ≠ -2 := by omega
        have h2 : (i : ℤ) ≠ -1 := by omega
        have h3 : (0 : ℤ) ≤ i ∧ (i : ℤ).toNat < x.length := ⟨by omega, by simpa using hilt⟩
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_left_of_eq_true (eq_true h3)]
        have hnotlt : ¬ (i : ℤ).toNat < i := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnotlt)]
        congr 2
      let b := x[i]'hilt
      let T1 := T.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))
      let T2 := T1.move .right
      have s1 : (FlatSM M acc hM hT1).step ⟨.convX, T⟩ = some ⟨.convXNext, T1⟩ := by
        rw [step_eq M acc hM hT1, hhead]; rfl
      have s2 : (FlatSM M acc hM hT1).step ⟨.convXNext, T1⟩ = some ⟨.convX, T2⟩ := rfl
      have hT2 : TapeAt ((i + 1 : ℕ) : ℤ) T2
          (convXBoard (max M.sig 4) (Nat.le_max_right _ _) x c (i + 1)) := by
        have h' := (hT.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))).move_right
        have hcast : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
        rw [hcast] at h'
        refine h'.congr fun z => ?_
        by_cases hzi : z = (i : ℤ)
        · subst hzi
          rw [Function.update_self]
          unfold convXBoard
          have h1 : (i : ℤ) ≠ -2 := by omega
          have h2 : (i : ℤ) ≠ -1 := by omega
          have h3 : (0 : ℤ) ≤ i ∧ (i : ℤ).toNat < x.length := ⟨by omega, by simpa using hilt⟩
          have h4 : (i : ℤ).toNat < i + 1 := by omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
            ite_eq_right_iff.mpr (fun h => absurd h h2),
            dite_eq_left_of_eq_true (eq_true h3),
            ite_eq_left_iff.mpr (fun h => absurd h4 h)]
          simp [b]
        · rw [Function.update_of_ne hzi]
          unfold convXBoard
          by_cases h2 : z = -2
          · simp [h2]
          · by_cases h1 : z = -1
            · simp [h1]
            · simp only [h2, h1, ite_false]
              by_cases h0 : 0 ≤ z ∧ z.toNat < x.length
              · rw [dite_eq_left_of_eq_true (eq_true h0), dite_eq_left_of_eq_true (eq_true h0)]
                have hiff : z.toNat < i ↔ z.toNat < i + 1 := by omega
                simp [hiff]
              · rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_right_of_eq_false (eq_false h0)]
      obtain ⟨T', hT', hev⟩ := ih (i + 1) (by omega) (by omega) T2 hT2
      exact ⟨T', hT', evals_mono (evals_trans (evals_single s1)
        (evals_trans (evals_single s2) hev)) (by omega)⟩

theorem phase1_shift_loop (x c : List Bool) (_hcpos : 0 < c.length) :
    ∀ (j : ℕ) (hj : j < c.length) (T : Tape (FlatSym (max M.sig 4))),
      TapeAt ((x.length + 1 + j : ℕ) : ℤ) T
        (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c j) →
      ∃ T' : Tape (FlatSym (max M.sig 4)),
        TapeAt ((x.length + c.length : ℕ) : ℤ) T'
          (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c c.length) ∧
        Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step
          ⟨.shift ((c)[j]'hj), T⟩ (some ⟨.initEnd0, T'⟩)
          (2 * (c.length - 1 - j) + 1)) := by
  intro j hj
  induction hrem : c.length - 1 - j generalizing j with
  | zero =>
      intro T hT
      have hjeq : j + 1 = c.length := by omega
      have hhd : T.head = .blank := by
        rw [hT.head]
        unfold shiftBoard
        have h1 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -2 := by omega
        have h2 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -1 := by omega
        have h3 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length) := by omega
        have h4 : ((x.length + 1 + j : ℕ) : ℤ) ≠ (x.length : ℤ) := by omega
        have h5 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            x.length + 1 ≤ ((x.length + 1 + j : ℕ) : ℤ).toNat ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length + 1 + j ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat - (x.length + 1) < c.length) := by omega
        have h6 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            x.length + 1 + j ≤ ((x.length + 1 + j : ℕ) : ℤ).toNat ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat - x.length < c.length) := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_right_of_eq_false (eq_false h3),
          ite_eq_right_iff.mpr (fun h => absurd h h4),
          dite_eq_right_of_eq_false (eq_false h5),
          dite_eq_right_of_eq_false (eq_false h6)]
      let b := (c)[j]'hj
      let T1 := T.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))
      have s1 : (FlatSM M acc hM hT1).step ⟨.shift b, T⟩ = some ⟨.initEnd0, T1⟩ := by
        rw [step_eq M acc hM hT1, hhd]; rfl
      have hT1' : TapeAt ((x.length + c.length : ℕ) : ℤ) T1
          (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c c.length) := by
        have h' := hT.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))
        have hpos : ((x.length + 1 + j : ℕ) : ℤ) = ((x.length + c.length : ℕ) : ℤ) := by omega
        rw [hpos] at h'
        refine h'.congr fun z => ?_
        by_cases hz : z = ((x.length + c.length : ℕ) : ℤ)
        · subst hz
          rw [Function.update_self]
          unfold shiftBoard
          have h1 : ((x.length + c.length : ℕ) : ℤ) ≠ -2 := by omega
          have h2 : ((x.length + c.length : ℕ) : ℤ) ≠ -1 := by omega
          have h3 : ¬ (0 ≤ ((x.length + c.length : ℕ) : ℤ) ∧
              ((x.length + c.length : ℕ) : ℤ).toNat < x.length) := by omega
          have h4 : ((x.length + c.length : ℕ) : ℤ) ≠ (x.length : ℤ) := by omega
          have h5 : 0 ≤ ((x.length + c.length : ℕ) : ℤ) ∧
              x.length + 1 ≤ ((x.length + c.length : ℕ) : ℤ).toNat ∧
              ((x.length + c.length : ℕ) : ℤ).toNat < x.length + 1 + c.length ∧
              ((x.length + c.length : ℕ) : ℤ).toNat - (x.length + 1) < c.length := by omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
            ite_eq_right_iff.mpr (fun h => absurd h h2),
            dite_eq_right_of_eq_false (eq_false h3),
            ite_eq_right_iff.mpr (fun h => absurd h h4),
            dite_eq_left_of_eq_true (eq_true h5)]
          have hidx : ((x.length + c.length : ℕ) : ℤ).toNat - (x.length + 1) = j := by omega
          simp only [b, hidx]
        · rw [Function.update_of_ne hz]
          unfold shiftBoard
          by_cases h1 : z = -2
          · simp [h1]
          · by_cases h2 : z = -1
            · simp [h2]
            · simp only [h1, h2, ite_false]
              by_cases hx : 0 ≤ z ∧ z.toNat < x.length
              · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_left_of_eq_true (eq_true hx)]
              · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_right_of_eq_false (eq_false hx)]
                by_cases hsep : z = (x.length : ℤ)
                · simp [hsep]
                · simp only [hsep, ite_false]
                  have hne_end : z.toNat ≠ x.length + 1 + j ∨ z < 0 := by omega
                  by_cases hcl1 : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧ z.toNat < x.length + 1 + j ∧
                      z.toNat - (x.length + 1) < c.length
                  · have hcl2 : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧
                        z.toNat < x.length + 1 + c.length ∧
                        z.toNat - (x.length + 1) < c.length := ⟨hcl1.1, hcl1.2.1, by omega, hcl1.2.2.2⟩
                    rw [dite_eq_left_of_eq_true (eq_true hcl1),
                      dite_eq_left_of_eq_true (eq_true hcl2)]
                  · have hcl2 : ¬ (0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧
                        z.toNat < x.length + 1 + c.length ∧
                        z.toNat - (x.length + 1) < c.length) := by omega
                    have hcr1 : ¬ (0 ≤ z ∧ x.length + 1 + j ≤ z.toNat ∧
                        z.toNat - x.length < c.length) := by omega
                    have hcr2 : ¬ (0 ≤ z ∧ x.length + 1 + c.length ≤ z.toNat ∧
                        z.toNat - x.length < c.length) := by omega
                    rw [dite_eq_right_of_eq_false (eq_false hcl1),
                      dite_eq_right_of_eq_false (eq_false hcr1),
                      dite_eq_right_of_eq_false (eq_false hcl2),
                      dite_eq_right_of_eq_false (eq_false hcr2)]
      exact ⟨T1, hT1', evals_mono (evals_single s1) (by omega)⟩
  | succ r ih =>
      intro T hT
      have hj1 : j + 1 < c.length := by omega
      have hhd : T.head = .inp (.inr ((c)[j + 1]'hj1)) := by
        rw [hT.head]
        unfold shiftBoard
        have h1 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -2 := by omega
        have h2 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -1 := by omega
        have h3 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length) := by omega
        have h4 : ((x.length + 1 + j : ℕ) : ℤ) ≠ (x.length : ℤ) := by omega
        have h5 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            x.length + 1 ≤ ((x.length + 1 + j : ℕ) : ℤ).toNat ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length + 1 + j ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat - (x.length + 1) < c.length) := by omega
        have h6 : 0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
            x.length + 1 + j ≤ ((x.length + 1 + j : ℕ) : ℤ).toNat ∧
            ((x.length + 1 + j : ℕ) : ℤ).toNat - x.length < c.length := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_right_of_eq_false (eq_false h3),
          ite_eq_right_iff.mpr (fun h => absurd h h4),
          dite_eq_right_of_eq_false (eq_false h5),
          dite_eq_left_of_eq_true (eq_true h6)]
        congr 2
        have hidx : ((x.length + 1 + j : ℕ) : ℤ).toNat - x.length = j + 1 := by omega
        simp only [hidx]
      let b := (c)[j]'hj
      let b' := (c)[j + 1]'hj1
      let T1 := T.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))
      let T2 := T1.move .right
      have s1 : (FlatSM M acc hM hT1).step ⟨.shift b, T⟩ = some ⟨.shiftMove b', T1⟩ := by
        rw [step_eq M acc hM hT1, hhd]; rfl
      have s2 : (FlatSM M acc hM hT1).step ⟨.shiftMove b', T1⟩ = some ⟨.shift b', T2⟩ := rfl
      have hT2 : TapeAt ((x.length + 1 + (j + 1) : ℕ) : ℤ) T2
          (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c (j + 1)) := by
        have h' := (hT.write (.cell (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩))).move_right
        have hpos : ((x.length + 1 + j : ℕ) : ℤ) + 1 = ((x.length + 1 + (j + 1) : ℕ) : ℤ) := by omega
        rw [hpos] at h'
        refine h'.congr fun z => ?_
        by_cases hz : z = ((x.length + 1 + j : ℕ) : ℤ)
        · subst hz
          rw [Function.update_self]
          unfold shiftBoard
          have h1 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -2 := by omega
          have h2 : ((x.length + 1 + j : ℕ) : ℤ) ≠ -1 := by omega
          have h3 : ¬ (0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
              ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length) := by omega
          have h4 : ((x.length + 1 + j : ℕ) : ℤ) ≠ (x.length : ℤ) := by omega
          have h5 : 0 ≤ ((x.length + 1 + j : ℕ) : ℤ) ∧
              x.length + 1 ≤ ((x.length + 1 + j : ℕ) : ℤ).toNat ∧
              ((x.length + 1 + j : ℕ) : ℤ).toNat < x.length + 1 + (j + 1) ∧
              ((x.length + 1 + j : ℕ) : ℤ).toNat - (x.length + 1) < c.length := by omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
            ite_eq_right_iff.mpr (fun h => absurd h h2),
            dite_eq_right_of_eq_false (eq_false h3),
            ite_eq_right_iff.mpr (fun h => absurd h h4),
            dite_eq_left_of_eq_true (eq_true h5)]
          have hidx : ((x.length + 1 + j : ℕ) : ℤ).toNat - (x.length + 1) = j := by omega
          simp only [b, hidx]
        · rw [Function.update_of_ne hz]
          unfold shiftBoard
          by_cases h1 : z = -2
          · simp [h1]
          · by_cases h2 : z = -1
            · simp [h2]
            · simp only [h1, h2, ite_false]
              by_cases hx : 0 ≤ z ∧ z.toNat < x.length
              · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_left_of_eq_true (eq_true hx)]
              · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_right_of_eq_false (eq_false hx)]
                by_cases hsep : z = (x.length : ℤ)
                · simp [hsep]
                · simp only [hsep, ite_false]
                  by_cases hcl1 : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧ z.toNat < x.length + 1 + j ∧
                      z.toNat - (x.length + 1) < c.length
                  · have hcl2 : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧
                        z.toNat < x.length + 1 + (j + 1) ∧
                        z.toNat - (x.length + 1) < c.length := ⟨hcl1.1, hcl1.2.1, by omega, hcl1.2.2.2⟩
                    rw [dite_eq_left_of_eq_true (eq_true hcl1),
                      dite_eq_left_of_eq_true (eq_true hcl2)]
                  · have hcl2 : ¬ (0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧
                        z.toNat < x.length + 1 + (j + 1) ∧
                        z.toNat - (x.length + 1) < c.length) := by omega
                    rw [dite_eq_right_of_eq_false (eq_false hcl1),
                      dite_eq_right_of_eq_false (eq_false hcl2)]
                    by_cases hcr1 : 0 ≤ z ∧ x.length + 1 + j ≤ z.toNat ∧ z.toNat - x.length < c.length
                    · have hcr2 : 0 ≤ z ∧ x.length + 1 + (j + 1) ≤ z.toNat ∧
                          z.toNat - x.length < c.length := ⟨hcr1.1, by omega, hcr1.2.2⟩
                      rw [dite_eq_left_of_eq_true (eq_true hcr1),
                        dite_eq_left_of_eq_true (eq_true hcr2)]
                    · have hcr2 : ¬ (0 ≤ z ∧ x.length + 1 + (j + 1) ≤ z.toNat ∧
                          z.toNat - x.length < c.length) := by omega
                      rw [dite_eq_right_of_eq_false (eq_false hcr1),
                        dite_eq_right_of_eq_false (eq_false hcr2)]
      obtain ⟨T', hT', ev⟩ := ih (j + 1) hj1 (by omega) T2 hT2
      exact ⟨T', hT', evals_mono (evals_trans (evals_single s1)
        (evals_trans (evals_single s2) ev)) (by omega)⟩

theorem phase1_rew_loop (board : ℤ → FlatSym (max M.sig 4))
    (hwall : board (-2) = .wall)
    (hnowall : ∀ z : ℤ, -1 ≤ z → board z ≠ .wall) :
    ∀ (k : ℕ) (T : Tape (FlatSym (max M.sig 4))),
      TapeAt ((k : ℤ) - 1) T board →
      ∃ T' : Tape (FlatSym (max M.sig 4)),
        TapeAt (-1) T' board ∧
        Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.initRew, T⟩
          (some ⟨.sim ⟨M.start, hM.1⟩, T'⟩) (k + 2)) := by
  intro k
  induction k with
  | zero =>
      intro T hT
      have hne : T.head ≠ .wall := by
        rw [hT.head]; exact hnowall (-1) (by omega)
      have s1 : (FlatSM M acc hM hT1).step ⟨.initRew, T⟩ = some ⟨.initRew, T.move .left⟩ := by
        rw [step_eq M acc hM hT1]
        cases hhd : T.head with
        | wall => exact absurd hhd hne
        | blank => rfl
        | cell _ => rfl
        | inp _ => rfl
        | out _ => rfl
      have hT1' : TapeAt (-2) (T.move .left) board := by
        have hL := hT.move_left
        have hpos : ((0 : ℕ) : ℤ) - 1 - 1 = -2 := by omega
        rwa [hpos] at hL
      have hw : (T.move .left).head = .wall := by rw [hT1'.head, hwall]
      have s2 : (FlatSM M acc hM hT1).step ⟨.initRew, T.move .left⟩ =
          some ⟨.sim ⟨M.start, hM.1⟩, (T.move .left).move .right⟩ := by
        rw [step_eq M acc hM hT1, hw]; rfl
      refine ⟨(T.move .left).move .right, ?_,
        evals_mono (evals_trans (evals_single s1) (evals_single s2)) (by omega)⟩
      have hR := hT1'.move_right
      have hpos : (-2 : ℤ) + 1 = -1 := by omega
      rwa [hpos] at hR
  | succ k ih =>
      intro T hT
      have hne : T.head ≠ .wall := by
        rw [hT.head]; exact hnowall (((k + 1 : ℕ) : ℤ) - 1) (by omega)
      have s1 : (FlatSM M acc hM hT1).step ⟨.initRew, T⟩ = some ⟨.initRew, T.move .left⟩ := by
        rw [step_eq M acc hM hT1]
        cases hhd : T.head with
        | wall => exact absurd hhd hne
        | blank => rfl
        | cell _ => rfl
        | inp _ => rfl
        | out _ => rfl
      have hT1' : TapeAt ((k : ℤ) - 1) (T.move .left) board := by
        have hL := hT.move_left
        have hpos : ((k + 1 : ℕ) : ℤ) - 1 - 1 = (k : ℤ) - 1 := by omega
        rwa [hpos] at hL
      obtain ⟨T', hT', hev⟩ := ih (T.move .left) hT1'
      exact ⟨T', hT', evals_mono (evals_trans (evals_single s1) hev) (by omega)⟩

theorem pairTape_bounded (x c : List Bool) :
    ∀ v ∈ CookLevin.pairTape x c, v < max M.sig 4 := by
  intro v hv
  simp only [CookLevin.pairTape, CookLevin.symbolsOf, List.mem_cons, List.mem_append,
    List.mem_map, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | (((⟨b, _, rfl⟩ | rfl) | ⟨b, _, rfl⟩) | (rfl | rfl))
  · omega
  · cases b <;> simp
  · omega
  · cases b <;> simp
  · omega
  · omega

theorem pairTape_len (x c : List Bool) :
    (CookLevin.pairTape x c).length = x.length + c.length + 4 := by
  simp [CookLevin.pairTape, CookLevin.symbolsOf] <;> omega

theorem phase1_full (x c : List Bool) :
    ∃ T : Tape (FlatSym (max M.sig 4)),
      TapeAt (-1) T (flatBoard (max M.sig 4) (CookLevin.pairTape x c)) ∧
      Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step
        ((FlatSM M acc hM hT1).init (PvsNP.encodePair (x, c)))
        (some ⟨.sim ⟨M.start, hM.1⟩, T⟩) (3 * (x.length + c.length) + 18)) := by
  obtain ⟨T1, hT1a, ev1⟩ := phase1_preamble M acc hM hT1 x c
  obtain ⟨T2, hT2, ev2⟩ := phase1_convX_loop M acc hM hT1 x c 0 (Nat.zero_le _) T1 hT1a
  obtain ⟨Tm, hTm, evM⟩ :
      ∃ Tm : Tape (FlatSym (max M.sig 4)),
        TapeAt ((x.length + c.length : ℕ) : ℤ) Tm
          (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c c.length) ∧
        Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.convX, T2⟩
          (some ⟨.initEnd0, Tm⟩) (2 * c.length + 2)) := by
    by_cases hc : c.length = 0
    · have hhd2 : T2.head = .blank := by
        rw [hT2.head]; unfold convXBoard
        have h1 : (x.length : ℤ) ≠ -2 := by omega
        have h2 : (x.length : ℤ) ≠ -1 := by omega
        have h3 : ¬ (0 ≤ (x.length : ℤ) ∧ (x.length : ℤ).toNat < x.length) := by omega
        have h4 : ¬ (0 ≤ (x.length : ℤ) ∧ x.length ≤ (x.length : ℤ).toNat ∧
            (x.length : ℤ).toNat - x.length < c.length) := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_right_of_eq_false (eq_false h3),
          dite_eq_right_of_eq_false (eq_false h4)]
      let T3 := T2.write (.cell ⟨0, by omega⟩)
      have s3 : (FlatSM M acc hM hT1).step ⟨.convX, T2⟩ = some ⟨.initEnd0, T3⟩ := by
        rw [step_eq M acc hM hT1, hhd2]; rfl
      refine ⟨T3, ?_, evals_mono (evals_single s3) (by omega)⟩
      have h' := hT2.write (.cell ⟨0, by omega⟩)
      have hpos : (x.length : ℤ) = ((x.length + c.length : ℕ) : ℤ) := by omega
      rw [hpos] at h'
      refine h'.congr fun z => ?_
      by_cases hz : z = ((x.length + c.length : ℕ) : ℤ)
      · subst hz
        rw [Function.update_self]
        unfold shiftBoard
        have h1 : ((x.length + c.length : ℕ) : ℤ) ≠ -2 := by omega
        have h2 : ((x.length + c.length : ℕ) : ℤ) ≠ -1 := by omega
        have h3 : ¬ (0 ≤ ((x.length + c.length : ℕ) : ℤ) ∧
            ((x.length + c.length : ℕ) : ℤ).toNat < x.length) := by omega
        have h4 : ((x.length + c.length : ℕ) : ℤ) = (x.length : ℤ) := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_right_of_eq_false (eq_false h3),
          ite_eq_left_iff.mpr (fun h => absurd h4 h)]
      · rw [Function.update_of_ne hz]
        unfold convXBoard shiftBoard
        by_cases h1 : z = -2
        · simp [h1]
        · by_cases h2 : z = -1
          · simp [h2]
          · simp only [h1, h2, ite_false]
            by_cases hx : 0 ≤ z ∧ z.toNat < x.length
            · rw [dite_eq_left_of_eq_true (eq_true hx),
                ite_eq_left_iff.mpr (fun h => absurd hx.2 h),
                dite_eq_left_of_eq_true (eq_true hx)]
            · have hsep : z ≠ (x.length : ℤ) := by omega
              have hn1 : ¬ (0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length) := by omega
              have hn2 : ¬ (0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧ z.toNat < x.length + 1 + c.length ∧
                  z.toNat - (x.length + 1) < c.length) := by omega
              have hn3 : ¬ (0 ≤ z ∧ x.length + 1 + c.length ≤ z.toNat ∧
                  z.toNat - x.length < c.length) := by omega
              rw [dite_eq_right_of_eq_false (eq_false hx),
                dite_eq_right_of_eq_false (eq_false hn1),
                dite_eq_right_of_eq_false (eq_false hx),
                ite_eq_right_iff.mpr (fun h => absurd h hsep),
                dite_eq_right_of_eq_false (eq_false hn2),
                dite_eq_right_of_eq_false (eq_false hn3)]
    · have hcpos : 0 < c.length := by omega
      have hhd2 : T2.head = .inp (.inr ((c)[0]'hcpos)) := by
        rw [hT2.head]; unfold convXBoard
        have h1 : (x.length : ℤ) ≠ -2 := by omega
        have h2 : (x.length : ℤ) ≠ -1 := by omega
        have h3 : ¬ (0 ≤ (x.length : ℤ) ∧ (x.length : ℤ).toNat < x.length) := by omega
        have h4 : 0 ≤ (x.length : ℤ) ∧ x.length ≤ (x.length : ℤ).toNat ∧
            (x.length : ℤ).toNat - x.length < c.length := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_right_iff.mpr (fun h => absurd h h2),
          dite_eq_right_of_eq_false (eq_false h3),
          dite_eq_left_of_eq_true (eq_true h4)]
        congr 2
        have h0 : (x.length : ℤ).toNat - x.length = 0 := by omega
        simp [h0]
      let b0 := (c)[0]'hcpos
      let T3 := T2.write (.cell ⟨0, by omega⟩)
      let T4 := T3.move .right
      have s3 : (FlatSM M acc hM hT1).step ⟨.convX, T2⟩ = some ⟨.shiftMove b0, T3⟩ := by
        rw [step_eq M acc hM hT1, hhd2]; rfl
      have s4 : (FlatSM M acc hM hT1).step ⟨.shiftMove b0, T3⟩ = some ⟨.shift b0, T4⟩ := rfl
      have hT4 : TapeAt ((x.length + 1 + 0 : ℕ) : ℤ) T4
          (shiftBoard (max M.sig 4) (Nat.le_max_right _ _) x c 0) := by
        have h' := (hT2.write (.cell ⟨0, by omega⟩)).move_right
        have hpos : (x.length : ℤ) + 1 = ((x.length + 1 + 0 : ℕ) : ℤ) := by omega
        rw [hpos] at h'
        refine h'.congr fun z => ?_
        by_cases hz : z = (x.length : ℤ)
        · subst hz
          rw [Function.update_self]
          unfold shiftBoard
          have h1 : (x.length : ℤ) ≠ -2 := by omega
          have h2 : (x.length : ℤ) ≠ -1 := by omega
          have h3 : ¬ (0 ≤ (x.length : ℤ) ∧ (x.length : ℤ).toNat < x.length) := by omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
            ite_eq_right_iff.mpr (fun h => absurd h h2),
            dite_eq_right_of_eq_false (eq_false h3),
            ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        · rw [Function.update_of_ne hz]
          unfold convXBoard shiftBoard
          by_cases h1 : z = -2
          · simp [h1]
          · by_cases h2 : z = -1
            · simp [h2]
            · simp only [h1, h2, ite_false]
              by_cases hx : 0 ≤ z ∧ z.toNat < x.length
              · rw [dite_eq_left_of_eq_true (eq_true hx),
                  ite_eq_left_iff.mpr (fun h => absurd hx.2 h),
                  dite_eq_left_of_eq_true (eq_true hx)]
              · rw [dite_eq_right_of_eq_false (eq_false hx),
                  dite_eq_right_of_eq_false (eq_false hx),
                  ite_eq_right_iff.mpr (fun h => absurd h hz)]
                have hncl : ¬ (0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧ z.toNat < x.length + 1 + 0 ∧
                    z.toNat - (x.length + 1) < c.length) := by omega
                rw [dite_eq_right_of_eq_false (eq_false hncl)]
                by_cases hcr : 0 ≤ z ∧ x.length ≤ z.toNat ∧ z.toNat - x.length < c.length
                · have hcr2 : 0 ≤ z ∧ x.length + 1 + 0 ≤ z.toNat ∧ z.toNat - x.length < c.length :=
                    ⟨hcr.1, by omega, hcr.2.2⟩
                  rw [dite_eq_left_of_eq_true (eq_true hcr),
                    dite_eq_left_of_eq_true (eq_true hcr2)]
                · have hcr2 : ¬ (0 ≤ z ∧ x.length + 1 + 0 ≤ z.toNat ∧
                      z.toNat - x.length < c.length) := by omega
                  rw [dite_eq_right_of_eq_false (eq_false hcr),
                    dite_eq_right_of_eq_false (eq_false hcr2)]
      obtain ⟨Tm, hTm, evS⟩ := phase1_shift_loop M acc hM hT1 x c hcpos 0 hcpos T4 hT4
      exact ⟨Tm, hTm, evals_mono (evals_trans (evals_single s3)
        (evals_trans (evals_single s4) evS)) (by omega)⟩
  let Te1 := Tm.move .right
  let Te2 := Te1.write (.cell ⟨0, by omega⟩)
  let Te3 := Te2.move .right
  let Te4 := Te3.write (.cell ⟨3, by omega⟩)
  have se1 : (FlatSM M acc hM hT1).step ⟨.initEnd0, Tm⟩ = some ⟨.initEnd1, Te1⟩ := rfl
  have se2 : (FlatSM M acc hM hT1).step ⟨.initEnd1, Te1⟩ = some ⟨.initEnd2, Te2⟩ := rfl
  have se3 : (FlatSM M acc hM hT1).step ⟨.initEnd2, Te2⟩ = some ⟨.initEnd3, Te3⟩ := rfl
  have se4 : (FlatSM M acc hM hT1).step ⟨.initEnd3, Te3⟩ = some ⟨.initRew, Te4⟩ := rfl
  have hTe4a : TapeAt (((x.length + c.length : ℕ) : ℤ) + 1 + 1) Te4
      (flatBoard (max M.sig 4) (CookLevin.pairTape x c)) := by
    have h' := (((hTm.move_right).write (.cell ⟨0, by omega⟩)).move_right).write (.cell ⟨3, by omega⟩)
    refine h'.congr fun z => ?_
    have hlen := pairTape_len x c
    have hbd := pairTape_bounded M x c
    by_cases hz2 : z = ((x.length + c.length : ℕ) : ℤ) + 1 + 1
    · subst hz2
      rw [Function.update_self]
      have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd
        (x.length + c.length + 3) (by omega)
      have heq : ((x.length + c.length + 3 : ℕ) : ℤ) - 1 =
          ((x.length + c.length : ℕ) : ℤ) + 1 + 1 := by omega
      rw [heq] at hfb; rw [hfb]
      congr 1; apply Fin.ext
      simp only [CookLevin.pairTape, List.getElem_cons_succ]
      rw [List.getElem_append_right (by simp [CookLevin.symbolsOf] <;> omega)]
      have hidx : x.length + c.length + 2 -
          ((CookLevin.symbolsOf x ++ [0]) ++ CookLevin.symbolsOf c).length = 1 := by
        simp [CookLevin.symbolsOf] <;> omega
      simp only [hidx]; rfl
    · rw [Function.update_of_ne hz2]
      by_cases hz1 : z = ((x.length + c.length : ℕ) : ℤ) + 1
      · subst hz1
        rw [Function.update_self]
        have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd
          (x.length + c.length + 2) (by omega)
        have heq : ((x.length + c.length + 2 : ℕ) : ℤ) - 1 =
            ((x.length + c.length : ℕ) : ℤ) + 1 := by omega
        rw [heq] at hfb; rw [hfb]
        congr 1; apply Fin.ext
        simp only [CookLevin.pairTape, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp [CookLevin.symbolsOf] <;> omega)]
        have hidx : x.length + c.length + 1 -
            ((CookLevin.symbolsOf x ++ [0]) ++ CookLevin.symbolsOf c).length = 0 := by
          simp [CookLevin.symbolsOf] <;> omega
        simp only [hidx]; rfl
      · rw [Function.update_of_ne hz1]
        unfold shiftBoard
        by_cases hmw : z = -2
        · subst hmw; simp [flatBoard_wall]
        · by_cases hm1 : z = -1
          · subst hm1
            simp only [hmw, ite_false, ite_true]
            have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd 0 (by omega)
            have heq : ((0 : ℕ) : ℤ) - 1 = -1 := by omega
            rw [heq] at hfb; rw [hfb]; rfl
          · simp only [hmw, hm1, ite_false]
            by_cases hx : 0 ≤ z ∧ z.toNat < x.length
            · rw [dite_eq_left_of_eq_true (eq_true hx)]
              have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd
                (z.toNat + 1) (by omega)
              have heq : ((z.toNat + 1 : ℕ) : ℤ) - 1 = z := by omega
              rw [heq] at hfb; rw [hfb]
              congr 1; apply Fin.ext
              simp only [CookLevin.pairTape, List.getElem_cons_succ]
              rw [List.getElem_append_left (by simp [CookLevin.symbolsOf] <;> omega),
                List.getElem_append_left (by simp [CookLevin.symbolsOf] <;> omega),
                List.getElem_append_left (by simp only [CookLevin.symbolsOf, List.length_map]; exact hx.2)]
              simp only [CookLevin.symbolsOf, List.getElem_map]
              cases x[z.toNat]'hx.2 <;> rfl
            · rw [dite_eq_right_of_eq_false (eq_false hx)]
              by_cases hsep : z = (x.length : ℤ)
              · subst hsep
                rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
                have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd
                  (x.length + 1) (by omega)
                have heq : ((x.length + 1 : ℕ) : ℤ) - 1 = (x.length : ℤ) := by omega
                rw [heq] at hfb; rw [hfb]
                congr 1; apply Fin.ext
                simp only [CookLevin.pairTape, List.getElem_cons_succ]
                rw [List.getElem_append_left (by simp [CookLevin.symbolsOf]),
                  List.getElem_append_left (by simp [CookLevin.symbolsOf]),
                  List.getElem_append_right (by simp [CookLevin.symbolsOf])]
                have hidx : x.length - (CookLevin.symbolsOf x).length = 0 := by
                  simp [CookLevin.symbolsOf]
                simp only [hidx]; rfl
              · rw [ite_eq_right_iff.mpr (fun h => absurd h hsep)]
                by_cases hcl : 0 ≤ z ∧ x.length + 1 ≤ z.toNat ∧
                    z.toNat < x.length + 1 + c.length ∧
                    z.toNat - (x.length + 1) < c.length
                · rw [dite_eq_left_of_eq_true (eq_true hcl)]
                  have hfb := flatBoard_at (max M.sig 4) (CookLevin.pairTape x c) hbd
                    (z.toNat + 1) (by omega)
                  have heq : ((z.toNat + 1 : ℕ) : ℤ) - 1 = z := by omega
                  rw [heq] at hfb; rw [hfb]
                  congr 1; apply Fin.ext
                  simp only [CookLevin.pairTape, List.getElem_cons_succ]
                  rw [List.getElem_append_left (by simp [CookLevin.symbolsOf] <;> omega),
                    List.getElem_append_right (by simp [CookLevin.symbolsOf] <;> omega)]
                  have hidx : z.toNat - (CookLevin.symbolsOf x ++ [0]).length =
                      z.toNat - (x.length + 1) := by simp [CookLevin.symbolsOf]
                  simp only [hidx]
                  simp only [CookLevin.symbolsOf, List.getElem_map]
                  cases (c)[z.toNat - (x.length + 1)]'hcl.2.2.2 <;> rfl
                · have hcr : ¬ (0 ≤ z ∧ x.length + 1 + c.length ≤ z.toNat ∧
                      z.toNat - x.length < c.length) := by omega
                  rw [dite_eq_right_of_eq_false (eq_false hcl),
                    dite_eq_right_of_eq_false (eq_false hcr)]
                  by_cases hlt : z < -2
                  · exact (flatBoard_lt _ _ z hlt).symm
                  · exact (flatBoard_ge _ _ z (by omega)).symm
  have hTe4 : TapeAt (((x.length + c.length + 3 : ℕ) : ℤ) - 1) Te4
      (flatBoard (max M.sig 4) (CookLevin.pairTape x c)) := by
    have hpos : ((x.length + c.length : ℕ) : ℤ) + 1 + 1 =
        ((x.length + c.length + 3 : ℕ) : ℤ) - 1 := by omega
    rwa [hpos] at hTe4a
  have hnowall : ∀ z : ℤ, -1 ≤ z → flatBoard (max M.sig 4) (CookLevin.pairTape x c) z ≠ .wall := by
    intro z hz; unfold flatBoard; split_ifs <;> first | omega | simp
  obtain ⟨Tf, hTf, evR⟩ := phase1_rew_loop M acc hM hT1 _ (flatBoard_wall _ _) hnowall
    (x.length + c.length + 3) Te4 hTe4
  exact ⟨Tf, hTf, evals_mono (evals_trans ev1 (evals_trans ev2 (evals_trans evM
    (evals_trans (evals_single se1) (evals_trans (evals_single se2)
      (evals_trans (evals_single se3) (evals_trans (evals_single se4) evR))))))) (by omega)⟩

/-! ### Phase 2: step-by-step `FlatTM` simulation -/

theorem doMove_run (q' : Fin M.states) (d : TMMove) (h : ℕ) (right : List ℕ)
    (T : Tape (FlatSym (max M.sig 4)))
    (hT : TapeAt ((h : ℤ) - 1) T (flatBoard (max M.sig 4) right)) :
    ∃ T' : Tape (FlatSym (max M.sig 4)),
      TapeAt (((moveTapeHead ([], h, right) d).2.1 : ℤ) - 1) T' (flatBoard (max M.sig 4) right) ∧
      Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.doMove q' d, T⟩ (some ⟨.sim q', T'⟩) 2) := by
  cases d with
  | Nmove =>
      have s1 : (FlatSM M acc hM hT1).step ⟨.doMove q' .Nmove, T⟩ = some ⟨.sim q', T⟩ := by
        rw [step_eq M acc hM hT1]; dsimp [mkDelta]; rw [tape_write_head]
      exact ⟨T, hT, evals_mono (evals_single s1) (by omega)⟩
  | Rmove =>
      have s1 : (FlatSM M acc hM hT1).step ⟨.doMove q' .Rmove, T⟩ = some ⟨.sim q', T.move .right⟩ := by
        rw [step_eq M acc hM hT1]; rfl
      refine ⟨T.move .right, ?_, evals_mono (evals_single s1) (by omega)⟩
      have hR := hT.move_right
      have hpos : (h : ℤ) - 1 + 1 = ((h + 1 : ℕ) : ℤ) - 1 := by omega
      rwa [hpos] at hR
  | Lmove =>
      have s1 : (FlatSM M acc hM hT1).step ⟨.doMove q' .Lmove, T⟩ = some ⟨.chkWall q', T.move .left⟩ := by
        rw [step_eq M acc hM hT1]; rfl
      have hL : TapeAt ((h : ℤ) - 2) (T.move .left) (flatBoard (max M.sig 4) right) := by
        have hLm := hT.move_left
        have hpos : (h : ℤ) - 1 - 1 = (h : ℤ) - 2 := by omega
        rwa [hpos] at hLm
      cases h with
      | zero =>
          have hw : (T.move .left).head = .wall := by
            rw [hL.head]; exact flatBoard_wall _ _
          have s2 : (FlatSM M acc hM hT1).step ⟨.chkWall q', T.move .left⟩ =
              some ⟨.sim q', T⟩ := by
            rw [step_eq M acc hM hT1, hw]; dsimp [mkDelta]; rw [tape_move_lr]
          exact ⟨T, hT, evals_trans (evals_single s1) (evals_single s2)⟩
      | succ h' =>
          have hnw : (T.move .left).head ≠ .wall := by
            rw [hL.head]
            unfold flatBoard
            split_ifs <;> first | omega | simp
          have s2 : (FlatSM M acc hM hT1).step ⟨.chkWall q', T.move .left⟩ =
              some ⟨.sim q', T.move .left⟩ := by
            rw [step_eq M acc hM hT1]
            cases hhd : (T.move .left).head with
            | wall => exact absurd hhd hnw
            | blank => dsimp [mkDelta]; rw [← hhd, tape_write_head]
            | cell _ => dsimp [mkDelta]; rw [← hhd, tape_write_head]
            | inp _ => dsimp [mkDelta]; rw [← hhd, tape_write_head]
            | out _ => dsimp [mkDelta]; rw [← hhd, tape_write_head]
          refine ⟨T.move .left, ?_, evals_trans (evals_single s1) (evals_single s2)⟩
          have hpos : ((h' + 1 : ℕ) : ℤ) - 2 = (h' : ℤ) - 1 := by omega
          rw [hpos] at hL
          exact hL

theorem phase2_step (q : Fin M.states) (h : ℕ) (right : List ℕ)
    (hr : ∀ v ∈ right, v < max M.sig 4)
    (hnh : haltingStateReached M ⟨q.val, [([], h, right)]⟩ = false)
    (cfg' : FlatTMConfig)
    (hstep : stepFlatTM M ⟨q.val, [([], h, right)]⟩ = some cfg')
    (T : Tape (FlatSym (max M.sig 4)))
    (hT : TapeAt ((h : ℤ) - 1) T (flatBoard (max M.sig 4) right)) :
    ∃ (q' : Fin M.states) (h' : ℕ) (right' : List ℕ) (T' : Tape (FlatSym (max M.sig 4))),
      cfg' = ⟨q'.val, [([], h', right')]⟩ ∧
      (∀ v ∈ right', v < max M.sig 4) ∧
      TapeAt ((h' : ℤ) - 1) T' (flatBoard (max M.sig 4) right') ∧
      Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ (some ⟨.sim q', T'⟩) 5) := by
  have hread : readSym T.1 = currentTapeSymbol ([], h, right) := by
    rw [hT.head]; exact flatBoard_readSym (max M.sig 4) right hr h
  have hmatch_eq : ∀ e : FlatTMTransEntry,
      (e.src_state == q.val && decide (e.src_tape_vals = [readSym T.1])) =
      entryMatchesConfig e ⟨q.val, [([], h, right)]⟩ := by
    intro e
    simp [entryMatchesConfig, hread]
  have hfind_eq : lookupEntry M q.val (readSym T.1) =
      M.trans.find? (fun e => entryMatchesConfig e ⟨q.val, [([], h, right)]⟩) := by
    unfold lookupEntry
    congr 1; funext e; exact hmatch_eq e
  simp only [stepFlatTM, Option.bind_eq_bind] at hstep
  cases hFind : M.trans.find? (fun e => entryMatchesConfig e ⟨q.val, [([], h, right)]⟩) with
  | none => rw [hFind] at hstep; simp at hstep
  | some e =>
      rw [hFind] at hstep
      have hFind' : lookupEntry M q.val (readSym T.1) = some e := hfind_eq.trans hFind
      have hmem : e ∈ M.trans := List.mem_of_find?_eq_some hFind
      have hval := hM.2.2 e hmem
      have hdst : e.dst_state < M.states := hval.2.1
      have hwlen : e.dst_write_vals.length = 1 := hval.2.2.2.1.trans hT1
      have hmlen : e.move_dirs.length = 1 := hval.2.2.2.2.1.trans hT1
      obtain ⟨wv, hw_eq⟩ : ∃ wv, e.dst_write_vals = [wv] := by
        cases h1 : e.dst_write_vals with
        | nil => simp [h1] at hwlen
        | cons a l =>
            cases l with
            | nil => exact ⟨a, rfl⟩
            | cons _ _ => simp [h1] at hwlen
      obtain ⟨mv, hm_eq⟩ : ∃ mv, e.move_dirs = [mv] := by
        cases h1 : e.move_dirs with
        | nil => simp [h1] at hmlen
        | cons a l =>
            cases l with
            | nil => exact ⟨a, rfl⟩
            | cons _ _ => simp [h1] at hmlen
      have hcfg' : cfg' = ⟨e.dst_state, [tapeStep ([], h, right) wv mv]⟩ := by
        simp [applyTransitionEntry, hw_eq, hm_eq] at hstep
        exact hstep.symm
      have hhlt_false : M.halt.getD q.val false = false := hnh
      let q' : Fin M.states := ⟨e.dst_state, hdst⟩
      cases wv with
      | none =>
          have s1 : (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ = some ⟨.doMove q' mv, T⟩ := by
            rw [step_eq M acc hM hT1,
              mkDelta_sim_none M acc hM hT1 q T.head hhlt_false e hFind' mv hw_eq hm_eq hdst]
            dsimp only
            rw [tape_write_head]
          obtain ⟨T', hT', evM⟩ := doMove_run M acc hM hT1 q' mv h right T hT
          refine ⟨q', (moveTapeHead ([], h, right) mv).2.1, right, T', ?_, hr, hT',
            evals_mono (evals_trans (evals_single s1) evM) (by omega)⟩
          rw [hcfg']; cases mv <;> rfl
      | some v =>
          have hv : v < max M.sig 4 :=
            Nat.lt_of_lt_of_le (hval.2.2.2.2.2.2 (some v) (by rw [hw_eq]; simp)) (Nat.le_max_left _ _)
          by_cases hlt : h < right.length
          · have hhd : T.head = .cell ⟨right[h], hr _ (List.getElem_mem hlt)⟩ := by
              rw [hT.head]; exact flatBoard_at _ right hr h hlt
            have s1 : (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ =
                some ⟨.doMove q' mv, T.write (.cell ⟨v, hv⟩)⟩ := by
              rw [step_eq M acc hM hT1, hhd]
              rw [mkDelta_sim_some_cell M acc hM hT1 q _ hhlt_false e
                (by rwa [hhd] at hFind') v hv mv hw_eq hm_eq hdst]
            set right' := right.take h ++ v :: right.drop (h + 1)
            have hr' : ∀ u ∈ right', u < max M.sig 4 := by
              intro u hu
              simp only [right', List.mem_append, List.mem_cons] at hu
              rcases hu with h1 | rfl | h2
              · exact hr u (List.mem_of_mem_take h1)
              · exact hv
              · exact hr u (List.mem_of_mem_drop h2)
            have hT1' : TapeAt ((h : ℤ) - 1) (T.write (.cell ⟨v, hv⟩))
                (flatBoard (max M.sig 4) right') :=
              (hT.write (.cell ⟨v, hv⟩)).congr (flatBoard_update_inRange _ right hr h hlt ⟨v, hv⟩)
            obtain ⟨T', hT', evM⟩ :=
              doMove_run M acc hM hT1 q' mv h right' (T.write (.cell ⟨v, hv⟩)) hT1'
            refine ⟨q', (moveTapeHead ([], h, right') mv).2.1, right', T', ?_, hr', hT',
              evals_mono (evals_trans (evals_single s1) evM) (by omega)⟩
            rw [hcfg']
            simp only [tapeStep, writeCurrentTapeSymbol, right']
            split_ifs <;> first | omega | (cases mv <;> rfl)
          · have hhd : T.head = .blank := by
              rw [hT.head]; exact flatBoard_ge _ right ((h : ℤ) - 1) (by omega)
            have s1 : (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ =
                some ⟨.chkFront q' ⟨v, hv⟩ mv, T.move .left⟩ := by
              rw [step_eq M acc hM hT1, hhd]
              rw [mkDelta_sim_some_blank M acc hM hT1 q hhlt_false e
                (by rwa [hhd] at hFind') v hv mv hw_eq hm_eq hdst]
            have hL : TapeAt ((h : ℤ) - 2) (T.move .left) (flatBoard (max M.sig 4) right) := by
              have hLm := hT.move_left
              have hpos : (h : ℤ) - 1 - 1 = (h : ℤ) - 2 := by omega
              rwa [hpos] at hLm
            by_cases heq : h = right.length
            · have hnb : (T.move .left).head ≠ .blank := by
                rw [hL.head]
                cases hrl : right.length with
                | zero =>
                    have hpos : (h : ℤ) - 2 = -2 := by omega
                    rw [hpos, flatBoard_wall]; simp
                | succ l =>
                    have hpos : (h : ℤ) - 2 = (l : ℤ) - 1 := by omega
                    rw [hpos, flatBoard_at _ right hr l (by omega)]; simp
              have s2 : (FlatSM M acc hM hT1).step ⟨.chkFront q' ⟨v, hv⟩ mv, T.move .left⟩ =
                  some ⟨.doWrite q' ⟨v, hv⟩ mv, T⟩ := by
                rw [step_eq M acc hM hT1]
                cases hhdL : (T.move .left).head with
                | blank => exact absurd hhdL hnb
                | wall => dsimp [mkDelta]; rw [tape_move_lr]
                | cell _ => dsimp [mkDelta]; rw [tape_move_lr]
                | inp _ => dsimp [mkDelta]; rw [tape_move_lr]
                | out _ => dsimp [mkDelta]; rw [tape_move_lr]
              have s3 : (FlatSM M acc hM hT1).step ⟨.doWrite q' ⟨v, hv⟩ mv, T⟩ =
                  some ⟨.doMove q' mv, T.write (.cell ⟨v, hv⟩)⟩ := by
                rw [step_eq M acc hM hT1]; rfl
              set right' := right ++ [v]
              have hr' : ∀ u ∈ right', u < max M.sig 4 := by
                intro u hu
                rcases List.mem_append.mp hu with h1 | h2
                · exact hr u h1
                · simp only [List.mem_singleton] at h2; subst h2; exact hv
              have hT1' : TapeAt ((h : ℤ) - 1) (T.write (.cell ⟨v, hv⟩))
                  (flatBoard (max M.sig 4) right') := by
                rw [heq] at hT ⊢
                exact (hT.write (.cell ⟨v, hv⟩)).congr (flatBoard_update_append _ right hr ⟨v, hv⟩)
              obtain ⟨T', hT', evM⟩ :=
                doMove_run M acc hM hT1 q' mv h right' (T.write (.cell ⟨v, hv⟩)) hT1'
              refine ⟨q', (moveTapeHead ([], h, right') mv).2.1, right', T', ?_, hr', hT',
                evals_mono (evals_trans (evals_single s1) (evals_trans (evals_single s2)
                  (evals_trans (evals_single s3) evM))) (by omega)⟩
              rw [hcfg']
              simp only [tapeStep, writeCurrentTapeSymbol, right']
              split_ifs <;> first | omega | (cases mv <;> rfl)
            · have hbL : (T.move .left).head = .blank := by
                rw [hL.head]; exact flatBoard_ge _ right ((h : ℤ) - 2) (by omega)
              have s2 : (FlatSM M acc hM hT1).step ⟨.chkFront q' ⟨v, hv⟩ mv, T.move .left⟩ =
                  some ⟨.doMove q' mv, T⟩ := by
                rw [step_eq M acc hM hT1, hbL]; dsimp [mkDelta]; rw [tape_move_lr]
              obtain ⟨T', hT', evM⟩ := doMove_run M acc hM hT1 q' mv h right T hT
              refine ⟨q', (moveTapeHead ([], h, right) mv).2.1, right, T', ?_, hr, hT',
                evals_mono (evals_trans (evals_single s1) (evals_trans (evals_single s2) evM)) (by omega)⟩
              rw [hcfg']
              simp only [tapeStep, writeCurrentTapeSymbol]
              split_ifs <;> first | omega | (cases mv <;> rfl)

theorem phase2_run :
    ∀ (n : ℕ) (q : Fin M.states) (h : ℕ) (right : List ℕ)
      (_hr : ∀ v ∈ right, v < max M.sig 4)
      (cfg : FlatTMConfig),
      runFlatTM n M ⟨q.val, [([], h, right)]⟩ = some cfg →
      haltingStateReached M cfg = true →
      ∀ (T : Tape (FlatSym (max M.sig 4))),
        TapeAt ((h : ℤ) - 1) T (flatBoard (max M.sig 4) right) →
        ∃ (qf : Fin M.states) (hf : ℕ) (rightf : List ℕ) (Tf : Tape (FlatSym (max M.sig 4))),
          cfg = ⟨qf.val, [([], hf, rightf)]⟩ ∧
          TapeAt ((hf : ℤ) - 1) Tf (flatBoard (max M.sig 4) rightf) ∧
          Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step ⟨.sim q, T⟩
            (some ⟨.writeAns (qf.val == acc), Tf⟩) (5 * n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro q h right _hr cfg hrun hhalt T hT
      have hceq : ⟨q.val, [([], h, right)]⟩ = cfg := Option.some.inj hrun
      subst hceq
      have s1 : (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ =
          some ⟨.writeAns (q.val == acc), T⟩ := by
        rw [step_eq M acc hM hT1]; dsimp only [mkDelta]
        rw [show M.halt.getD q.val false = true from hhalt]
        simp only [ite_true]; rw [tape_write_head]
      exact ⟨q, h, right, T, rfl, hT, evals_single s1⟩
  | succ n ih =>
      intro q h right hr cfg hrun hhalt T hT
      by_cases hnow : haltingStateReached M ⟨q.val, [([], h, right)]⟩ = true
      · rw [runFlatTM_of_halting M _ (n + 1) hnow] at hrun
        have hceq : ⟨q.val, [([], h, right)]⟩ = cfg := Option.some.inj hrun
        subst hceq
        have s1 : (FlatSM M acc hM hT1).step ⟨.sim q, T⟩ =
            some ⟨.writeAns (q.val == acc), T⟩ := by
          rw [step_eq M acc hM hT1]; dsimp only [mkDelta]
          rw [show M.halt.getD q.val false = true from hnow]
          simp only [ite_true]; rw [tape_write_head]
        exact ⟨q, h, right, T, rfl, hT, evals_mono (evals_single s1) (by omega)⟩
      · have hnh : haltingStateReached M ⟨q.val, [([], h, right)]⟩ = false := by
          cases h1 : haltingStateReached M ⟨q.val, [([], h, right)]⟩ <;> simp_all
        simp only [runFlatTM, hnh, Bool.false_eq_true, ite_false] at hrun
        cases hst : stepFlatTM M ⟨q.val, [([], h, right)]⟩ with
        | none =>
            rw [hst] at hrun
            have hceq : ⟨q.val, [([], h, right)]⟩ = cfg := Option.some.inj hrun
            subst hceq
            exact absurd hhalt (by rw [hnh]; decide)
        | some cfg1 =>
            rw [hst] at hrun
            obtain ⟨q1, h1, right1, T1, rfl, hr1, hT1a, ev1⟩ :=
              phase2_step M acc hM hT1 q h right hr hnh cfg1 hst T hT
            obtain ⟨qf, hf, rightf, Tf, hcfgf, hTf, ev2⟩ :=
              ih q1 h1 right1 hr1 cfg hrun hhalt T1 hT1a
            exact ⟨qf, hf, rightf, Tf, hcfgf, hTf, evals_mono (evals_trans ev1 ev2) (by omega)⟩

/-! ### Phase 3: writing 1-bit answer `[b]` and halting in 4 steps -/

theorem phase3_ans (b : Bool) (pos : ℤ) (board : ℤ → FlatSym (max M.sig 4))
    (T : Tape (FlatSym (max M.sig 4))) (hT : TapeAt pos T board) :
    ∃ T' : Tape (FlatSym (max M.sig 4)),
      (FlatSM M acc hM hT1).step ⟨.outHalt, T'⟩ = none ∧
      (FlatSM M acc hM hT1).Shows ⟨.outHalt, T'⟩ [b] ∧
      Nonempty (EvalsToInTime (FlatSM M acc hM hT1).step
        ⟨.writeAns b, T⟩ (some ⟨.outHalt, T'⟩) 4) := by
  let T1 := T.write (.out b)
  let T2 := T1.move .right
  let T3 := T2.write .blank
  let T4 := T3.move .left
  have s1 : (FlatSM M acc hM hT1).step ⟨.writeAns b, T⟩ = some ⟨.ansMoveR, T1⟩ := rfl
  have s2 : (FlatSM M acc hM hT1).step ⟨.ansMoveR, T1⟩ = some ⟨.ansClear, T2⟩ := rfl
  have s3 : (FlatSM M acc hM hT1).step ⟨.ansClear, T2⟩ = some ⟨.ansBack, T3⟩ := rfl
  have s4 : (FlatSM M acc hM hT1).step ⟨.ansBack, T3⟩ = some ⟨.outHalt, T4⟩ := rfl
  have hT4 : TapeAt pos T4 (Function.update (Function.update board pos (.out b)) (pos + 1) .blank) := by
    have h' := (((hT.write (.out b)).move_right).write .blank).move_left
    have hp : pos + 1 - 1 = pos := by omega
    rwa [hp] at h'
  refine ⟨T4, rfl, ?_,
    evals_mono (evals_trans (evals_single s1) (evals_trans (evals_single s2)
      (evals_trans (evals_single s3) (evals_single s4)))) (by omega)⟩
  constructor
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    change T4.right₀.nth 0 = .out b
    rw [Tape.right₀_nth, hT4]
    have hne : pos + (0 : ℕ) ≠ pos + 1 := by omega
    rw [Function.update_of_ne hne]
    simp
  · intro b'
    change T4.right₀.nth 1 ≠ .out b'
    rw [Tape.right₀_nth, hT4]
    have heq : pos + ((1 : ℕ) : ℤ) = pos + 1 := by omega
    rw [heq, Function.update_self]
    simp

end sim

/-! ### Polynomial bound from `inOPoly` -/

theorem poly_of_inOPoly (t : ℕ → ℕ) (ht : inOPoly t) :
    ∃ p : Polynomial ℕ, ∀ n : ℕ, 5 * t n + 3 * n + 25 ≤ p.eval n := by
  obtain ⟨d, c, n0, hbound⟩ := ht
  let C0 := maxPrefix t n0
  refine ⟨Polynomial.C 5 * (Polynomial.C C0 + Polynomial.C c * Polynomial.X ^ d) +
      Polynomial.C 3 * Polynomial.X + Polynomial.C 25, fun n => ?_⟩
  have htn : t n ≤ C0 + c * n ^ d := by
    by_cases hn : n0 ≤ n
    · exact le_trans (hbound n hn) (Nat.le_add_left _ _)
    · exact le_trans (le_maxPrefix t (Nat.le_of_lt (Nat.lt_of_not_ge hn))) (Nat.le_add_right _ _)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  omega

end PvsNP.Units.m1_flat_np_to_st_np

/-- Bridge: a language in Cook-Levin NP is in single-tape NP. -/
theorem PvsNP.Units.m1_flat_np_to_st_np :
    ∀ L : Language Bool, CookLevin.inNP (fun x => x ∈ L) → L ∈ PvsNP.SingleTape.NP := by
  intro L hNP
  classical
  obtain ⟨R, a, k, b, t, M, acc, rej, ht, hM, hT1, hL, hdec⟩ := hNP
  let V : List Bool × List Bool → Bool := fun p => decide (R p.1 p.2)
  let pCert : Polynomial ℕ := Polynomial.C a * Polynomial.X ^ k + Polynomial.C b
  refine ⟨V, pCert, ?_, ?_⟩
  · obtain ⟨pTime, hpTime⟩ := PvsNP.Units.m1_flat_np_to_st_np.poly_of_inOPoly t ht
    refine ⟨PvsNP.Units.m1_flat_np_to_st_np.mkMachine M acc hM hT1, pTime, fun xc => ?_⟩
    rcases xc with ⟨x, c⟩
    obtain ⟨cfg, hrun, hhalt, hacc, _hrej⟩ := hdec x c
    obtain ⟨T1, hT1a, ev1⟩ := PvsNP.Units.m1_flat_np_to_st_np.phase1_full M acc hM hT1 x c
    have hbd := PvsNP.Units.m1_flat_np_to_st_np.pairTape_bounded M x c
    have hrun' : runFlatTM (t (x.length + c.length)) M
        ⟨M.start, [([], 0, CookLevin.pairTape x c)]⟩ = some cfg := hrun
    obtain ⟨qf, hf, rightf, Tf, hcfg, hTf, ev2⟩ :=
      PvsNP.Units.m1_flat_np_to_st_np.phase2_run M acc hM hT1 (t (x.length + c.length))
        ⟨M.start, hM.1⟩ 0 (CookLevin.pairTape x c) hbd cfg hrun' hhalt T1 hT1a
    obtain ⟨Tfinal, hstep0, hshows, ev3⟩ :=
      PvsNP.Units.m1_flat_np_to_st_np.phase3_ans M acc hM hT1 (qf.val == acc) ((hf : ℤ) - 1)
        (PvsNP.Units.m1_flat_np_to_st_np.flatBoard (max M.sig 4) rightf) Tf hTf
    have hans : (qf.val == acc) = V (x, c) := by
      have hiff : R x c ↔ qf.val = acc := by
        simpa [hcfg] using hacc
      cases hV : V (x, c) with
      | true =>
          have hR : R x c := of_decide_eq_true hV
          exact beq_iff_eq.mpr (hiff.mp hR)
      | false =>
          have hnR : ¬ R x c := of_decide_eq_false hV
          exact beq_false_of_ne (fun heq => hnR (hiff.mpr heq))
    have henc : PvsNP.encodeAnswer (V (x, c)) = [V (x, c)] := rfl
    rw [henc, ← hans]
    have hlen_pair : (PvsNP.encodePair (x, c)).length = x.length + c.length := by
      simp [PvsNP.Units.m1_flat_np_to_st_np.encodePair_eq]
    refine ⟨⟨.outHalt, Tfinal⟩, ?_, hstep0, hshows⟩
    exact PvsNP.Units.m1_flat_np_to_st_np.evals_mono
      (PvsNP.Units.m1_flat_np_to_st_np.evals_trans ev1
        (PvsNP.Units.m1_flat_np_to_st_np.evals_trans ev2 ev3))
      (by
        rw [hlen_pair]
        have hpn := hpTime (x.length + c.length)
        omega)
  · intro x
    have hLx : x ∈ L ↔ ∃ c, c.length ≤ a * x.length ^ k + b ∧ R x c := hL x
    rw [hLx]
    constructor
    · rintro ⟨c, hc, hR⟩
      refine ⟨c, ?_, decide_eq_true hR⟩
      simpa [pCert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] using hc
    · rintro ⟨c, hc, hV⟩
      refine ⟨c, ?_, of_decide_eq_true hV⟩
      simpa [pCert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] using hc
