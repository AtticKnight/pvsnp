import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/MetaComplexity/Helpers/Machines/Codec.lean (cpt_fstRun2, cpt_fstRun, cpt_fstRun_comp),
  lean/PEqualNP/MetaComplexity/Helpers/Machines/Glue.lean (cpt_congr, cpt_dec_of_bit, packRaw, δun, unpack,
    unpack_packRaw, unpack_pack, cpt_pack, cpt_unpack, pair_prod),
  lean/PEqualNP/MetaComplexity/Helpers/Machines/Lookup.lean (all of it) and
  lean/PEqualNP/Library/L098.lean (the statement).
MODIFIED from those files: the parts used are joined here inside the namespace PvsNP.Units.m2_bit_lookup_polytime, on top
of the settled campaign unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), in
whose namespace the upstream Defs and Library machines live (every upstream name PEqualNP.Library.X used here is
PvsNP.Units.fr_ladner.PEqualNP.Library.X); upstream's `encodePair` is written with that full name. The closing
theorems carry upstream L098 over to the campaign's definitions in PvsNP.Defs (PvsNP.encodePair and
PvsNP.encodeAnswer are definitionally the upstream encodings).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_bit_lookup_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-! ## From upstream Codec: transducer runs are polynomial-time computable -/

theorem cpt_fstRun2 {A B Q : Type} [Fintype A] [Fintype Q]
    (δ : Q → A → Q × Option B × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l) (fstRun2 δ fin q₀) :=
  fst2_polyTime _ _ _ δ fin q₀ (fun _ => rfl)

theorem cpt_fstRun {A B Q : Type} [Fintype A] [Fintype Q]
    (δ : Q → A → Q × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l) (fstRun δ fin q₀) :=
  fst_polyTime _ _ _ δ fin q₀ (fun _ => rfl)

theorem cpt_fstRun_comp {α αΓ A B Q : Type} [Fintype A] [Fintype Q] {ea : α → List αΓ}
    {f : α → List A} (hf : ComputableInPolyTime ea (fun l : List A => l) f)
    (δ : Q → A → Q × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime ea (fun l : List B => l) (fun a => fstRun δ fin q₀ (f a)) :=
  cpt_comp hf (cpt_fstRun δ fin q₀)

/-! ## From upstream Glue -/

theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f g : α → β}
    (hf : ComputableInPolyTime ea eb f) (e : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  have h : f = g := funext e
  rw [← h]; exact hf

theorem cpt_dec_of_bit {α αΓ : Type} {ea : α → List αΓ} {a : α → Bool}
    (h : ComputableInPolyTime ea (fun x : List Bool => x) (fun p => [a p])) :
    ComputableInPolyTime ea Computability.encodeBool a := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun q⟩⟩

/-- Two bits per symbol: the side, then the bit. -/
def packRaw (l : List (Bool ⊕ Bool)) : List Bool :=
  fstRun2
    (fun (_ : Unit) (s : Bool ⊕ Bool) => ((), some (Sum.isRight s), some (Sum.elim id id s)))
    (fun _ => none) () l

/-- The reader of one side `t`. -/
def δun (t : Bool) : Option Bool → Bool → Option Bool × Option Bool
  | none, a => (some a, none)
  | some a, b => (none, if a = t then some b else none)

/-- The two strings of a packed raw list. -/
def unpack (l : List Bool) : List Bool × List Bool :=
  (fstRun (δun false) (fun _ => none) none l, fstRun (δun true) (fun _ => none) none l)

theorem unpack_packRaw (l : List (Bool ⊕ Bool)) : unpack (packRaw l) = nfDec l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | inl b =>
      have h1 : unpack (packRaw (Sum.inl b :: l)) =
          (b :: (unpack (packRaw l)).1, (unpack (packRaw l)).2) := rfl
      have h2 : nfDec (Sum.inl b :: l) = (b :: (nfDec l).1, (nfDec l).2) := rfl
      rw [h1, h2, ih]
    | inr b =>
      have h1 : unpack (packRaw (Sum.inr b :: l)) =
          ((unpack (packRaw l)).1, b :: (unpack (packRaw l)).2) := rfl
      have h2 : nfDec (Sum.inr b :: l) = ((nfDec l).1, b :: (nfDec l).2) := rfl
      rw [h1, h2, ih]

theorem unpack_pack (p : List Bool × List Bool) :
    unpack (packRaw (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p)) = p := by
  rw [unpack_packRaw, nfDec_encodePair]

theorem cpt_pack :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => packRaw (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p)) :=
  fst2_polyTime _ _ _
    (fun (_ : Unit) (s : Bool ⊕ Bool) => ((), some (Sum.isRight s), some (Sum.elim id id s)))
    (fun _ => none) () (fun _ => rfl)

theorem cpt_unpack :
    ComputableInPolyTime (fun x : List Bool => x) PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      unpack :=
  cpt_pair (cpt_fstRun (δun false) (fun _ => none) none)
    (cpt_fstRun (δun true) (fun _ => none) none)

theorem pair_prod {f g : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) g) :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (f p, g p)) :=
  cpt_congr
    (cpt_comp cpt_pack (cpt_pair (cpt_comp cpt_unpack hf) (cpt_comp cpt_unpack hg)))
    (fun p => by simp only [unpack_pack])

/-! ## From upstream Lookup: the pure fact -/

/-- The value of an index written in binary, least significant bit first. -/
def idxVal (i : List Bool) : ℕ :=
  List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i

/-- The entries of a string at the even positions (`half false`) or at the odd positions
(`half true`). -/
def half : Bool → List Bool → List Bool
  | _, [] => []
  | false, c :: l => c :: half true l
  | true, _ :: l => half false l

theorem getD_half (l : List Bool) : ∀ (b : Bool) (a : ℕ),
    l.getD (2 * a + (if b = true then 1 else 0)) false = (half b l).getD a false := by
  induction l with
  | nil => intro b a; cases b <;> simp [half]
  | cons c l ih =>
    intro b a
    cases b with
    | true =>
      have e : 2 * a + (if true = true then 1 else 0) = 2 * a + 1 := by simp
      have h : half true (c :: l) = half false l := rfl
      rw [e, h, List.getD_cons_succ]
      simpa using ih false a
    | false =>
      have h : half false (c :: l) = c :: half true l := rfl
      rw [h]
      cases a with
      | zero => rfl
      | succ a =>
        have e : 2 * (a + 1) + (if false = true then 1 else 0) = (2 * a + 1) + 1 := by
          simp; omega
        rw [e, List.getD_cons_succ, List.getD_cons_succ]
        simpa using ih true a

/-- One round on pairs (remaining index, current string). -/
def stepP : List Bool × List Bool → List Bool × List Bool
  | ([], l) => ([], l)
  | (b :: i, l) => (i, half b l)

theorem stepP_iter (i : List Bool) : ∀ l : List Bool, ∃ l' : List Bool,
    stepP^[i.length] (i, l) = ([], l') ∧ l'.getD 0 false = l.getD (idxVal i) false := by
  induction i with
  | nil => intro l; exact ⟨l, rfl, rfl⟩
  | cons b i ih =>
    intro l
    obtain ⟨l', h1, h2⟩ := ih (half b l)
    refine ⟨l', ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply]; exact h1
    · rw [h2]; exact (getD_half l b (idxVal i)).symm

/-! ## One round as a transducer -/

def δstep : Option Bool → Bool ⊕ Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, Sum.inl b => (some b, none)
  | none, Sum.inr c => (none, some (Sum.inr c))
  | some k, Sum.inl c => (some k, some (Sum.inl c))
  | some k, Sum.inr c => (some (!k), if k = true then none else some (Sum.inr c))

def stepT (y : List (Bool ⊕ Bool)) : List (Bool ⊕ Bool) := fstRun δstep (fun _ => none) none y

theorem stepRun_none_str (l : List Bool) :
    fstRun δstep (fun _ => none) none (l.map Sum.inr) = l.map Sum.inr := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [fstRun, δstep, ih]

theorem stepRun_some_str (l : List Bool) : ∀ k : Bool,
    fstRun δstep (fun _ => none) (some k) (l.map Sum.inr) = (half k l).map Sum.inr := by
  induction l with
  | nil => intro k; cases k <;> rfl
  | cons c l ih => intro k; cases k <;> simp [fstRun, δstep, half, ih]

theorem stepRun_some_idx (k : Bool) (i l : List Bool) :
    fstRun δstep (fun _ => none) (some k) (i.map Sum.inl ++ l.map Sum.inr) =
      i.map Sum.inl ++ (half k l).map Sum.inr := by
  induction i with
  | nil => simpa using stepRun_some_str l k
  | cons b i ih => simp [fstRun, δstep, ih]

theorem stepT_encodePair (p : List Bool × List Bool) :
    stepT (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p) =
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (stepP p) := by
  obtain ⟨i, l⟩ := p
  cases i with
  | nil => exact stepRun_none_str l
  | cons b i => exact stepRun_some_idx b i l

theorem length_fstRun_le {A B Q : Type} (δ : Q → A → Q × Option B) (q : Q) (l : List A) :
    (fstRun δ (fun _ => none) q l).length ≤ l.length := by
  induction l generalizing q with
  | nil => simp [fstRun]
  | cons a l ih =>
    have h := ih (δ q a).1
    simp only [fstRun, List.length_append, List.length_cons]
    cases (δ q a).2 <;> simp <;> omega

/-! ## Packed raw lists read back -/

def δunpk : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, a => (some a, none)
  | some a, b => (none, some (if a = true then Sum.inr b else Sum.inl b))

def unpk (w : List Bool) : List (Bool ⊕ Bool) := fstRun δunpk (fun _ => none) none w

theorem unpk_packRaw (l : List (Bool ⊕ Bool)) : unpk (packRaw l) = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have h : unpk (packRaw (s :: l)) = s :: unpk (packRaw l) := by cases s <;> rfl
    rw [h, ih]

theorem length_packRaw (l : List (Bool ⊕ Bool)) : (packRaw l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have h : packRaw (s :: l) = Sum.isRight s :: Sum.elim id id s :: packRaw l := rfl
    rw [h]
    simp only [List.length_cons, ih]
    omega

theorem length_unpkRun_le (q : Option Bool) (w : List Bool) :
    2 * (fstRun δunpk (fun _ => none) q w).length ≤ w.length + (if q.isSome then 1 else 0) := by
  induction w generalizing q with
  | nil => simp [fstRun]
  | cons x w ih =>
    rcases q with _ | a
    · have h := ih (some x)
      simp only [fstRun, δunpk, Option.toList_none, List.nil_append, List.length_cons,
        Option.isSome_some, Option.isSome_none] at h ⊢
      simp at h ⊢
      omega
    · have h := ih none
      simp only [fstRun, δunpk, Option.toList_some, List.singleton_append, List.length_cons,
        Option.isSome_some, Option.isSome_none] at h ⊢
      simp at h ⊢
      omega

theorem length_unpk_le (w : List Bool) : 2 * (unpk w).length ≤ w.length := by
  simpa [unpk] using length_unpkRun_le none w

/-! ## The round on bit strings -/

def lookStep (w : List Bool) : List Bool := packRaw (stepT (unpk w))

theorem length_lookStep_le (w : List Bool) : (lookStep w).length ≤ w.length := by
  have h1 := length_fstRun_le δstep none (unpk w)
  have h2 := length_unpk_le w
  have h3 : (lookStep w).length = 2 * (stepT (unpk w)).length := length_packRaw _
  have h4 : (stepT (unpk w)).length ≤ (unpk w).length := h1
  omega

theorem cpt_packRaw :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) (fun x : List Bool => x) packRaw :=
  cpt_fstRun2 _ _ _

theorem cpt_unpk :
    ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l) unpk :=
  cpt_fstRun δunpk (fun _ => none) none

theorem cpt_lookStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lookStep :=
  cpt_congr (cpt_comp (cpt_fstRun_comp cpt_unpk δstep (fun _ => none) none) cpt_packRaw)
    (fun _ => rfl)

theorem lookStep_iter (k : ℕ) : ∀ p : List Bool × List Bool,
    lookStep^[k] (packRaw (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p)) =
      packRaw (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (stepP^[k] p)) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    simp only [lookStep, unpk_packRaw, stepT_encodePair]

/-! ## The read-out -/

def δread : Bool → Bool ⊕ Bool → Bool × Option Bool
  | false, Sum.inr c => (true, some c)
  | false, Sum.inl _ => (false, none)
  | true, _ => (true, none)

def finRead : Bool → Option Bool
  | false => some false
  | true => none

theorem readRun_true (y : List (Bool ⊕ Bool)) : fstRun δread finRead true y = [] := by
  induction y with
  | nil => rfl
  | cons s y ih => simp [fstRun, δread, ih]

theorem readRun_str (l : List Bool) :
    fstRun δread finRead false (l.map Sum.inr) = [l.getD 0 false] := by
  cases l with
  | nil => rfl
  | cons c l => simp [fstRun, δread, readRun_true]

/-! ## The lookup (upstream `cpt_lookup`) -/

theorem cpt_lookup :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => p.1.getD
        (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2)
        false) := by
  obtain ⟨c⟩ := cpt_lookStep
  have hI : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => lookStep^[p.2.length] p.1) :=
    Iter.iter_polyTime lookStep c 0 (fun y => by simpa using length_lookStep_le y)
  have h0 := pair_prod (cpt_comp cpt_swap cpt_pack) cpt_snd
  have h1 := cpt_comp h0 hI
  have h2 := cpt_fstRun_comp (cpt_comp h1 cpt_unpk) δread finRead false
  refine cpt_dec_of_bit (cpt_congr h2 (fun p => ?_))
  obtain ⟨l, i⟩ := p
  obtain ⟨l', e1, e2⟩ := stepP_iter i l
  show fstRun δread finRead false
    (unpk (lookStep^[i.length] (packRaw (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (i, l))))) = _
  rw [lookStep_iter, e1, unpk_packRaw]
  show fstRun δread finRead false (l'.map Sum.inr) = _
  rw [readRun_str, e2]
  rfl

/-- Upstream L098 in the campaign's definitions. -/
theorem main : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => p.1.getD
      (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false) :=
  cpt_lookup

/-- The same as a machine with a polynomial time bound. -/
theorem main_tm : Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => p.1.getD
      (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false)) :=
  main

/-- The same with an explicit polynomial step bound. -/
theorem main_time : ∃ (q : Polynomial ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodePair
    PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1.getD
      (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false)),
    ∀ n : ℕ, M.time n ≤ q.eval n := by
  obtain ⟨M⟩ := main
  exact ⟨M.time, M.toTM2ComputableInTime, fun _ => le_rfl⟩



theorem h_bool :
    PvsNP.PolyTimeComputable PvsNP.encodePair Computability.encodeBool (fun p : List Bool × List Bool => p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false) :=
  PvsNP.Units.m2_bit_lookup_polytime.main


theorem h_ifb :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + if b then 1 else 0) 0 p.2) false) :=
  PvsNP.Units.m2_bit_lookup_polytime.main


theorem h_x :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun x : List Bool × List Bool => x.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 x.2) false) :=
  PvsNP.Units.m2_bit_lookup_polytime.main


theorem h_tm :
    Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false)) :=
  PvsNP.Units.m2_bit_lookup_polytime.main_tm


theorem h_time :
    ∃ (q : Polynomial ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false)), ∀ n : ℕ, M.time n ≤ q.eval n :=
  PvsNP.Units.m2_bit_lookup_polytime.main_time


end PvsNP.Units.m2_bit_lookup_polytime

theorem PvsNP.Units.m2_bit_lookup_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false) :=
  PvsNP.Units.m2_bit_lookup_polytime.main
