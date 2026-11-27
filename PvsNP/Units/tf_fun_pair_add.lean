import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.tf_fun_pair_add

open Turing

def bitSum (a b c : Bool) : Bool :=
  xor (xor a b) c

def bitCarry (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

theorem bitSum_bitCarry_eq (a b c : Bool) :
    (bitSum a b c).toNat + 2 * (bitCarry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def binSumAcc : Bool → List Bool → List Bool → List Bool → List Bool
  | c, [], [], acc => if c then true :: acc else acc
  | c, a :: xs, [], acc => binSumAcc (bitCarry a false c) xs [] (bitSum a false c :: acc)
  | c, [], b :: ys, acc => binSumAcc (bitCarry false b c) [] ys (bitSum false b c :: acc)
  | c, a :: xs, b :: ys, acc => binSumAcc (bitCarry a b c) xs ys (bitSum a b c :: acc)

def stripZeros : List Bool → List Bool
  | [] => []
  | false :: rest => stripZeros rest
  | true :: rest => true :: rest

theorem ofDigits_append_singleton (xs : List ℕ) (d : ℕ) :
    Nat.ofDigits (2 : ℕ) (xs ++ [d]) = Nat.ofDigits (2 : ℕ) xs + 2 ^ xs.length * d := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.cons_append, Nat.ofDigits_cons, List.length_cons, ih, Nat.pow_succ]
    ring

theorem ofDigits_append_one_pos (xs : List Bool) :
    0 < Nat.ofDigits (2 : ℕ) ((xs ++ [true]).map Bool.toNat) := by
  rw [List.map_append, List.map_singleton, Bool.toNat_true, ofDigits_append_singleton]
  have hpow : 1 ≤ 2 ^ (xs.map Bool.toNat).length := Nat.one_le_two_pow
  omega

theorem bits_ofDigits_append_true (xs : List Bool) :
    Nat.bits (Nat.ofDigits (2 : ℕ) ((xs ++ [true]).map Bool.toNat)) = xs ++ [true] := by
  induction xs with
  | nil => decide
  | cons b rest ih =>
    simp only [List.cons_append, List.map_cons, Nat.ofDigits_cons]
    have hpos : 0 < Nat.ofDigits (2 : ℕ) ((rest ++ [true]).map Bool.toNat) :=
      ofDigits_append_one_pos rest
    have hne : Nat.ofDigits (2 : ℕ) ((rest ++ [true]).map Bool.toNat) ≠ 0 := by omega
    have hbit : b.toNat + 2 * Nat.ofDigits (2 : ℕ) ((rest ++ [true]).map Bool.toNat) =
        Nat.bit b (Nat.ofDigits (2 : ℕ) ((rest ++ [true]).map Bool.toNat)) := by
      cases b
      · simp [Nat.bit]
      · simp [Nat.bit]; omega
    rw [hbit, Nat.bits_append_bit _ _ (fun h => absurd h hne), ih]

theorem stripZeros_reverse_eq_bits (r : List Bool) :
    (stripZeros r).reverse = Nat.bits (Nat.ofDigits (2 : ℕ) (r.reverse.map Bool.toNat)) := by
  induction r with
  | nil => simp [stripZeros]
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [stripZeros, List.reverse_cons, List.map_append, List.map_singleton,
        Bool.toNat_false, ofDigits_append_singleton, mul_zero, Nat.add_zero]
      exact ih
    | true =>
      simp only [stripZeros, List.reverse_cons]
      exact (bits_ofDigits_append_true rest.reverse).symm

theorem binSumAcc_val (x y acc : List Bool) (c : Bool) :
    Nat.ofDigits (2 : ℕ) ((binSumAcc c x y acc).reverse.map Bool.toNat) =
      Nat.ofDigits (2 : ℕ) (acc.reverse.map Bool.toNat) +
        2 ^ acc.length *
          (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (y.map Bool.toNat) +
            c.toNat) := by
  induction x generalizing y acc c with
  | nil =>
    induction y generalizing acc c with
    | nil =>
      cases c with
      | false =>
        simp [binSumAcc]
      | true =>
        simp only [binSumAcc, ↓reduceIte, List.reverse_cons, List.map_append, List.map_singleton,
          Bool.toNat_true, ofDigits_append_singleton, List.length_map, List.length_reverse,
          List.map_nil, Nat.ofDigits_nil, Nat.zero_add]
    | cons b ys ihy =>
      simp only [binSumAcc, List.map_nil, Nat.ofDigits_nil, List.map_cons, Nat.ofDigits_cons]
      rw [ihy (bitSum false b c :: acc) (bitCarry false b c)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, ofDigits_append_singleton,
        List.length_map, List.length_reverse, List.length_cons, Nat.pow_succ,
        List.map_nil, Nat.ofDigits_nil]
      have hbc := bitSum_bitCarry_eq false b c
      simp only [Bool.toNat_false, Nat.zero_add] at hbc
      have hmul : 2 ^ acc.length * (bitSum false b c).toNat +
          2 ^ acc.length * 2 * (0 + Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat) + (bitCarry false b c).toNat) =
          2 ^ acc.length * (0 + (b.toNat + 2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) + c.toNat) := by
        calc 2 ^ acc.length * (bitSum false b c).toNat +
            2 ^ acc.length * 2 * (0 + Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat) + (bitCarry false b c).toNat)
            = 2 ^ acc.length * ((bitSum false b c).toNat + 2 * (bitCarry false b c).toNat +
                2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) := by ring
          _ = 2 ^ acc.length * (b.toNat + c.toNat +
                2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) := by rw [hbc]
          _ = 2 ^ acc.length * (0 + (b.toNat + 2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) + c.toNat) := by
              ring
      omega
  | cons a xs ihx =>
    cases y with
    | nil =>
      simp only [binSumAcc, List.map_cons, Nat.ofDigits_cons, List.map_nil, Nat.ofDigits_nil]
      rw [ihx [] (bitSum a false c :: acc) (bitCarry a false c)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, ofDigits_append_singleton,
        List.length_map, List.length_reverse, List.length_cons, Nat.pow_succ,
        List.map_nil, Nat.ofDigits_nil]
      have hbc := bitSum_bitCarry_eq a false c
      simp only [Bool.toNat_false, Nat.add_zero] at hbc
      have hmul : 2 ^ acc.length * (bitSum a false c).toNat +
          2 ^ acc.length * 2 * (Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + 0 + (bitCarry a false c).toNat) =
          2 ^ acc.length * (a.toNat + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + 0 + c.toNat) := by
        calc 2 ^ acc.length * (bitSum a false c).toNat +
            2 ^ acc.length * 2 * (Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + 0 + (bitCarry a false c).toNat)
            = 2 ^ acc.length * ((bitSum a false c).toNat + 2 * (bitCarry a false c).toNat +
                2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by ring
          _ = 2 ^ acc.length * (a.toNat + c.toNat +
                2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by rw [hbc]
          _ = 2 ^ acc.length * (a.toNat + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + 0 + c.toNat) := by
              ring
      omega
    | cons b ys =>
      simp only [binSumAcc, List.map_cons, Nat.ofDigits_cons]
      rw [ihx ys (bitSum a b c :: acc) (bitCarry a b c)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, ofDigits_append_singleton,
        List.length_map, List.length_reverse, List.length_cons, Nat.pow_succ]
      have hbc := bitSum_bitCarry_eq a b c
      have hmul : 2 ^ acc.length * (bitSum a b c).toNat +
          2 ^ acc.length * 2 *
            (Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat) +
              (bitCarry a b c).toNat) =
          2 ^ acc.length *
            (a.toNat + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) +
              (b.toNat + 2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) + c.toNat) := by
        calc 2 ^ acc.length * (bitSum a b c).toNat +
            2 ^ acc.length * 2 *
              (Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat) +
                (bitCarry a b c).toNat)
            = 2 ^ acc.length * ((bitSum a b c).toNat + 2 * (bitCarry a b c).toNat +
                2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) +
                2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) := by ring
          _ = 2 ^ acc.length * (a.toNat + b.toNat + c.toNat +
                2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) +
                2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) := by rw [hbc]
          _ = 2 ^ acc.length *
                (a.toNat + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) +
                  (b.toNat + 2 * Nat.ofDigits (2 : ℕ) (ys.map Bool.toNat)) + c.toNat) := by ring
      omega

theorem binSumAcc_len_le (x y acc : List Bool) (c : Bool) :
    (binSumAcc c x y acc).length ≤ acc.length + max x.length y.length + 1 := by
  induction x generalizing y acc c with
  | nil =>
    induction y generalizing acc c with
    | nil =>
      cases c <;> simp [binSumAcc]
    | cons b ys ihy =>
      simp only [binSumAcc]
      have h := ihy (bitSum false b c :: acc) (bitCarry false b c)
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ihx =>
    cases y with
    | nil =>
      simp only [binSumAcc]
      have h := ihx [] (bitSum a false c :: acc) (bitCarry a false c)
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      simp only [binSumAcc]
      have h := ihx ys (bitSum a b c :: acc) (bitCarry a b c)
      simp only [List.length_cons] at h ⊢
      omega

theorem stripZeros_binSumAcc_eq (x y : List Bool) :
    (stripZeros (binSumAcc false x y [])).reverse =
      Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (y.map Bool.toNat)) := by
  rw [stripZeros_reverse_eq_bits, binSumAcc_val]
  simp

inductive SStk
  | inp | rx | ry | sx | sy | out
  deriving DecidableEq

instance : Fintype SStk where
  elems := {.inp, .rx, .ry, .sx, .sy, .out}
  complete x := by cases x <;> simp

inductive SLbl
  | split | revX | revY | doAdd | strip | revOut
  deriving DecidableEq

instance : Fintype SLbl where
  elems := {.split, .revX, .revY, .doAdd, .strip, .revOut}
  complete x := by cases x <;> simp

abbrev SΓ : SStk → Type
  | .inp => Bool ⊕ Bool
  | _ => Bool

abbrev Sσ : Type := Bool × Option (Bool ⊕ Bool) × Option Bool × Option Bool

def initσ : Sσ := (false, none, none, none)

def sProg : SLbl → TM2.Stmt SΓ SLbl Sσ
  | .split =>
    .pop .inp (fun st o => (st.1, o, none, none))
      (.branch (fun st => st.2.1.isSome)
        (.branch (fun st => match st.2.1 with | some (Sum.inl _) => true | _ => false)
          (.push .rx (fun st => match st.2.1 with | some (Sum.inl a) => a | _ => false)
            (.load (fun _ => initσ) (.goto fun _ => .split)))
          (.push .ry (fun st => match st.2.1 with | some (Sum.inr b) => b | _ => false)
            (.load (fun _ => initσ) (.goto fun _ => .split))))
        (.load (fun _ => initσ) (.goto fun _ => .revX)))
  | .revX =>
    .pop .rx (fun st o => (st.1, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.push .sx (fun st => st.2.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revX)))
        (.load (fun _ => initσ) (.goto fun _ => .revY)))
  | .revY =>
    .pop .ry (fun st o => (st.1, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.push .sy (fun st => st.2.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revY)))
        (.load (fun _ => initσ) (.goto fun _ => .doAdd)))
  | .doAdd =>
    .pop .sx (fun st o => (st.1, none, o, none))
      (.pop .sy (fun st o => (st.1, none, st.2.2.1, o))
        (.branch (fun st => st.2.2.1.isSome || st.2.2.2.isSome)
          (.push .rx (fun st => bitSum (st.2.2.1.getD false) (st.2.2.2.getD false) st.1)
            (.load (fun st => (bitCarry (st.2.2.1.getD false) (st.2.2.2.getD false) st.1, none, none, none))
              (.goto fun _ => .doAdd)))
          (.branch (fun st => st.1)
            (.push .rx (fun _ => true)
              (.load (fun _ => initσ) (.goto fun _ => .strip)))
            (.load (fun _ => initσ) (.goto fun _ => .strip)))))
  | .strip =>
    .pop .rx (fun st o => (st.1, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.branch (fun st => st.2.2.1.getD false)
          (.push .out (fun _ => true)
            (.load (fun _ => initσ) (.goto fun _ => .revOut)))
          (.load (fun _ => initσ) (.goto fun _ => .strip)))
        (.load (fun _ => initσ) .halt))
  | .revOut =>
    .pop .rx (fun st o => (st.1, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.push .out (fun st => st.2.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revOut)))
        (.load (fun _ => initσ) .halt))

def sTM : FinTM2 where
  K := SStk
  k₀ := .inp
  k₁ := .out
  Γ := SΓ
  Λ := SLbl
  main := .split
  σ := Sσ
  initialState := initσ
  m := sProg

abbrev SCfg : Type := TM2.Cfg SΓ SLbl Sσ

def mkStk (i : List (Bool ⊕ Bool)) (rx ry sx sy o : List Bool) : ∀ k, List (SΓ k)
  | .inp => i
  | .rx => rx
  | .ry => ry
  | .sx => sx
  | .sy => sy
  | .out => o

theorem upd_inp (i i' : List (Bool ⊕ Bool)) (rx ry sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .inp i' = mkStk i' rx ry sx sy o := by
  funext k; cases k <;> rfl

theorem upd_rx (i : List (Bool ⊕ Bool)) (rx rx' ry sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .rx rx' = mkStk i rx' ry sx sy o := by
  funext k; cases k <;> rfl

theorem upd_ry (i : List (Bool ⊕ Bool)) (rx ry ry' sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .ry ry' = mkStk i rx ry' sx sy o := by
  funext k; cases k <;> rfl

theorem upd_sx (i : List (Bool ⊕ Bool)) (rx ry sx sx' sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .sx sx' = mkStk i rx ry sx' sy o := by
  funext k; cases k <;> rfl

theorem upd_sy (i : List (Bool ⊕ Bool)) (rx ry sx sy sy' o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .sy sy' = mkStk i rx ry sx sy' o := by
  funext k; cases k <;> rfl

theorem upd_out (i : List (Bool ⊕ Bool)) (rx ry sx sy o o' : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .out o' = mkStk i rx ry sx sy o' := by
  funext k; cases k <;> rfl

theorem initList_sTM (i : List (Bool ⊕ Bool)) :
    initList sTM i = (⟨some .split, initσ, mkStk i [] [] [] [] []⟩ : SCfg) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_sTM (o : List Bool) :
    haltList sTM o = (⟨none, initσ, mkStk [] [] [] [] [] o⟩ : SCfg) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

theorem step_split_inl (a : Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk (Sum.inl a :: rest) rx ry [] [] []⟩ : SCfg) =
      some ⟨some .split, initσ, mkStk rest (a :: rx) ry [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true]
  rw [upd_inp, upd_rx]
  rfl

theorem step_split_inr (b : Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk (Sum.inr b :: rest) rx ry [] [] []⟩ : SCfg) =
      some ⟨some .split, initσ, mkStk rest rx (b :: ry) [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Bool.cond_false]
  rw [upd_inp, upd_ry]
  rfl

theorem step_split_nil (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk [] rx ry [] [] []⟩ : SCfg) =
      some ⟨some .revX, initσ, mkStk [] rx ry [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_inp]

theorem loop_split_inl (x : List Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    (flip bind (TM2.step sProg))^[x.length]
        (some (⟨some .split, initσ, mkStk (x.map Sum.inl ++ rest) rx ry [] [] []⟩ : SCfg)) =
      some ⟨some .split, initσ, mkStk rest (x.reverse ++ rx) ry [] [] []⟩ := by
  induction x generalizing rx with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .split, initσ, mkStk (Sum.inl a :: (xs.map Sum.inl ++ rest)) rx ry [] [] []⟩ : SCfg)) =
        some ⟨some .split, initσ, mkStk (xs.map Sum.inl ++ rest) (a :: rx) ry [] [] []⟩ :=
      step_split_inl a (xs.map Sum.inl ++ rest) rx ry
    rw [e, ih (a :: rx)]
    simp

theorem loop_split_inr (y : List Bool) (rx ry : List Bool) :
    (flip bind (TM2.step sProg))^[y.length + 1]
        (some (⟨some .split, initσ, mkStk (y.map Sum.inr) rx ry [] [] []⟩ : SCfg)) =
      some ⟨some .revX, initσ, mkStk [] rx (y.reverse ++ ry) [] [] []⟩ := by
  induction y generalizing ry with
  | nil => exact step_split_nil rx ry
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .split, initσ, mkStk (Sum.inr b :: ys.map Sum.inr) rx ry [] [] []⟩ : SCfg)) =
        some ⟨some .split, initσ, mkStk (ys.map Sum.inr) rx (b :: ry) [] [] []⟩ :=
      step_split_inr b (ys.map Sum.inr) rx ry
    rw [e, ih (b :: ry)]
    simp

theorem step_revX_cons (a : Bool) (rx ry sx : List Bool) :
    TM2.step sProg (⟨some .revX, initσ, mkStk [] (a :: rx) ry sx [] []⟩ : SCfg) =
      some ⟨some .revX, initσ, mkStk [] rx ry (a :: sx) [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [upd_rx, upd_sx]
  rfl

theorem step_revX_nil (ry sx : List Bool) :
    TM2.step sProg (⟨some .revX, initσ, mkStk [] [] ry sx [] []⟩ : SCfg) =
      some ⟨some .revY, initσ, mkStk [] [] ry sx [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_rx]

theorem loop_revX (rx ry sx : List Bool) :
    (flip bind (TM2.step sProg))^[rx.length + 1]
        (some (⟨some .revX, initσ, mkStk [] rx ry sx [] []⟩ : SCfg)) =
      some ⟨some .revY, initσ, mkStk [] [] ry (rx.reverse ++ sx) [] []⟩ := by
  induction rx generalizing sx with
  | nil => exact step_revX_nil ry sx
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revX, initσ, mkStk [] (a :: xs) ry sx [] []⟩ : SCfg)) =
        some ⟨some .revX, initσ, mkStk [] xs ry (a :: sx) [] []⟩ :=
      step_revX_cons a xs ry sx
    rw [e, ih (a :: sx)]
    simp

theorem step_revY_cons (b : Bool) (ry sx sy : List Bool) :
    TM2.step sProg (⟨some .revY, initσ, mkStk [] [] (b :: ry) sx sy []⟩ : SCfg) =
      some ⟨some .revY, initσ, mkStk [] [] ry sx (b :: sy) []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [upd_ry, upd_sy]
  rfl

theorem step_revY_nil (sx sy : List Bool) :
    TM2.step sProg (⟨some .revY, initσ, mkStk [] [] [] sx sy []⟩ : SCfg) =
      some ⟨some .doAdd, initσ, mkStk [] [] [] sx sy []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_ry]

theorem loop_revY (ry sx sy : List Bool) :
    (flip bind (TM2.step sProg))^[ry.length + 1]
        (some (⟨some .revY, initσ, mkStk [] [] ry sx sy []⟩ : SCfg)) =
      some ⟨some .doAdd, initσ, mkStk [] [] [] sx (ry.reverse ++ sy) []⟩ := by
  induction ry generalizing sy with
  | nil => exact step_revY_nil sx sy
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revY, initσ, mkStk [] [] (b :: ys) sx sy []⟩ : SCfg)) =
        some ⟨some .revY, initσ, mkStk [] [] ys sx (b :: sy) []⟩ :=
      step_revY_cons b ys sx sy
    rw [e, ih (b :: sy)]
    simp

theorem step_doAdd_nil_nil (c : Bool) (acc : List Bool) :
    TM2.step sProg (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] [] [] []⟩ : SCfg) =
      some ⟨some .strip, initσ, mkStk [] (if c then true :: acc else acc) [] [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux]
  rw [upd_sx]
  simp only [mkStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.or_self,
    Bool.cond_false]
  rw [upd_sy]
  cases c with
  | false => rfl
  | true =>
    simp only [Bool.cond_true, mkStk]
    rw [upd_rx]
    rfl

theorem step_doAdd_cons_nil (c a : Bool) (xs acc : List Bool) :
    TM2.step sProg (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] (a :: xs) [] []⟩ : SCfg) =
      some ⟨some .doAdd, (bitCarry a false c, none, none, none),
        mkStk [] (bitSum a false c :: acc) [] xs [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux]
  rw [upd_sx]
  simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.cond_true,
    Option.getD_some, Option.getD_none]
  rw [upd_sy]
  simp only [mkStk]
  rw [upd_rx]

theorem step_doAdd_nil_cons (c b : Bool) (ys acc : List Bool) :
    TM2.step sProg (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] [] (b :: ys) []⟩ : SCfg) =
      some ⟨some .doAdd, (bitCarry false b c, none, none, none),
        mkStk [] (bitSum false b c :: acc) [] [] ys []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux]
  rw [upd_sx]
  simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Bool.false_or, Bool.cond_true,
    Option.getD_some, Option.getD_none]
  rw [upd_sy]
  simp only [mkStk]
  rw [upd_rx]

theorem step_doAdd_cons_cons (c a b : Bool) (xs ys acc : List Bool) :
    TM2.step sProg (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] (a :: xs) (b :: ys) []⟩ : SCfg) =
      some ⟨some .doAdd, (bitCarry a b c, none, none, none),
        mkStk [] (bitSum a b c :: acc) [] xs ys []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux]
  rw [upd_sx]
  simp only [mkStk, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.or_self,
    Bool.cond_true, Option.getD_some]
  rw [upd_sy]
  simp only [mkStk]
  rw [upd_rx]

theorem loop_doAdd (sx sy acc : List Bool) (c : Bool) :
    (flip bind (TM2.step sProg))^[max sx.length sy.length + 1]
        (some (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] sx sy []⟩ : SCfg)) =
      some ⟨some .strip, initσ, mkStk [] (binSumAcc c sx sy acc) [] [] [] []⟩ := by
  induction sx generalizing sy acc c with
  | nil =>
    induction sy generalizing acc c with
    | nil =>
      simp only [binSumAcc]
      exact step_doAdd_nil_nil c acc
    | cons b ys ihy =>
      have hmax : max ([] : List Bool).length (b :: ys).length + 1 =
          (max ([] : List Bool).length ys.length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] [] (b :: ys) []⟩ : SCfg)) =
          some ⟨some .doAdd, (bitCarry false b c, none, none, none),
            mkStk [] (bitSum false b c :: acc) [] [] ys []⟩ :=
        step_doAdd_nil_cons c b ys acc
      rw [e, ihy (bitSum false b c :: acc) (bitCarry false b c)]
      simp only [binSumAcc]
  | cons a xs ihx =>
    cases sy with
    | nil =>
      have hmax : max (a :: xs).length ([] : List Bool).length + 1 =
          (max xs.length ([] : List Bool).length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] (a :: xs) [] []⟩ : SCfg)) =
          some ⟨some .doAdd, (bitCarry a false c, none, none, none),
            mkStk [] (bitSum a false c :: acc) [] xs [] []⟩ :=
        step_doAdd_cons_nil c a xs acc
      rw [e, ihx [] (bitSum a false c :: acc) (bitCarry a false c)]
      simp only [binSumAcc]
    | cons b ys =>
      have hmax : max (a :: xs).length (b :: ys).length + 1 =
          (max xs.length ys.length + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doAdd, (c, none, none, none), mkStk [] acc [] (a :: xs) (b :: ys) []⟩ : SCfg)) =
          some ⟨some .doAdd, (bitCarry a b c, none, none, none),
            mkStk [] (bitSum a b c :: acc) [] xs ys []⟩ :=
        step_doAdd_cons_cons c a b xs ys acc
      rw [e, ihx ys (bitSum a b c :: acc) (bitCarry a b c)]
      simp only [binSumAcc]

theorem step_revOut_cons (b : Bool) (rx out : List Bool) :
    TM2.step sProg (⟨some .revOut, initσ, mkStk [] (b :: rx) [] [] [] out⟩ : SCfg) =
      some ⟨some .revOut, initσ, mkStk [] rx [] [] [] (b :: out)⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [upd_rx, upd_out]
  rfl

theorem step_revOut_nil (out : List Bool) :
    TM2.step sProg (⟨some .revOut, initσ, mkStk [] [] [] [] [] out⟩ : SCfg) =
      some ⟨none, initσ, mkStk [] [] [] [] [] out⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_rx]

theorem loop_revOut (rx out : List Bool) :
    (flip bind (TM2.step sProg))^[rx.length + 1]
        (some (⟨some .revOut, initσ, mkStk [] rx [] [] [] out⟩ : SCfg)) =
      some ⟨none, initσ, mkStk [] [] [] [] [] (rx.reverse ++ out)⟩ := by
  induction rx generalizing out with
  | nil => exact step_revOut_nil out
  | cons b xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revOut, initσ, mkStk [] (b :: xs) [] [] [] out⟩ : SCfg)) =
        some ⟨some .revOut, initσ, mkStk [] xs [] [] [] (b :: out)⟩ :=
      step_revOut_cons b xs out
    rw [e, ih (b :: out)]
    simp

theorem step_strip_nil :
    TM2.step sProg (⟨some .strip, initσ, mkStk [] [] [] [] [] []⟩ : SCfg) =
      some ⟨none, initσ, mkStk [] [] [] [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_rx]

theorem step_strip_false (rest : List Bool) :
    TM2.step sProg (⟨some .strip, initσ, mkStk [] (false :: rest) [] [] [] []⟩ : SCfg) =
      some ⟨some .strip, initσ, mkStk [] rest [] [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some, Bool.cond_false]
  rw [upd_rx]

theorem step_strip_true (rest : List Bool) :
    TM2.step sProg (⟨some .strip, initσ, mkStk [] (true :: rest) [] [] [] []⟩ : SCfg) =
      some ⟨some .revOut, initσ, mkStk [] rest [] [] [] [true]⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [upd_rx, upd_out]
  rfl

def stripSteps : List Bool → ℕ
  | [] => 1
  | false :: rest => stripSteps rest + 1
  | true :: rest => rest.length + 2

theorem stripSteps_le (r : List Bool) : stripSteps r ≤ r.length + 1 := by
  induction r with
  | nil => simp [stripSteps]
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [stripSteps, List.length_cons]
      omega
    | true =>
      simp only [stripSteps, List.length_cons]
      omega

theorem loop_strip (r : List Bool) :
    (flip bind (TM2.step sProg))^[stripSteps r]
        (some (⟨some .strip, initσ, mkStk [] r [] [] [] []⟩ : SCfg)) =
      some ⟨none, initσ, mkStk [] [] [] [] [] (stripZeros r).reverse⟩ := by
  induction r with
  | nil =>
    exact step_strip_nil
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [stripSteps, stripZeros]
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .strip, initσ, mkStk [] (false :: rest) [] [] [] []⟩ : SCfg)) =
          some ⟨some .strip, initσ, mkStk [] rest [] [] [] []⟩ :=
        step_strip_false rest
      rw [e]
      exact ih
    | true =>
      simp only [stripSteps, stripZeros, List.reverse_cons]
      have hst : rest.length + 2 = (rest.length + 1) + 1 := rfl
      rw [hst, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .strip, initσ, mkStk [] (true :: rest) [] [] [] []⟩ : SCfg)) =
          some ⟨some .revOut, initσ, mkStk [] rest [] [] [] [true]⟩ :=
        step_strip_true rest
      rw [e]
      exact loop_revOut rest [true]

theorem sTM_run (x y : List Bool) :
    (flip bind (TM2.step sProg))^[
        stripSteps (binSumAcc false x y []) +
        (max x.length y.length + 1) +
        (y.length + 1) +
        (x.length + 1) +
        (y.length + 1) +
        x.length]
        (some (initList sTM (PvsNP.encodePair (x, y)))) =
      some (haltList sTM (stripZeros (binSumAcc false x y [])).reverse) := by
  have henc : PvsNP.encodePair (x, y) = x.map Sum.inl ++ y.map Sum.inr := by
    simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
  refine (congrArg (fun c => (flip bind (TM2.step sProg))^[
      stripSteps (binSumAcc false x y []) + (max x.length y.length + 1) +
      (y.length + 1) + (x.length + 1) + (y.length + 1) + x.length]
      (some c)) (initList_sTM (PvsNP.encodePair (x, y)))).trans
    (Eq.trans ?_ (congrArg some (haltList_sTM (stripZeros (binSumAcc false x y [])).reverse)).symm)
  rw [henc]
  rw [Function.iterate_add_apply, loop_split_inl x (y.map Sum.inr) [] []]
  rw [List.append_nil]
  rw [Function.iterate_add_apply, loop_split_inr y x.reverse []]
  rw [List.append_nil]
  have hrevX := loop_revX x.reverse y.reverse []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevX
  rw [Function.iterate_add_apply, hrevX]
  have hrevY := loop_revY y.reverse x []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevY
  rw [Function.iterate_add_apply, hrevY]
  rw [Function.iterate_add_apply]
  have hdoAdd := loop_doAdd x y [] false
  change (flip bind (TM2.step sProg))^[max x.length y.length + 1]
      (some (⟨some .doAdd, initσ, mkStk [] [] [] x y []⟩ : SCfg)) =
    some ⟨some .strip, initσ, mkStk [] (binSumAcc false x y []) [] [] [] []⟩ at hdoAdd
  rw [hdoAdd]
  exact loop_strip (binSumAcc false x y [])

theorem pair_add_aux :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  ⟨{
    tm := sTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 6
    outputsFun := fun p =>
      { steps :=
          stripSteps (binSumAcc false p.1 p.2 []) +
          (max p.1.length p.2.length + 1) +
          (p.2.length + 1) +
          (p.1.length + 1) +
          (p.2.length + 1) +
          p.1.length
        evals_in_steps := by
          have hm1 : List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair p) =
              PvsNP.encodePair p := by simp
          have hm2 : List.map (Equiv.refl Bool).invFun
              (PvsNP.encodeString (Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) +
                Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) =
              (stripZeros (binSumAcc false p.1 p.2 [])).reverse := by
            simp [PvsNP.encodeString, Computability.encodingList, stripZeros_binSumAcc_eq]
          exact (congrArg (fun i => (flip bind (TM2.step sProg))^[
              stripSteps (binSumAcc false p.1 p.2 []) + (max p.1.length p.2.length + 1) +
              (p.2.length + 1) + (p.1.length + 1) + (p.2.length + 1) + p.1.length]
              (some (initList sTM i))) hm1).trans
            ((sTM_run p.1 p.2).trans
              (congrArg (fun o => some (haltList sTM o)) hm2.symm))
        steps_le_m := by
          have hlen : (PvsNP.encodePair p).length = p.1.length + p.2.length := by
            simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
          have hs1 := stripSteps_le (binSumAcc false p.1 p.2 [])
          have hs2 := binSumAcc_len_le p.1 p.2 [] false
          simp only [List.length_nil, Nat.zero_add] at hs2
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, hlen]
          omega } }⟩

end PvsNP.Units.tf_fun_pair_add

/-- Adding two binary-encoded natural numbers (LSB first) is polynomial-time computable (TM2). -/
theorem PvsNP.Units.tf_fun_pair_add :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_pair_add.pair_add_aux
