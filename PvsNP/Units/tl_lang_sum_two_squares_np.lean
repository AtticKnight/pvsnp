import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_sum_two_squares_np

open Turing

/-! ### Bit-list arithmetic and certificate encoding -/

/-- Value of a least-significant-bit-first binary string. -/
private def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

private theorem val_nil : val [] = 0 := rfl

private theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := rfl

private theorem val_append (l₁ l₂ : List Bool) :
    val (l₁ ++ l₂) = val l₁ + 2 ^ l₁.length * val l₂ := by
  unfold val
  rw [List.map_append, Nat.ofDigits_append, List.length_map]

private theorem val_eq_head_add_two_tail (l : List Bool) :
    val l = (l.head?.getD false).toNat + 2 * val l.tail := by
  cases l with
  | nil => rfl
  | cons b l => rfl

private theorem val_lt_two_pow : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by simp [val]
  | b :: l => by
    have ih := val_lt_two_pow l
    rw [val_cons, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

/-- Fixed-width LSB-first binary representation of a natural number. -/
private def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: toBits k (n / 2)

private theorem toBits_length : ∀ (k n : ℕ), (toBits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [toBits, toBits_length k (n / 2)]

private theorem val_toBits : ∀ (k n : ℕ), n < 2 ^ k → val (toBits k n) = n
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0; rfl
  | k + 1, n, hn => by
    have hhalf : n / 2 < 2 ^ k := by
      rw [pow_succ'] at hn
      omega
    have ih := val_toBits k (n / 2) hhalf
    rw [toBits, val_cons, ih]
    have hmod : (n % 2 == 1).toNat = n % 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    rw [hmod]
    omega

/-- De-interleave a certificate bitstring into two bitstrings according to a starting parity. -/
private def splitParity : Bool → List Bool → List Bool × List Bool
  | _, [] => ([], [])
  | false, b :: rest =>
    let p := splitParity true rest
    (b :: p.1, p.2)
  | true, b :: rest =>
    let p := splitParity false rest
    (p.1, b :: p.2)

private theorem splitParity_length :
    ∀ (p : Bool) (w : List Bool), (splitParity p w).1.length + (splitParity p w).2.length = w.length
  | _, [] => rfl
  | false, _ :: rest => by
    have ih := splitParity_length true rest
    simp only [splitParity, List.length_cons]
    omega
  | true, _ :: rest => by
    have ih := splitParity_length false rest
    simp only [splitParity, List.length_cons]
    omega

/-- Interleave two bitstrings. -/
private def interleave : List Bool → List Bool → List Bool
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x :: y :: interleave xs ys

private theorem interleave_length :
    ∀ (xs ys : List Bool), (interleave xs ys).length = xs.length + ys.length
  | [], ys => by simp [interleave]
  | x :: xs, [] => by simp [interleave]
  | x :: xs, y :: ys => by
    have ih := interleave_length xs ys
    simp only [interleave, List.length_cons]
    omega

private theorem splitParity_interleave :
    ∀ (xs ys : List Bool), xs.length = ys.length →
      splitParity false (interleave xs ys) = (xs, ys)
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have hlen : xs.length = ys.length := by simpa using h
    have ih := splitParity_interleave xs ys hlen
    simp only [interleave, splitParity, ih]

/-- Full-adder sum bit and carry bit. -/
private def addBit (a b c : Bool) : Bool := xor (xor a b) c

private def addCarry (a b c : Bool) : Bool := (a && b) || (c && (a || b))

private theorem addBit_addCarry_spec (a b c : Bool) :
    (addBit a b c).toNat + 2 * (addCarry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- LSB-first binary addition with carry-in. -/
private def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], false => []
  | [], [], true => [true]
  | a :: as, [], c => addBit a false c :: addBits as [] (addCarry a false c)
  | [], b :: bs, c => addBit false b c :: addBits [] bs (addCarry false b c)
  | a :: as, b :: bs, c => addBit a b c :: addBits as bs (addCarry a b c)

private theorem val_addBits :
    ∀ (as bs : List Bool) (c : Bool), val (addBits as bs c) = val as + val bs + c.toNat
  | [], [], false => by simp [addBits, val]
  | [], [], true => by simp [addBits, val]
  | a :: as, [], c => by
    have ih := val_addBits as [] (addCarry a false c)
    have h := addBit_addCarry_spec a false c
    simp only [addBits, val_cons, val_nil, Bool.toNat_false] at ih h ⊢
    omega
  | [], b :: bs, c => by
    have ih := val_addBits [] bs (addCarry false b c)
    have h := addBit_addCarry_spec false b c
    simp only [addBits, val_cons, val_nil, Bool.toNat_false] at ih h ⊢
    omega
  | a :: as, b :: bs, c => by
    have ih := val_addBits as bs (addCarry a b c)
    have h := addBit_addCarry_spec a b c
    simp only [addBits, val_cons] at ih ⊢
    omega

private theorem length_addBits :
    ∀ (as bs : List Bool) (c : Bool), (addBits as bs c).length ≤ max as.length bs.length + 1
  | [], [], false => by simp [addBits]
  | [], [], true => by simp [addBits]
  | a :: as, [], c => by
    have ih := length_addBits as [] (addCarry a false c)
    simp only [addBits, List.length_cons, List.length_nil] at ih ⊢
    omega
  | [], b :: bs, c => by
    have ih := length_addBits [] bs (addCarry false b c)
    simp only [addBits, List.length_cons, List.length_nil] at ih ⊢
    omega
  | a :: as, b :: bs, c => by
    have ih := length_addBits as bs (addCarry a b c)
    simp only [addBits, List.length_cons] at ih ⊢
    omega

/-- Horner shift-and-add squaring accumulator over MSB-first multiplier bits `ds`. -/
private def sqAcc (v : List Bool) : List Bool → List Bool → List Bool
  | [], acc => acc
  | false :: ds, acc => sqAcc v ds (false :: acc)
  | true :: ds, acc => sqAcc v ds (addBits v (false :: acc) false)

private theorem val_sqAcc (v : List Bool) :
    ∀ (ds acc : List Bool),
      val (sqAcc v ds acc) = 2 ^ ds.length * val acc + val ds.reverse * val v
  | [], acc => by simp [sqAcc, val_nil]
  | false :: ds, acc => by
    have ih := val_sqAcc v ds (false :: acc)
    rw [sqAcc, ih, val_cons, Bool.toNat_false, zero_add, List.length_cons, List.reverse_cons,
      val_append, List.length_reverse]
    simp only [val_cons, val_nil, Bool.toNat_false, mul_zero, add_zero]
    rw [pow_succ']
    ring
  | true :: ds, acc => by
    have ih := val_sqAcc v ds (addBits v (false :: acc) false)
    rw [sqAcc, ih, val_addBits, val_cons, Bool.toNat_false, zero_add, add_zero,
      List.length_cons, List.reverse_cons, val_append, List.length_reverse]
    simp only [val_cons, val_nil, Bool.toNat_true, mul_zero, add_zero]
    rw [pow_succ']
    ring

private theorem val_sqAcc_self (v : List Bool) :
    val (sqAcc v v.reverse []) = (val v) ^ 2 := by
  rw [val_sqAcc, val_nil, mul_zero, zero_add, List.reverse_reverse, sq]

private theorem length_sqAcc (v : List Bool) :
    ∀ (ds acc : List Bool),
      (sqAcc v ds acc).length ≤ max v.length acc.length + 2 * ds.length
  | [], acc => by
    simp only [sqAcc, List.length_nil, mul_zero, add_zero]
    exact le_max_right _ _
  | false :: ds, acc => by
    have ih := length_sqAcc v ds (false :: acc)
    simp only [sqAcc, List.length_cons] at ih ⊢
    omega
  | true :: ds, acc => by
    have ih := length_sqAcc v ds (addBits v (false :: acc) false)
    have hadd := length_addBits v (false :: acc) false
    simp only [sqAcc, List.length_cons] at ih hadd ⊢
    omega

private theorem length_sqAcc_self (v : List Bool) :
    (sqAcc v v.reverse []).length ≤ 3 * v.length := by
  have h := length_sqAcc v v.reverse []
  simp only [List.length_nil, List.length_reverse] at h
  omega

/-- The verifier boolean function for sums of two squares. -/
private def verifier (p : List Bool × List Bool) : Bool :=
  let ab := splitParity false p.2
  decide ((val ab.1) ^ 2 + (val ab.2) ^ 2 = val p.1)

/-! ### Multi-stack Turing machine (`FinTM2`) for `verifier` -/

private inductive SK : Type
  | inp | out | sx | sb | su | sm | sd | smBak | sacc | saccBak
  deriving DecidableEq

private instance : Fintype SK :=
  Fintype.ofEquiv (Fin 10)
    { toFun := fun i => match i.1 with
        | 0 => .inp | 1 => .out | 2 => .sx | 3 => .sb | 4 => .su
        | 5 => .sm | 6 => .sd | 7 => .smBak | 8 => .sacc | _ => .saccBak
      invFun := fun k => match k with
        | .inp => 0 | .out => 1 | .sx => 2 | .sb => 3 | .su => 4
        | .sm => 5 | .sd => 6 | .smBak => 7 | .sacc => 8 | .saccBak => 9
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun k => by cases k <;> rfl }

private abbrev SΓ : SK → Type
  | .inp => Bool ⊕ Bool
  | _ => Bool

private inductive SL : Type
  | split | revAll | dupToD | revM | sqStep | sqAdd | sqRev | cleanM | move1 | move2 | cmp
  deriving DecidableEq

private instance : Fintype SL :=
  Fintype.ofEquiv (Fin 11)
    { toFun := fun i => match i.1 with
        | 0 => .split | 1 => .revAll | 2 => .dupToD | 3 => .revM | 4 => .sqStep
        | 5 => .sqAdd | 6 => .sqRev | 7 => .cleanM | 8 => .move1 | 9 => .move2 | _ => .cmp
      invFun := fun l => match l with
        | .split => 0 | .revAll => 1 | .dupToD => 2 | .revM => 3 | .sqStep => 4
        | .sqAdd => 5 | .sqRev => 6 | .cleanM => 7 | .move1 => 8 | .move2 => 9 | .cmp => 10
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun l => by cases l <;> rfl }

/-- Internal state: `(inSym, b1, b2, b3, flag1, flag2, flag3)`.
`flag1` is `parity` in `split` and `phase` in the squaring phases;
`flag2` is `carry` in `sqAdd`/`cmp`; `flag3` is `ok` in `cmp`. -/
private abbrev Sσ : Type :=
  Option (Bool ⊕ Bool) × Option Bool × Option Bool × Option Bool × Bool × Bool × Bool

private def st (f1 f2 f3 : Bool) : Sσ :=
  (none, none, none, none, f1, f2, f3)

private def initS : Sσ := st false false false

private def optPush (k : SK) (hk : SΓ k = Bool) (get : Sσ → Option Bool)
    (next : TM2.Stmt SΓ SL Sσ) : TM2.Stmt SΓ SL Sσ :=
  .branch (fun s => (get s).isSome)
    (.push k (fun s => hk ▸ (get s).getD false) next)
    next

private def optCons (o : Option Bool) (l : List Bool) : List Bool :=
  o.elim l (fun b => b :: l)

private theorem reverse_tail_append_optCons (l acc : List Bool) :
    l.tail.reverse ++ optCons l.head? acc = l.reverse ++ acc := by
  cases l <;> simp [optCons]

private def sqProg : SL → TM2.Stmt SΓ SL Sσ
  | .split =>
    .pop .inp (fun s o => (o, none, none, none, s.2.2.2.2.1, false, false))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => (s.1.bind Sum.getLeft?).isSome)
          (.push .smBak (fun s => (s.1.bind Sum.getLeft?).getD false)
            (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .split)))
          (.branch (fun s => s.2.2.2.2.1)
            (.push .saccBak (fun s => (s.1.bind Sum.getRight?).getD false)
              (.load (fun _ => st false false false) (.goto fun _ => .split)))
            (.push .sd (fun s => (s.1.bind Sum.getRight?).getD false)
              (.load (fun _ => st true false false) (.goto fun _ => .split)))))
        (.load (fun _ => initS) (.goto fun _ => .revAll)))
  | .revAll =>
    .pop .smBak (fun _ o => (none, o, none, none, false, false, false))
      (.pop .sd (fun s o => (none, s.2.1, o, none, false, false, false))
        (.pop .saccBak (fun s o => (none, s.2.1, s.2.2.1, o, false, false, false))
          (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome || s.2.2.2.1.isSome)
            (optPush .sx rfl (fun s => s.2.1)
              (optPush .sm rfl (fun s => s.2.2.1)
                (optPush .sb rfl (fun s => s.2.2.2.1)
                  (.load (fun _ => initS) (.goto fun _ => .revAll)))))
            (.load (fun _ => initS) (.goto fun _ => .dupToD)))))
  | .dupToD =>
    .pop .sm (fun s o => (none, o, none, none, s.2.2.2.2.1, false, false))
      (.branch (fun s => s.2.1.isSome)
        (.push .smBak (fun s => s.2.1.getD false)
          (.push .sd (fun s => s.2.1.getD false)
            (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .dupToD))))
        (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .revM)))
  | .revM =>
    .pop .smBak (fun s o => (none, o, none, none, s.2.2.2.2.1, false, false))
      (.branch (fun s => s.2.1.isSome)
        (.push .sm (fun s => s.2.1.getD false)
          (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .revM)))
        (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqStep)))
  | .sqStep =>
    .pop .sd (fun s o => (none, o, none, none, s.2.2.2.2.1, false, false))
      (.branch (fun s => s.2.1.isSome)
        (.push .sacc (fun _ => false)
          (.branch (fun s => s.2.1.getD false)
            (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqAdd))
            (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqStep))))
        (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .cleanM)))
  | .sqAdd =>
    .pop .sm (fun s o => (none, o, none, none, s.2.2.2.2.1, s.2.2.2.2.2.1, false))
      (.pop .sacc (fun s o => (none, s.2.1, o, none, s.2.2.2.2.1, s.2.2.2.2.2.1, false))
        (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome || s.2.2.2.2.2.1)
          (optPush .smBak rfl (fun s => s.2.1)
            (.push .saccBak
              (fun s => addBit (s.2.1.getD false) (s.2.2.1.getD false) s.2.2.2.2.2.1)
              (.load
                (fun s => st s.2.2.2.2.1
                  (addCarry (s.2.1.getD false) (s.2.2.1.getD false) s.2.2.2.2.2.1) false)
                (.goto fun _ => .sqAdd))))
          (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqRev))))
  | .sqRev =>
    .pop .smBak (fun s o => (none, o, none, none, s.2.2.2.2.1, false, false))
      (.pop .saccBak (fun s o => (none, s.2.1, o, none, s.2.2.2.2.1, false, false))
        (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome)
          (optPush .sm rfl (fun s => s.2.1)
            (optPush .sacc rfl (fun s => s.2.2.1)
              (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqRev))))
          (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .sqStep))))
  | .cleanM =>
    .pop .sm (fun s o => (none, o, none, none, s.2.2.2.2.1, false, false))
      (.branch (fun s => s.2.1.isSome)
        (.load (fun s => st s.2.2.2.2.1 false false) (.goto fun _ => .cleanM))
        (.branch (fun s => s.2.2.2.2.1)
          (.load (fun _ => st false false true) (.goto fun _ => .cmp))
          (.load (fun _ => initS) (.goto fun _ => .move1))))
  | .move1 =>
    .pop .sb (fun _ o => (none, o, none, none, false, false, false))
      (.pop .sacc (fun s o => (none, s.2.1, o, none, false, false, false))
        (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome)
          (optPush .smBak rfl (fun s => s.2.1)
            (optPush .saccBak rfl (fun s => s.2.2.1)
              (.load (fun _ => initS) (.goto fun _ => .move1))))
          (.load (fun _ => initS) (.goto fun _ => .move2))))
  | .move2 =>
    .pop .smBak (fun _ o => (none, o, none, none, false, false, false))
      (.pop .saccBak (fun s o => (none, s.2.1, o, none, false, false, false))
        (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome)
          (optPush .sm rfl (fun s => s.2.1)
            (optPush .su rfl (fun s => s.2.2.1)
              (.load (fun _ => initS) (.goto fun _ => .move2))))
          (.load (fun _ => st true false false) (.goto fun _ => .dupToD))))
  | .cmp =>
    .pop .su (fun s o => (none, o, none, none, false, s.2.2.2.2.2.1, s.2.2.2.2.2.2))
      (.pop .sacc (fun s o => (none, s.2.1, o, none, false, s.2.2.2.2.2.1, s.2.2.2.2.2.2))
        (.pop .sx (fun s o => (none, s.2.1, s.2.2.1, o, false, s.2.2.2.2.2.1, s.2.2.2.2.2.2))
          (.branch (fun s => s.2.1.isSome || s.2.2.1.isSome || s.2.2.2.1.isSome)
            (.load (fun s =>
              let bu := s.2.1.getD false
              let bv := s.2.2.1.getD false
              let bx := s.2.2.2.1.getD false
              let c := s.2.2.2.2.2.1
              let ok := s.2.2.2.2.2.2
              st false (addCarry bu bv c) (ok && (addBit bu bv c == bx)))
              (.goto fun _ => .cmp))
            (.push .out (fun s => s.2.2.2.2.2.2 && !s.2.2.2.2.2.1)
              (.load (fun _ => initS) .halt)))))

private def sqTM : FinTM2 where
  K := SK
  k₀ := .inp
  k₁ := .out
  Γ := SΓ
  Λ := SL
  main := .split
  σ := Sσ
  initialState := initS
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := sqProg

private def mkCfg (l : Option SL) (var : Sσ)
    (inp : List (Bool ⊕ Bool)) (out sx sb su sm sd smBak sacc saccBak : List Bool) :
    sqTM.Cfg where
  l := l
  var := var
  stk k := match k with
    | .inp => inp
    | .out => out
    | .sx => sx
    | .sb => sb
    | .su => su
    | .sm => sm
    | .sd => sd
    | .smBak => smBak
    | .sacc => sacc
    | .saccBak => saccBak

private theorem cfg_ext {c₁ c₂ : sqTM.Cfg}
    (h1 : c₁.l = c₂.l) (h2 : c₁.var = c₂.var) (h3 : ∀ k, c₁.stk k = c₂.stk k) :
    c₁ = c₂ := by
  cases c₁ with
  | mk l1 v1 s1 =>
    cases c₂ with
    | mk l2 v2 s2 =>
      simp only at h1 h2 h3
      subst h1; subst h2
      have hs : s1 = s2 := funext h3
      subst hs
      rfl

/-! ### Phase 1: `split` -/

private theorem step_split_inl (b : Bool) (rest : List (Bool ⊕ Bool)) (smBak : List Bool) :
    sqTM.step (mkCfg (some .split) initS (Sum.inl b :: rest) [] [] [] [] [] [] smBak [] []) =
      some (mkCfg (some .split) initS rest [] [] [] [] [] [] (b :: smBak) [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_split_inr_false (b : Bool) (rest : List (Bool ⊕ Bool))
    (sd smBak saccBak : List Bool) :
    sqTM.step (mkCfg (some .split) (st false false false) (Sum.inr b :: rest)
        [] [] [] [] [] sd smBak [] saccBak) =
      some (mkCfg (some .split) (st true false false) rest
        [] [] [] [] [] (b :: sd) smBak [] saccBak) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_split_inr_true (b : Bool) (rest : List (Bool ⊕ Bool))
    (sd smBak saccBak : List Bool) :
    sqTM.step (mkCfg (some .split) (st true false false) (Sum.inr b :: rest)
        [] [] [] [] [] sd smBak [] saccBak) =
      some (mkCfg (some .split) (st false false false) rest
        [] [] [] [] [] sd smBak [] (b :: saccBak)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_split_nil (p : Bool) (sd smBak saccBak : List Bool) :
    sqTM.step (mkCfg (some .split) (st p false false) [] [] [] [] [] [] sd smBak [] saccBak) =
      some (mkCfg (some .revAll) initS [] [] [] [] [] [] sd smBak [] saccBak) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_split_inl :
    ∀ (x : List Bool) (rest : List (Bool ⊕ Bool)) (smBak : List Bool),
      (flip bind sqTM.step)^[x.length]
        (some (mkCfg (some .split) initS (x.map Sum.inl ++ rest) [] [] [] [] [] [] smBak [] [])) =
        some (mkCfg (some .split) initS rest [] [] [] [] [] [] (x.reverse ++ smBak) [] [])
  | [], rest, smBak => rfl
  | b :: x, rest, smBak => by
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[x.length]
      (sqTM.step (mkCfg (some .split) initS (Sum.inl b :: (x.map Sum.inl ++ rest))
        [] [] [] [] [] [] smBak [] [])) = _
    rw [step_split_inl]
    simpa [List.reverse_cons, List.append_assoc] using eval_split_inl x rest (b :: smBak)

private theorem eval_split_inr :
    ∀ (w : List Bool) (p : Bool) (sd smBak saccBak : List Bool),
      (flip bind sqTM.step)^[w.length + 1]
        (some (mkCfg (some .split) (st p false false) (w.map Sum.inr)
          [] [] [] [] [] sd smBak [] saccBak)) =
        some (mkCfg (some .revAll) initS [] [] [] [] [] []
          ((splitParity p w).1.reverse ++ sd) smBak [] ((splitParity p w).2.reverse ++ saccBak))
  | [], p, sd, smBak, saccBak => by
    change sqTM.step (mkCfg (some .split) (st p false false) [] [] [] [] [] [] sd smBak [] saccBak) = _
    exact step_split_nil p sd smBak saccBak
  | b :: w, false, sd, smBak, saccBak => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[w.length + 1]
      (sqTM.step (mkCfg (some .split) (st false false false) (Sum.inr b :: w.map Sum.inr)
        [] [] [] [] [] sd smBak [] saccBak)) = _
    rw [step_split_inr_false]
    simpa [splitParity, List.reverse_cons, List.append_assoc] using
      eval_split_inr w true (b :: sd) smBak saccBak
  | b :: w, true, sd, smBak, saccBak => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[w.length + 1]
      (sqTM.step (mkCfg (some .split) (st true false false) (Sum.inr b :: w.map Sum.inr)
        [] [] [] [] [] sd smBak [] saccBak)) = _
    rw [step_split_inr_true]
    simpa [splitParity, List.reverse_cons, List.append_assoc] using
      eval_split_inr w false sd smBak (b :: saccBak)

/-! ### Phase 2: `revAll` -/

private theorem step_revAll_nil (sx sb sm : List Bool) :
    sqTM.step (mkCfg (some .revAll) initS [] [] sx sb [] sm [] [] [] []) =
      some (mkCfg (some .dupToD) initS [] [] sx sb [] sm [] [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_revAll_nonnil (sx sb sm sd smBak saccBak : List Bool)
    (h : smBak ≠ [] ∨ sd ≠ [] ∨ saccBak ≠ []) :
    sqTM.step (mkCfg (some .revAll) initS [] [] sx sb [] sm sd smBak [] saccBak) =
      some (mkCfg (some .revAll) initS [] []
        (optCons smBak.head? sx) (optCons saccBak.head? sb) [] (optCons sd.head? sm)
        sd.tail smBak.tail [] saccBak.tail) := by
  rcases smBak with _ | ⟨a1, l1⟩ <;> rcases sd with _ | ⟨a2, l2⟩ <;>
    rcases saccBak with _ | ⟨a3, l3⟩
  · simp at h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_revAll :
    ∀ (n : ℕ) (sx sb sm sd smBak saccBak : List Bool),
      max (max smBak.length sd.length) saccBak.length = n →
      (flip bind sqTM.step)^[n + 1]
        (some (mkCfg (some .revAll) initS [] [] sx sb [] sm sd smBak [] saccBak)) =
        some (mkCfg (some .dupToD) initS [] []
          (smBak.reverse ++ sx) (saccBak.reverse ++ sb) [] (sd.reverse ++ sm) [] [] [] [])
  | 0, sx, sb, sm, sd, smBak, saccBak, h => by
    have h1 : smBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : sd = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h3 : saccBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2; subst h3
    change sqTM.step (mkCfg (some .revAll) initS [] [] sx sb [] sm [] [] [] []) = _
    exact step_revAll_nil sx sb sm
  | n + 1, sx, sb, sm, sd, smBak, saccBak, h => by
    have hne : smBak ≠ [] ∨ sd ≠ [] ∨ saccBak ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rcases hc with ⟨rfl, rfl, rfl⟩
      simp at h
    have htail : max (max smBak.tail.length sd.tail.length) saccBak.tail.length = n := by
      simp only [List.length_tail]; omega
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[n + 1]
      (sqTM.step (mkCfg (some .revAll) initS [] [] sx sb [] sm sd smBak [] saccBak)) = _
    rw [step_revAll_nonnil sx sb sm sd smBak saccBak hne]
    rw [eval_revAll n _ _ _ _ _ _ htail]
    rw [reverse_tail_append_optCons, reverse_tail_append_optCons, reverse_tail_append_optCons]

/-! ### Phase 3: Squaring subroutine (`dupToD`, `revM`, `sqStep`, `sqAdd`, `sqRev`, `cleanM`) -/

private theorem step_dupToD_nil (phase : Bool) (sx sb su sd smBak : List Bool) :
    sqTM.step (mkCfg (some .dupToD) (st phase false false) [] [] sx sb su [] sd smBak [] []) =
      some (mkCfg (some .revM) (st phase false false) [] [] sx sb su [] sd smBak [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_dupToD_cons (phase : Bool) (sx sb su : List Bool) (b : Bool)
    (sm sd smBak : List Bool) :
    sqTM.step (mkCfg (some .dupToD) (st phase false false)
        [] [] sx sb su (b :: sm) sd smBak [] []) =
      some (mkCfg (some .dupToD) (st phase false false)
        [] [] sx sb su sm (b :: sd) (b :: smBak) [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_dupToD (phase : Bool) (sx sb su : List Bool) :
    ∀ (sm sd smBak : List Bool),
      (flip bind sqTM.step)^[sm.length + 1]
        (some (mkCfg (some .dupToD) (st phase false false) [] [] sx sb su sm sd smBak [] [])) =
        some (mkCfg (some .revM) (st phase false false)
          [] [] sx sb su [] (sm.reverse ++ sd) (sm.reverse ++ smBak) [] [])
  | [], sd, smBak => by
    change sqTM.step (mkCfg (some .dupToD) (st phase false false) [] [] sx sb su [] sd smBak [] []) = _
    exact step_dupToD_nil phase sx sb su sd smBak
  | b :: sm, sd, smBak => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[sm.length + 1]
      (sqTM.step (mkCfg (some .dupToD) (st phase false false)
        [] [] sx sb su (b :: sm) sd smBak [] [])) = _
    rw [step_dupToD_cons]
    simpa [List.reverse_cons, List.append_assoc] using
      eval_dupToD phase sx sb su sm (b :: sd) (b :: smBak)

private theorem step_revM_nil (phase : Bool) (sx sb su sm sd : List Bool) :
    sqTM.step (mkCfg (some .revM) (st phase false false) [] [] sx sb su sm sd [] [] []) =
      some (mkCfg (some .sqStep) (st phase false false) [] [] sx sb su sm sd [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_revM_cons (phase : Bool) (sx sb su sm sd : List Bool) (b : Bool)
    (smBak : List Bool) :
    sqTM.step (mkCfg (some .revM) (st phase false false)
        [] [] sx sb su sm sd (b :: smBak) [] []) =
      some (mkCfg (some .revM) (st phase false false)
        [] [] sx sb su (b :: sm) sd smBak [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_revM (phase : Bool) (sx sb su sd : List Bool) :
    ∀ (smBak sm : List Bool),
      (flip bind sqTM.step)^[smBak.length + 1]
        (some (mkCfg (some .revM) (st phase false false) [] [] sx sb su sm sd smBak [] [])) =
        some (mkCfg (some .sqStep) (st phase false false)
          [] [] sx sb su (smBak.reverse ++ sm) sd [] [] [])
  | [], sm => by
    change sqTM.step (mkCfg (some .revM) (st phase false false) [] [] sx sb su sm sd [] [] []) = _
    exact step_revM_nil phase sx sb su sm sd
  | b :: smBak, sm => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[smBak.length + 1]
      (sqTM.step (mkCfg (some .revM) (st phase false false)
        [] [] sx sb su sm sd (b :: smBak) [] [])) = _
    rw [step_revM_cons]
    simpa [List.reverse_cons, List.append_assoc] using
      eval_revM phase sx sb su sd smBak (b :: sm)

private theorem step_sqStep_nil (phase : Bool) (sx sb su sm sacc : List Bool) :
    sqTM.step (mkCfg (some .sqStep) (st phase false false) [] [] sx sb su sm [] [] sacc []) =
      some (mkCfg (some .cleanM) (st phase false false) [] [] sx sb su sm [] [] sacc []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqStep_false (phase : Bool) (sx sb su sm ds sacc : List Bool) :
    sqTM.step (mkCfg (some .sqStep) (st phase false false)
        [] [] sx sb su sm (false :: ds) [] sacc []) =
      some (mkCfg (some .sqStep) (st phase false false)
        [] [] sx sb su sm ds [] (false :: sacc) []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqStep_true (phase : Bool) (sx sb su sm ds sacc : List Bool) :
    sqTM.step (mkCfg (some .sqStep) (st phase false false)
        [] [] sx sb su sm (true :: ds) [] sacc []) =
      some (mkCfg (some .sqAdd) (st phase false false)
        [] [] sx sb su sm ds [] (false :: sacc) []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqAdd_nil_false (phase : Bool) (sx sb su ds mb ab : List Bool) :
    sqTM.step (mkCfg (some .sqAdd) (st phase false false) [] [] sx sb su [] ds mb [] ab) =
      some (mkCfg (some .sqRev) (st phase false false) [] [] sx sb su [] ds mb [] ab) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqAdd_nil_true (phase : Bool) (sx sb su ds mb ab : List Bool) :
    sqTM.step (mkCfg (some .sqAdd) (st phase true false) [] [] sx sb su [] ds mb [] ab) =
      some (mkCfg (some .sqAdd) (st phase false false) [] [] sx sb su [] ds mb [] (true :: ab)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqAdd_cons_nil (phase c : Bool) (sx sb su ds mb ab : List Bool)
    (a : Bool) (as : List Bool) :
    sqTM.step (mkCfg (some .sqAdd) (st phase c false) [] [] sx sb su (a :: as) ds mb [] ab) =
      some (mkCfg (some .sqAdd) (st phase (addCarry a false c) false)
        [] [] sx sb su as ds (a :: mb) [] (addBit a false c :: ab)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqAdd_nil_cons (phase c : Bool) (sx sb su ds mb ab : List Bool)
    (b : Bool) (bs : List Bool) :
    sqTM.step (mkCfg (some .sqAdd) (st phase c false) [] [] sx sb su [] ds mb (b :: bs) ab) =
      some (mkCfg (some .sqAdd) (st phase (addCarry false b c) false)
        [] [] sx sb su [] ds mb bs (addBit false b c :: ab)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqAdd_cons_cons (phase c : Bool) (sx sb su ds mb ab : List Bool)
    (a b : Bool) (as bs : List Bool) :
    sqTM.step (mkCfg (some .sqAdd) (st phase c false)
        [] [] sx sb su (a :: as) ds mb (b :: bs) ab) =
      some (mkCfg (some .sqAdd) (st phase (addCarry a b c) false)
        [] [] sx sb su as ds (a :: mb) bs (addBit a b c :: ab)) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_sqAdd (phase : Bool) (sx sb su ds : List Bool) :
    ∀ (n : ℕ) (as bs mb ab : List Bool) (c : Bool),
      max as.length bs.length = n →
      (flip bind sqTM.step)^[(addBits as bs c).length + 1]
        (some (mkCfg (some .sqAdd) (st phase c false) [] [] sx sb su as ds mb bs ab)) =
        some (mkCfg (some .sqRev) (st phase false false)
          [] [] sx sb su [] ds (as.reverse ++ mb) [] ((addBits as bs c).reverse ++ ab))
  | 0, as, bs, mb, ab, c, h => by
    have ha : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha; subst hb
    cases c with
    | false =>
      simp only [addBits, List.length_nil, List.reverse_nil, List.nil_append]
      exact step_sqAdd_nil_false phase sx sb su ds mb ab
    | true =>
      simp only [addBits, List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append]
      rw [Function.iterate_succ_apply]
      change (flip bind sqTM.step)^[1]
        (sqTM.step (mkCfg (some .sqAdd) (st phase true false) [] [] sx sb su [] ds mb [] ab)) = _
      rw [step_sqAdd_nil_true]
      exact step_sqAdd_nil_false phase sx sb su ds mb (true :: ab)
  | n + 1, [], [], mb, ab, c, h => by
    simp at h
  | n + 1, a :: as, [], mb, ab, c, h => by
    have htail : max as.length ([] : List Bool).length = n := by simp at h ⊢; omega
    simp only [addBits, List.length_cons]
    rw [Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[(addBits as [] (addCarry a false c)).length + 1]
      (sqTM.step (mkCfg (some .sqAdd) (st phase c false) [] [] sx sb su (a :: as) ds mb [] ab)) = _
    rw [step_sqAdd_cons_nil]
    simpa [List.reverse_cons, List.append_assoc] using
      eval_sqAdd phase sx sb su ds n as [] (a :: mb) (addBit a false c :: ab) (addCarry a false c) htail
  | n + 1, [], b :: bs, mb, ab, c, h => by
    have htail : max ([] : List Bool).length bs.length = n := by simp at h ⊢; omega
    simp only [addBits, List.length_cons]
    rw [Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[(addBits [] bs (addCarry false b c)).length + 1]
      (sqTM.step (mkCfg (some .sqAdd) (st phase c false) [] [] sx sb su [] ds mb (b :: bs) ab)) = _
    rw [step_sqAdd_nil_cons]
    simpa [List.reverse_cons, List.append_assoc] using
      eval_sqAdd phase sx sb su ds n [] bs mb (addBit false b c :: ab) (addCarry false b c) htail
  | n + 1, a :: as, b :: bs, mb, ab, c, h => by
    have htail : max as.length bs.length = n := by simp at h ⊢; omega
    simp only [addBits, List.length_cons]
    rw [Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[(addBits as bs (addCarry a b c)).length + 1]
      (sqTM.step (mkCfg (some .sqAdd) (st phase c false)
        [] [] sx sb su (a :: as) ds mb (b :: bs) ab)) = _
    rw [step_sqAdd_cons_cons]
    simpa [List.reverse_cons, List.append_assoc] using
      eval_sqAdd phase sx sb su ds n as bs (a :: mb) (addBit a b c :: ab) (addCarry a b c) htail

private theorem step_sqRev_nil (phase : Bool) (sx sb su sm ds sacc : List Bool) :
    sqTM.step (mkCfg (some .sqRev) (st phase false false) [] [] sx sb su sm ds [] sacc []) =
      some (mkCfg (some .sqStep) (st phase false false) [] [] sx sb su sm ds [] sacc []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_sqRev_nonnil (phase : Bool) (sx sb su sm ds smBak sacc saccBak : List Bool)
    (h : smBak ≠ [] ∨ saccBak ≠ []) :
    sqTM.step (mkCfg (some .sqRev) (st phase false false)
        [] [] sx sb su sm ds smBak sacc saccBak) =
      some (mkCfg (some .sqRev) (st phase false false) [] [] sx sb su
        (optCons smBak.head? sm) ds smBak.tail (optCons saccBak.head? sacc) saccBak.tail) := by
  rcases smBak with _ | ⟨a1, l1⟩ <;> rcases saccBak with _ | ⟨a2, l2⟩
  · simp at h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_sqRev (phase : Bool) (sx sb su ds : List Bool) :
    ∀ (n : ℕ) (sm smBak sacc saccBak : List Bool),
      max smBak.length saccBak.length = n →
      (flip bind sqTM.step)^[n + 1]
        (some (mkCfg (some .sqRev) (st phase false false)
          [] [] sx sb su sm ds smBak sacc saccBak)) =
        some (mkCfg (some .sqStep) (st phase false false)
          [] [] sx sb su (smBak.reverse ++ sm) ds [] (saccBak.reverse ++ sacc) [])
  | 0, sm, smBak, sacc, saccBak, h => by
    have h1 : smBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : saccBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2
    change sqTM.step (mkCfg (some .sqRev) (st phase false false) [] [] sx sb su sm ds [] sacc []) = _
    exact step_sqRev_nil phase sx sb su sm ds sacc
  | n + 1, sm, smBak, sacc, saccBak, h => by
    have hne : smBak ≠ [] ∨ saccBak ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rcases hc with ⟨rfl, rfl⟩
      simp at h
    have htail : max smBak.tail.length saccBak.tail.length = n := by
      simp only [List.length_tail]; omega
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[n + 1]
      (sqTM.step (mkCfg (some .sqRev) (st phase false false)
        [] [] sx sb su sm ds smBak sacc saccBak)) = _
    rw [step_sqRev_nonnil phase sx sb su sm ds smBak sacc saccBak hne]
    rw [eval_sqRev phase sx sb su ds n _ _ _ _ htail]
    rw [reverse_tail_append_optCons, reverse_tail_append_optCons]

private def sqLoopSteps (v : List Bool) : List Bool → List Bool → ℕ
  | [], _ => 1
  | false :: ds, acc => sqLoopSteps v ds (false :: acc) + 1
  | true :: ds, acc =>
    let next := addBits v (false :: acc) false
    sqLoopSteps v ds next + ((max v.length next.length + 1) + ((next.length + 1) + 1))

private theorem sqLoopSteps_le (v : List Bool) :
    ∀ (ds acc : List Bool),
      sqLoopSteps v ds acc ≤ ds.length * (2 * (max v.length acc.length + 2 * ds.length) + 3) + 1
  | [], acc => by simp [sqLoopSteps]
  | false :: ds, acc => by
    have ih := sqLoopSteps_le v ds (false :: acc)
    have hle : 2 * (max v.length (false :: acc).length + 2 * ds.length) + 3 ≤
        2 * (max v.length acc.length + 2 * (false :: ds).length) + 3 := by
      simp only [List.length_cons]; omega
    have hmul : ds.length * (2 * (max v.length (false :: acc).length + 2 * ds.length) + 3) ≤
        ds.length * (2 * (max v.length acc.length + 2 * (false :: ds).length) + 3) :=
      Nat.mul_le_mul_left _ hle
    have hsucc : (false :: ds).length * (2 * (max v.length acc.length + 2 * (false :: ds).length) + 3) =
        ds.length * (2 * (max v.length acc.length + 2 * (false :: ds).length) + 3) +
          (2 * (max v.length acc.length + 2 * (false :: ds).length) + 3) := by
      rw [List.length_cons, Nat.succ_mul]
    simp only [sqLoopSteps]
    omega
  | true :: ds, acc => by
    dsimp only [sqLoopSteps]
    set next := addBits v (false :: acc) false
    have ih := sqLoopSteps_le v ds next
    have hnext : next.length ≤ max v.length (false :: acc).length + 1 :=
      length_addBits v (false :: acc) false
    have hle : 2 * (max v.length next.length + 2 * ds.length) + 3 ≤
        2 * (max v.length acc.length + 2 * (true :: ds).length) + 3 := by
      simp only [List.length_cons] at hnext ⊢; omega
    have hmul : ds.length * (2 * (max v.length next.length + 2 * ds.length) + 3) ≤
        ds.length * (2 * (max v.length acc.length + 2 * (true :: ds).length) + 3) :=
      Nat.mul_le_mul_left _ hle
    have hsucc : (true :: ds).length * (2 * (max v.length acc.length + 2 * (true :: ds).length) + 3) =
        ds.length * (2 * (max v.length acc.length + 2 * (true :: ds).length) + 3) +
          (2 * (max v.length acc.length + 2 * (true :: ds).length) + 3) := by
      rw [List.length_cons, Nat.succ_mul]
    have hcur : (max v.length next.length + 1) + ((next.length + 1) + 1) ≤
        2 * (max v.length acc.length + 2 * (true :: ds).length) + 3 := by
      simp only [List.length_cons] at hnext ⊢; omega
    omega

private theorem eval_sqLoop (phase : Bool) (sx sb su v : List Bool) :
    ∀ (ds acc : List Bool),
      (flip bind sqTM.step)^[sqLoopSteps v ds acc]
        (some (mkCfg (some .sqStep) (st phase false false) [] [] sx sb su v ds [] acc [])) =
        some (mkCfg (some .cleanM) (st phase false false)
          [] [] sx sb su v [] [] (sqAcc v ds acc) [])
  | [], acc => by
    change sqTM.step (mkCfg (some .sqStep) (st phase false false) [] [] sx sb su v [] [] acc []) = _
    exact step_sqStep_nil phase sx sb su v acc
  | false :: ds, acc => by
    simp only [sqLoopSteps, sqAcc]
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[sqLoopSteps v ds (false :: acc)]
      (sqTM.step (mkCfg (some .sqStep) (st phase false false)
        [] [] sx sb su v (false :: ds) [] acc [])) = _
    rw [step_sqStep_false]
    exact eval_sqLoop phase sx sb su v ds (false :: acc)
  | true :: ds, acc => by
    set next := addBits v (false :: acc) false
    simp only [sqLoopSteps, sqAcc]
    rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[sqLoopSteps v ds next]
      ((flip bind sqTM.step)^[max v.length next.length + 1]
        ((flip bind sqTM.step)^[next.length + 1]
          (sqTM.step (mkCfg (some .sqStep) (st phase false false)
            [] [] sx sb su v (true :: ds) [] acc [])))) = _
    rw [step_sqStep_true]
    have hadd := eval_sqAdd phase sx sb su ds (max v.length (false :: acc).length)
      v (false :: acc) [] [] false rfl
    simp only [List.append_nil] at hadd
    rw [hadd]
    have hrev := eval_sqRev phase sx sb su ds (max v.length next.length)
      [] v.reverse [] next.reverse (by simp)
    simp only [List.reverse_reverse, List.append_nil] at hrev
    rw [hrev]
    exact eval_sqLoop phase sx sb su v ds next

private theorem step_cleanM_cons (phase : Bool) (sx sb su : List Bool) (b : Bool)
    (sm sacc : List Bool) :
    sqTM.step (mkCfg (some .cleanM) (st phase false false) [] [] sx sb su (b :: sm) [] [] sacc []) =
      some (mkCfg (some .cleanM) (st phase false false) [] [] sx sb su sm [] [] sacc []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cleanM_nil_false (sx sb su sacc : List Bool) :
    sqTM.step (mkCfg (some .cleanM) (st false false false) [] [] sx sb su [] [] [] sacc []) =
      some (mkCfg (some .move1) initS [] [] sx sb su [] [] [] sacc []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cleanM_nil_true (sx sb su sacc : List Bool) :
    sqTM.step (mkCfg (some .cleanM) (st true false false) [] [] sx sb su [] [] [] sacc []) =
      some (mkCfg (some .cmp) (st false false true) [] [] sx sb su [] [] [] sacc []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_cleanM (phase : Bool) (sx sb su sacc : List Bool) :
    ∀ (sm : List Bool),
      (flip bind sqTM.step)^[sm.length + 1]
        (some (mkCfg (some .cleanM) (st phase false false) [] [] sx sb su sm [] [] sacc [])) =
        some (mkCfg (some (if phase then .cmp else .move1))
          (if phase then st false false true else initS)
          [] [] sx sb su [] [] [] sacc [])
  | [] => by
    cases phase with
    | false =>
      change sqTM.step (mkCfg (some .cleanM) (st false false false) [] [] sx sb su [] [] [] sacc []) = _
      exact step_cleanM_nil_false sx sb su sacc
    | true =>
      change sqTM.step (mkCfg (some .cleanM) (st true false false) [] [] sx sb su [] [] [] sacc []) = _
      exact step_cleanM_nil_true sx sb su sacc
  | b :: sm => by
    rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[sm.length + 1]
      (sqTM.step (mkCfg (some .cleanM) (st phase false false)
        [] [] sx sb su (b :: sm) [] [] sacc [])) = _
    rw [step_cleanM_cons]
    exact eval_cleanM phase sx sb su sacc sm

private theorem step_trans {α : Type} {f : α → α} {m n : ℕ} {a b c : α}
    (h1 : f^[n] a = b) (h2 : f^[m] b = c) : f^[m + n] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

private def sqTotalSteps (v : List Bool) : ℕ :=
  (v.length + 1) + (sqLoopSteps v v.reverse [] + ((v.length + 1) + (v.length + 1)))

private theorem sqTotalSteps_le (v : List Bool) :
    sqTotalSteps v ≤ 6 * v.length ^ 2 + 6 * v.length + 4 := by
  have h := sqLoopSteps_le v v.reverse []
  simp only [List.length_reverse, List.length_nil] at h
  have hmax : max v.length 0 = v.length := by omega
  rw [hmax] at h
  have hring : v.length * (2 * (v.length + 2 * v.length) + 3) =
      6 * v.length ^ 2 + 3 * v.length := by ring
  unfold sqTotalSteps
  omega

private theorem eval_square (phase : Bool) (sx sb su v : List Bool) :
    (flip bind sqTM.step)^[sqTotalSteps v]
      (some (mkCfg (some .dupToD) (st phase false false) [] [] sx sb su v [] [] [] [])) =
      some (mkCfg (some (if phase then .cmp else .move1))
        (if phase then st false false true else initS)
        [] [] sx sb su [] [] [] (sqAcc v v.reverse []) []) := by
  unfold sqTotalSteps
  have h1 := eval_dupToD phase sx sb su v [] []
  simp only [List.append_nil] at h1
  have h2 := eval_revM phase sx sb su v.reverse v.reverse []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have h3 := eval_sqLoop phase sx sb su v v.reverse []
  have h4 := eval_cleanM phase sx sb su (sqAcc v v.reverse []) v
  exact step_trans (step_trans (step_trans h1 h2) h3) h4

/-! ### Phase 4: `move1` and `move2` -/

private theorem step_move1_nil (sx smBak saccBak : List Bool) :
    sqTM.step (mkCfg (some .move1) initS [] [] sx [] [] [] [] smBak [] saccBak) =
      some (mkCfg (some .move2) initS [] [] sx [] [] [] [] smBak [] saccBak) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_move1_nonnil (sx sb smBak sacc saccBak : List Bool)
    (h : sb ≠ [] ∨ sacc ≠ []) :
    sqTM.step (mkCfg (some .move1) initS [] [] sx sb [] [] [] smBak sacc saccBak) =
      some (mkCfg (some .move1) initS [] [] sx sb.tail [] [] []
        (optCons sb.head? smBak) sacc.tail (optCons sacc.head? saccBak)) := by
  rcases sb with _ | ⟨a1, l1⟩ <;> rcases sacc with _ | ⟨a2, l2⟩
  · simp at h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_move1 (sx : List Bool) :
    ∀ (n : ℕ) (sb smBak sacc saccBak : List Bool),
      max sb.length sacc.length = n →
      (flip bind sqTM.step)^[n + 1]
        (some (mkCfg (some .move1) initS [] [] sx sb [] [] [] smBak sacc saccBak)) =
        some (mkCfg (some .move2) initS [] [] sx [] [] [] []
          (sb.reverse ++ smBak) [] (sacc.reverse ++ saccBak))
  | 0, sb, smBak, sacc, saccBak, h => by
    have h1 : sb = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : sacc = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2
    change sqTM.step (mkCfg (some .move1) initS [] [] sx [] [] [] [] smBak [] saccBak) = _
    exact step_move1_nil sx smBak saccBak
  | n + 1, sb, smBak, sacc, saccBak, h => by
    have hne : sb ≠ [] ∨ sacc ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rcases hc with ⟨rfl, rfl⟩
      simp at h
    have htail : max sb.tail.length sacc.tail.length = n := by
      simp only [List.length_tail]; omega
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[n + 1]
      (sqTM.step (mkCfg (some .move1) initS [] [] sx sb [] [] [] smBak sacc saccBak)) = _
    rw [step_move1_nonnil sx sb smBak sacc saccBak hne]
    rw [eval_move1 sx n _ _ _ _ htail]
    rw [reverse_tail_append_optCons, reverse_tail_append_optCons]

private theorem step_move2_nil (sx su sm : List Bool) :
    sqTM.step (mkCfg (some .move2) initS [] [] sx [] su sm [] [] [] []) =
      some (mkCfg (some .dupToD) (st true false false) [] [] sx [] su sm [] [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_move2_nonnil (sx su sm smBak saccBak : List Bool)
    (h : smBak ≠ [] ∨ saccBak ≠ []) :
    sqTM.step (mkCfg (some .move2) initS [] [] sx [] su sm [] smBak [] saccBak) =
      some (mkCfg (some .move2) initS [] [] sx []
        (optCons saccBak.head? su) (optCons smBak.head? sm) [] smBak.tail [] saccBak.tail) := by
  rcases smBak with _ | ⟨a1, l1⟩ <;> rcases saccBak with _ | ⟨a2, l2⟩
  · simp at h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem eval_move2 (sx : List Bool) :
    ∀ (n : ℕ) (su sm smBak saccBak : List Bool),
      max smBak.length saccBak.length = n →
      (flip bind sqTM.step)^[n + 1]
        (some (mkCfg (some .move2) initS [] [] sx [] su sm [] smBak [] saccBak)) =
        some (mkCfg (some .dupToD) (st true false false) [] [] sx []
          (saccBak.reverse ++ su) (smBak.reverse ++ sm) [] [] [] [])
  | 0, su, sm, smBak, saccBak, h => by
    have h1 : smBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : saccBak = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2
    change sqTM.step (mkCfg (some .move2) initS [] [] sx [] su sm [] [] [] []) = _
    exact step_move2_nil sx su sm
  | n + 1, su, sm, smBak, saccBak, h => by
    have hne : smBak ≠ [] ∨ saccBak ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rcases hc with ⟨rfl, rfl⟩
      simp at h
    have htail : max smBak.tail.length saccBak.tail.length = n := by
      simp only [List.length_tail]; omega
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[n + 1]
      (sqTM.step (mkCfg (some .move2) initS [] [] sx [] su sm [] smBak [] saccBak)) = _
    rw [step_move2_nonnil sx su sm smBak saccBak hne]
    rw [eval_move2 sx n _ _ _ _ htail]
    rw [reverse_tail_append_optCons, reverse_tail_append_optCons]

/-! ### Phase 5: `cmp` (`val u + val v = val x`) -/

private theorem step_cmp_nil (c ok : Bool) :
    sqTM.step (mkCfg (some .cmp) (st false c ok) [] [] [] [] [] [] [] [] [] []) =
      some (mkCfg none initS [] [ok && !c] [] [] [] [] [] [] [] []) := by
  apply congrArg some
  exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem step_cmp_nonnil (c ok : Bool) (sx su sacc : List Bool)
    (h : su ≠ [] ∨ sacc ≠ [] ∨ sx ≠ []) :
    sqTM.step (mkCfg (some .cmp) (st false c ok) [] [] sx [] su [] [] [] sacc []) =
      some (mkCfg (some .cmp)
        (st false
          (addCarry (su.head?.getD false) (sacc.head?.getD false) c)
          (ok && (addBit (su.head?.getD false) (sacc.head?.getD false) c == sx.head?.getD false)))
        [] [] sx.tail [] su.tail [] [] [] sacc.tail []) := by
  rcases su with _ | ⟨a1, l1⟩ <;> rcases sacc with _ | ⟨a2, l2⟩ <;> rcases sx with _ | ⟨a3, l3⟩
  · simp at h
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)
  · apply congrArg some; exact cfg_ext rfl rfl (fun k => by cases k <;> rfl)

private theorem cmp_flag_step (ok c : Bool) (u v x : List Bool) :
    ((ok && (addBit (u.head?.getD false) (v.head?.getD false) c == x.head?.getD false)) &&
      decide (val u.tail + val v.tail +
        (addCarry (u.head?.getD false) (v.head?.getD false) c).toNat = val x.tail)) =
      (ok && decide (val u + val v + c.toNat = val x)) := by
  rw [Bool.and_assoc]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rw [val_eq_head_add_two_tail u, val_eq_head_add_two_tail v, val_eq_head_add_two_tail x]
  have h := addBit_addCarry_spec (u.head?.getD false) (v.head?.getD false) c
  generalize hsb : addBit (u.head?.getD false) (v.head?.getD false) c = sb at h ⊢
  cases sb <;> cases (x.head?.getD false) <;>
    simp only [Bool.toNat_false, Bool.toNat_true] at h ⊢ <;>
    constructor
  · rintro ⟨_, hiff⟩; omega
  · intro hiff; exact ⟨trivial, by omega⟩
  · rintro ⟨habs, _⟩; cases habs
  · intro hiff; omega
  · rintro ⟨habs, _⟩; cases habs
  · intro hiff; omega
  · rintro ⟨_, hiff⟩; omega
  · intro hiff; exact ⟨trivial, by omega⟩

private theorem eval_cmp :
    ∀ (n : ℕ) (c ok : Bool) (sx su sacc : List Bool),
      max (max su.length sacc.length) sx.length = n →
      (flip bind sqTM.step)^[n + 1]
        (some (mkCfg (some .cmp) (st false c ok) [] [] sx [] su [] [] [] sacc [])) =
        some (mkCfg none initS [] [ok && decide (val su + val sacc + c.toNat = val sx)]
          [] [] [] [] [] [] [] [])
  | 0, c, ok, sx, su, sacc, h => by
    have h1 : su = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : sacc = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h3 : sx = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2; subst h3
    change sqTM.step (mkCfg (some .cmp) (st false c ok) [] [] [] [] [] [] [] [] [] []) = _
    rw [step_cmp_nil]
    cases c <;> simp [val_nil]
  | n + 1, c, ok, sx, su, sacc, h => by
    have hne : su ≠ [] ∨ sacc ≠ [] ∨ sx ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rcases hc with ⟨rfl, rfl, rfl⟩
      simp at h
    have htail : max (max su.tail.length sacc.tail.length) sx.tail.length = n := by
      simp only [List.length_tail]; omega
    rw [Function.iterate_succ_apply]
    change (flip bind sqTM.step)^[n + 1]
      (sqTM.step (mkCfg (some .cmp) (st false c ok) [] [] sx [] su [] [] [] sacc [])) = _
    rw [step_cmp_nonnil c ok sx su sacc hne]
    rw [eval_cmp n _ _ _ _ _ htail]
    rw [cmp_flag_step]

/-! ### Full machine run and polynomial-time witness -/

private def totalSteps (p : List Bool × List Bool) : ℕ :=
  let x := p.1
  let a := (splitParity false p.2).1
  let b := (splitParity false p.2).2
  let u := sqAcc a a.reverse []
  let v := sqAcc b b.reverse []
  (max (max u.length v.length) x.length + 1) +
    (sqTotalSteps b +
      ((max b.length u.length + 1) +
        ((max b.length u.length + 1) +
          (sqTotalSteps a +
            ((max (max x.length a.length) b.length + 1) +
              ((p.2.length + 1) + x.length))))))

private theorem encodePair_eq (p : List Bool × List Bool) :
    PvsNP.encodePair p = p.1.map Sum.inl ++ p.2.map Sum.inr := by
  rcases p with ⟨x, w⟩
  simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]

private noncomputable def verifierComputable :
    TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer verifier where
  tm := sqTM
  inputAlphabet := Equiv.refl (Bool ⊕ Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 12 * Polynomial.X ^ 2 + Polynomial.C 23 * Polynomial.X + Polynomial.C 13
  outputsFun p :=
    { steps := totalSteps p
      evals_in_steps := by
        rcases p with ⟨x, w⟩
        set a := (splitParity false w).1
        set b := (splitParity false w).2
        set u := sqAcc a a.reverse []
        set v := sqAcc b b.reverse []
        have hinit : initList sqTM (List.map (Equiv.refl (Bool ⊕ Bool)).invFun
            (PvsNP.encodePair (x, w))) =
            mkCfg (some .split) initS (x.map Sum.inl ++ w.map Sum.inr)
              [] [] [] [] [] [] [] [] [] := by
          apply cfg_ext
          · rfl
          · rfl
          · intro k
            cases k
            · change List.map id (PvsNP.encodePair (x, w)) = x.map Sum.inl ++ w.map Sum.inr
              rw [List.map_id, encodePair_eq]
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
        have hhalt : Option.map (haltList sqTM)
            (some (List.map (Equiv.refl Bool).invFun
              (PvsNP.encodeAnswer (verifier (x, w))))) =
            some (mkCfg none initS [] [verifier (x, w)] [] [] [] [] [] [] [] []) := by
          apply congrArg some
          apply cfg_ext
          · rfl
          · rfl
          · intro k
            cases k <;> rfl
        rw [hinit, hhalt]
        unfold totalSteps
        dsimp only
        have hsp1 := eval_split_inl x (w.map Sum.inr) []
        simp only [List.append_nil] at hsp1
        have hsp2 := eval_split_inr w false [] x.reverse []
        simp only [List.append_nil] at hsp2
        have hrev := eval_revAll (max (max x.length a.length) b.length)
          [] [] [] a.reverse x.reverse b.reverse (by simp)
        simp only [List.reverse_reverse, List.append_nil] at hrev
        have hsq1 := eval_square false x b [] a
        simp only [Bool.false_eq_true, ↓reduceIte] at hsq1
        have hm1 := eval_move1 x (max b.length u.length) b [] u [] rfl
        simp only [List.append_nil] at hm1
        have hm2 := eval_move2 x (max b.length u.length) [] [] b.reverse u.reverse (by simp)
        simp only [List.reverse_reverse, List.append_nil] at hm2
        have hsq2 := eval_square true x [] u b
        simp only [↓reduceIte] at hsq2
        have hcmp := eval_cmp (max (max u.length v.length) x.length) false true x u v rfl
        have hval : (true && decide (val u + val v + false.toNat = val x)) = verifier (x, w) := by
          simp only [verifier, Bool.true_and, Bool.toNat_false, add_zero, u, v, a, b,
            val_sqAcc_self]
        rw [hval] at hcmp
        exact step_trans
          (step_trans
            (step_trans
              (step_trans
                (step_trans
                  (step_trans
                    (step_trans hsp1 hsp2)
                    hrev)
                  hsq1)
                hm1)
              hm2)
            hsq2)
          hcmp
      steps_le_m := by
        rcases p with ⟨x, w⟩
        set a := (splitParity false w).1
        set b := (splitParity false w).2
        set u := sqAcc a a.reverse []
        set v := sqAcc b b.reverse []
        set L := (PvsNP.encodePair (x, w)).length
        have hL : L = x.length + w.length := by
          simp [L, encodePair_eq]
        have hab : a.length + b.length = w.length := splitParity_length false w
        have haL : a.length ≤ L := by omega
        have hbL : b.length ≤ L := by omega
        have ha2 : a.length ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left haL 2
        have hb2 : b.length ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hbL 2
        have hu : u.length ≤ 3 * a.length := length_sqAcc_self a
        have hv : v.length ≤ 3 * b.length := length_sqAcc_self b
        have hsqa : sqTotalSteps a ≤ 6 * a.length ^ 2 + 6 * a.length + 4 := sqTotalSteps_le a
        have hsqb : sqTotalSteps b ≤ 6 * b.length ^ 2 + 6 * b.length + 4 := sqTotalSteps_le b
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, totalSteps]
        change (max (max u.length v.length) x.length + 1) +
          (sqTotalSteps b +
            ((max b.length u.length + 1) +
              ((max b.length u.length + 1) +
                (sqTotalSteps a +
                  ((max (max x.length a.length) b.length + 1) +
                    ((w.length + 1) + x.length)))))) ≤ 12 * L ^ 2 + 23 * L + 13
        omega }

/-! ### Verifier correctness -/

private theorem verifier_iff (x : List Bool) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = val x) ↔
      ∃ w : List Bool, w.length ≤ (Polynomial.C 2 * Polynomial.X).eval x.length ∧
        verifier (x, w) = true := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, verifier,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab⟩
    have hxlt : val x < 2 ^ x.length := val_lt_two_pow x
    have ha_le_sq : a ≤ a ^ 2 := by
      rw [sq]
      exact Nat.le_mul_self a
    have hb_le_sq : b ≤ b ^ 2 := by
      rw [sq]
      exact Nat.le_mul_self b
    have halt : a < 2 ^ x.length := by omega
    have hblt : b < 2 ^ x.length := by omega
    let la := toBits x.length a
    let lb := toBits x.length b
    refine ⟨interleave la lb, ?_, ?_⟩
    · rw [interleave_length, toBits_length, toBits_length]
      omega
    · have hsp : splitParity false (interleave la lb) = (la, lb) :=
        splitParity_interleave la lb (by simp [la, lb, toBits_length])
      rw [hsp, val_toBits x.length a halt, val_toBits x.length b hblt]
      exact hab
  · rintro ⟨w, -, hw⟩
    exact ⟨val (splitParity false w).1, val (splitParity false w).2, hw⟩

theorem sum_two_squares_in_np :
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
      Language Bool) ∈ PvsNP.NP :=
  ⟨verifier, Polynomial.C 2 * Polynomial.X, ⟨verifierComputable⟩, fun x => verifier_iff x⟩

end PvsNP.Units.tl_lang_sum_two_squares_np

theorem PvsNP.Units.tl_lang_sum_two_squares_np :
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  exact PvsNP.Units.tl_lang_sum_two_squares_np.sum_two_squares_in_np
