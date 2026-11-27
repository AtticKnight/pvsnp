import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_poly_clock

namespace PvsNP.Units.m2_exp_clock_aux

open Turing

inductive K : Type
  | inp | aux | out
  deriving DecidableEq

instance : Fintype K where
  elems := { K.inp, K.aux, K.out }
  complete x := by cases x <;> simp

inductive Lab : Type
  | init | outer | dbl | move
  deriving DecidableEq

instance : Fintype Lab where
  elems := { Lab.init, Lab.outer, Lab.dbl, Lab.move }
  complete x := by cases x <;> simp

def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .init => .push .out (fun _ => true) (.goto (fun _ => .outer))
  | .outer => .pop .inp (fun _ o => o.isSome)
      (.branch (fun s => s)
        (.load (fun _ => false) (.goto (fun _ => .dbl)))
        (.load (fun _ => false) .halt))
  | .dbl => .pop .out (fun _ o => o.isSome)
      (.branch (fun s => s)
        (.load (fun _ => false)
          (.push .aux (fun _ => true) (.push .aux (fun _ => true) (.goto (fun _ => .dbl)))))
        (.load (fun _ => false) (.goto (fun _ => .move))))
  | .move => .pop .aux (fun _ o => o.isSome)
      (.branch (fun s => s)
        (.load (fun _ => false) (.push .out (fun _ => true) (.goto (fun _ => .move))))
        (.load (fun _ => false) (.goto (fun _ => .outer))))

def exp2TM : FinTM2 where
  K := K
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Lab
  main := .init
  σ := Bool
  initialState := false
  m := prog

abbrev ECfg : Type := TM2.Cfg (fun _ : K => Bool) Lab Bool

def stk (a b c : List Bool) : K → List Bool
  | .inp => a
  | .aux => b
  | .out => c

theorem stk_upd_inp (a a' b c : List Bool) :
    Function.update (stk a b c) .inp a' = stk a' b c := by
  funext k; cases k <;> rfl

theorem stk_upd_aux (a b b' c : List Bool) :
    Function.update (stk a b c) .aux b' = stk a b' c := by
  funext k; cases k <;> rfl

theorem stk_upd_out (a b c c' : List Bool) :
    Function.update (stk a b c) .out c' = stk a b c' := by
  funext k; cases k <;> rfl

theorem init_step (a : List Bool) :
    TM2.step prog (⟨some .init, false, stk a [] []⟩ : ECfg) =
      some ⟨some .outer, false, stk a [] [true]⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_out]
  rfl

theorem dbl_cons (a : List Bool) (n : ℕ) (x : Bool) (r : List Bool) :
    TM2.step prog (⟨some .dbl, false, stk a (List.replicate n true) (x :: r)⟩ : ECfg) =
      some ⟨some .dbl, false, stk a (List.replicate (n + 2) true) r⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_out]
  simp only [stk, List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
  rw [stk_upd_aux, stk_upd_aux]
  simp only [stk]
  rfl

theorem dbl_nil (a : List Bool) (n : ℕ) :
    TM2.step prog (⟨some .dbl, false, stk a (List.replicate n true) []⟩ : ECfg) =
      some ⟨some .move, false, stk a (List.replicate n true) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_out]
  simp only [stk, List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]

theorem dbl_loop (a c : List Bool) (n : ℕ) :
    (flip bind (TM2.step prog))^[c.length + 1]
        (some (⟨some .dbl, false, stk a (List.replicate n true) c⟩ : ECfg)) =
      some ⟨some .move, false, stk a (List.replicate (n + 2 * c.length) true) []⟩ := by
  induction c generalizing n with
  | nil => exact dbl_nil a n
  | cons x r ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog)
        (some (⟨some .dbl, false, stk a (List.replicate n true) (x :: r)⟩ : ECfg)) =
        some ⟨some .dbl, false, stk a (List.replicate (n + 2) true) r⟩ := dbl_cons a n x r
    rw [e, ih (n + 2)]
    have hlen : (n + 2) + 2 * r.length = n + 2 * (r.length + 1) := by omega
    rw [hlen]

theorem move_cons (a : List Bool) (x : Bool) (r : List Bool) (n : ℕ) :
    TM2.step prog (⟨some .move, false, stk a (x :: r) (List.replicate n true)⟩ : ECfg) =
      some ⟨some .move, false, stk a r (List.replicate (n + 1) true)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_aux]
  simp only [stk, List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
  rw [stk_upd_out]
  rfl

theorem move_nil (a : List Bool) (n : ℕ) :
    TM2.step prog (⟨some .move, false, stk a [] (List.replicate n true)⟩ : ECfg) =
      some ⟨some .outer, false, stk a [] (List.replicate n true)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_aux]
  simp only [stk, List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]

theorem move_loop (a b : List Bool) (n : ℕ) :
    (flip bind (TM2.step prog))^[b.length + 1]
        (some (⟨some .move, false, stk a b (List.replicate n true)⟩ : ECfg)) =
      some ⟨some .outer, false, stk a [] (List.replicate (n + b.length) true)⟩ := by
  induction b generalizing n with
  | nil => exact move_nil a n
  | cons x r ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog)
        (some (⟨some .move, false, stk a (x :: r) (List.replicate n true)⟩ : ECfg)) =
        some ⟨some .move, false, stk a r (List.replicate (n + 1) true)⟩ := move_cons a x r n
    rw [e, ih (n + 1)]
    have hlen : (n + 1) + r.length = n + (r.length + 1) := by omega
    rw [hlen]

theorem outer_cons (x : Bool) (a' c : List Bool) :
    TM2.step prog (⟨some .outer, false, stk (x :: a') [] c⟩ : ECfg) =
      some ⟨some .dbl, false, stk a' [] c⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_inp]
  simp only [stk, List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]

theorem outer_nil (m : ℕ) :
    TM2.step prog (⟨some .outer, false, stk [] [] (List.replicate m true)⟩ : ECfg) =
      some ⟨none, false, stk [] [] (List.replicate m true)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [stk_upd_inp]
  simp only [stk, List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]

theorem outer_step (x : Bool) (a' : List Bool) (m : ℕ) :
    (flip bind (TM2.step prog))^[3 * m + 3]
        (some (⟨some .outer, false, stk (x :: a') [] (List.replicate m true)⟩ : ECfg)) =
      some ⟨some .outer, false, stk a' [] (List.replicate (2 * m) true)⟩ := by
  have h1 : flip bind (TM2.step prog)
      (some (⟨some .outer, false, stk (x :: a') [] (List.replicate m true)⟩ : ECfg)) =
      some ⟨some .dbl, false, stk a' [] (List.replicate m true)⟩ :=
    outer_cons x a' (List.replicate m true)
  have h2 := dbl_loop a' (List.replicate m true) 0
  simp only [List.length_replicate, Nat.zero_add, List.replicate_zero] at h2
  have h3 := move_loop a' (List.replicate (2 * m) true) 0
  simp only [List.length_replicate, Nat.zero_add, List.replicate_zero] at h3
  calc (flip bind (TM2.step prog))^[3 * m + 3]
        (some (⟨some .outer, false, stk (x :: a') [] (List.replicate m true)⟩ : ECfg))
      = (flip bind (TM2.step prog))^[2 * m + 1]
          ((flip bind (TM2.step prog))^[m + 1]
            (flip bind (TM2.step prog)
              (some (⟨some .outer, false, stk (x :: a') [] (List.replicate m true)⟩ : ECfg)))) := by
        rw [show 3 * m + 3 = (2 * m + 1) + ((m + 1) + 1) by omega,
          Function.iterate_add_apply,
          Function.iterate_add_apply (f := flip bind (TM2.step prog)) (m + 1) 1,
          Function.iterate_one]
    _ = some ⟨some .outer, false, stk a' [] (List.replicate (2 * m) true)⟩ := by
        rw [h1, h2, h3]

theorem outer_run (a : List Bool) (m : ℕ) (hm : 1 ≤ m) :
    ∃ s, s ≤ 7 * m * 2 ^ a.length - 6 * m ∧
      (flip bind (TM2.step prog))^[s]
          (some (⟨some .outer, false, stk a [] (List.replicate m true)⟩ : ECfg)) =
        some ⟨none, false, stk [] [] (List.replicate (m * 2 ^ a.length) true)⟩ := by
  induction a generalizing m with
  | nil =>
    refine ⟨1, by simp only [List.length_nil, pow_zero, Nat.mul_one]; omega, ?_⟩
    rw [Function.iterate_one, List.length_nil, pow_zero, Nat.mul_one]
    exact outer_nil m
  | cons x a' ih =>
    obtain ⟨s', hs', hr'⟩ := ih (2 * m) (by omega)
    refine ⟨s' + (3 * m + 3), ?_, ?_⟩
    · have hpow : 1 ≤ 2 ^ a'.length := Nat.one_le_two_pow
      have hm1 : 6 * m ≤ 7 * m * 2 ^ a'.length := by nlinarith
      have h7 : 7 * (2 * m) * 2 ^ a'.length = 2 * (7 * m * 2 ^ a'.length) := by ring
      have heq : 7 * m * 2 ^ (x :: a').length = 2 * (7 * m * 2 ^ a'.length) := by
        simp only [List.length_cons, pow_succ]; ring
      omega
    · rw [Function.iterate_add_apply, outer_step x a' m, hr']
      have heq : 2 * m * 2 ^ a'.length = m * 2 ^ (x :: a').length := by
        simp only [List.length_cons, pow_succ]; ring
      rw [heq]

theorem initList_exp2 (a : List Bool) :
    initList exp2TM a = (⟨some .init, false, stk a [] []⟩ : ECfg) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_exp2 (c : List Bool) :
    haltList exp2TM c = (⟨none, false, stk [] [] c⟩ : ECfg) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

theorem exp2_run (a : List Bool) :
    ∃ s, s ≤ 7 * 2 ^ a.length ∧
      (flip bind (TM2.step prog))^[s] (some (initList exp2TM a)) =
        some (haltList exp2TM (List.replicate (2 ^ a.length) true)) := by
  obtain ⟨s, hs, hr⟩ := outer_run a 1 (le_refl 1)
  have hpow : 1 ≤ 2 ^ a.length := Nat.one_le_two_pow
  refine ⟨s + 1, by omega, ?_⟩
  rw [initList_exp2, show haltList exp2TM (List.replicate (2 ^ a.length) true) =
      (⟨none, false, stk [] [] (List.replicate (2 ^ a.length) true)⟩ : ECfg) from haltList_exp2 _,
    Function.iterate_add_apply, Function.iterate_one]
  have h1 : flip bind (TM2.step prog) (some (⟨some .init, false, stk a [] []⟩ : ECfg)) =
      some ⟨some .outer, false, stk a [] (List.replicate 1 true)⟩ := init_step a
  rw [h1]
  rw [Nat.one_mul] at hr
  exact hr

theorem pow_le_mul_two_pow (d : ℕ) : ∃ C : ℕ, ∀ n : ℕ, n ^ d ≤ C * 2 ^ n := by
  refine ⟨max (2 ^ d * d.factorial) ((2 * d) ^ d), fun n => ?_⟩
  by_cases hn : n < 2 * d
  · calc n ^ d ≤ (2 * d) ^ d := Nat.pow_le_pow_left hn.le d
      _ ≤ max (2 ^ d * d.factorial) ((2 * d) ^ d) := le_max_right _ _
      _ ≤ max (2 ^ d * d.factorial) ((2 * d) ^ d) * 2 ^ n :=
          Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
  · have hge : 2 * d ≤ n := le_of_not_gt hn
    have hdesc : n ^ d ≤ 2 ^ d * n.descFactorial d := by
      rw [Nat.descFactorial_eq_prod_range]
      have h1 : n ^ d = ∏ _i ∈ Finset.range d, n := by simp
      have h2 : 2 ^ d = ∏ _i ∈ Finset.range d, 2 := by simp
      rw [h1, h2, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod fun i hi => ?_
      have hi' : i < d := Finset.mem_range.mp hi
      omega
    have hch : n.descFactorial d ≤ d.factorial * 2 ^ n := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      refine Nat.mul_le_mul_left _ ?_
      have hle : n.choose d ≤ ∑ k ∈ Finset.range (n + 1), n.choose k := by
        by_cases hd : d < n + 1
        · exact Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr hd)
        · rw [Nat.choose_eq_zero_of_lt (by omega)]
          exact Nat.zero_le _
      rwa [Nat.sum_range_choose] at hle
    calc n ^ d ≤ 2 ^ d * n.descFactorial d := hdesc
      _ ≤ 2 ^ d * (d.factorial * 2 ^ n) := Nat.mul_le_mul_left _ hch
      _ = (2 ^ d * d.factorial) * 2 ^ n := by ring
      _ ≤ max (2 ^ d * d.factorial) ((2 * d) ^ d) * 2 ^ n :=
          Nat.mul_le_mul_right _ (le_max_left _ _)

theorem poly_le_mul_two_pow (p : Polynomial ℕ) : ∃ C : ℕ, ∀ n : ℕ, p.eval n ≤ C * 2 ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C1, hC1⟩ := hp
    obtain ⟨C2, hC2⟩ := hq
    refine ⟨C1 + C2, fun n => ?_⟩
    rw [Polynomial.eval_add, Nat.add_mul]
    exact Nat.add_le_add (hC1 n) (hC2 n)
  | monomial d a =>
    obtain ⟨C, hC⟩ := pow_le_mul_two_pow d
    refine ⟨a * C, fun n => ?_⟩
    rw [Polynomial.eval_monomial, Nat.mul_assoc]
    exact Nat.mul_le_mul_left a (hC n)

end PvsNP.Units.m2_exp_clock_aux

theorem PvsNP.Units.m2_exp_clock : ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  classical
  have hpoly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length ^ k) true) := by
    have h := PvsNP.Units.m2_poly_clock (Polynomial.X ^ k)
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using h
  obtain ⟨c1⟩ := hpoly
  let φ : c1.tm.Γ c1.tm.k₁ →
      PvsNP.Units.m2_exp_clock_aux.exp2TM.Γ PvsNP.Units.m2_exp_clock_aux.exp2TM.k₀ :=
    fun x => c1.outputAlphabet x
  let d : Option (PvsNP.Units.m2_exp_clock_aux.exp2TM.Γ PvsNP.Units.m2_exp_clock_aux.exp2TM.k₀) :=
    some true
  have hd : d = none →
      IsEmpty (PvsNP.Units.m2_exp_clock_aux.exp2TM.Γ PvsNP.Units.m2_exp_clock_aux.exp2TM.k₀) := by
    intro h; simp [d] at h
  obtain ⟨C, hC⟩ := PvsNP.Units.m2_exp_clock_aux.poly_le_mul_two_pow c1.time
  have htime : ∀ n : ℕ, c1.time.eval n + (2 * (n ^ k) + 2) + 7 * 2 ^ (n ^ k) ≤
      (C + 9) * 2 ^ (n ^ k) + 2 := by
    intro n
    have h1 : n ≤ n ^ k := Nat.le_self_pow (by omega) n
    have h2 : 2 ^ n ≤ 2 ^ (n ^ k) := Nat.pow_le_pow_right (by omega) h1
    have h3 : c1.time.eval n ≤ C * 2 ^ (n ^ k) := (hC n).trans (Nat.mul_le_mul_left C h2)
    have h4 : n ^ k ≤ 2 ^ (n ^ k) := Nat.lt_two_pow_self.le
    rw [Nat.add_mul]
    omega
  have key : ∀ a : List Bool, ∃ n, n ≤ (C + 9) * 2 ^ (a.length ^ k) + 2 ∧
      (flip bind (Turing.TM2.step (PvsNP.Units.m2_poly_clock.prog c1.tm
          PvsNP.Units.m2_exp_clock_aux.exp2TM φ d)))^[n]
        (some (Turing.initList
          (PvsNP.Units.m2_poly_clock.comp c1.tm PvsNP.Units.m2_exp_clock_aux.exp2TM φ d)
          (List.map c1.inputAlphabet.invFun (PvsNP.encodeString a)))) =
        some (Turing.haltList
          (PvsNP.Units.m2_poly_clock.comp c1.tm PvsNP.Units.m2_exp_clock_aux.exp2TM φ d)
          (List.replicate (2 ^ (a.length ^ k)) true)) := by
    intro a
    have r1 := c1.outputsFun a
    have hφ : (List.map c1.outputAlphabet.invFun
        (PvsNP.encodeString (List.replicate (a.length ^ k) true))).map φ =
        List.replicate (a.length ^ k) true := by
      have henc_rep : PvsNP.encodeString (List.replicate (a.length ^ k) true) =
          List.replicate (a.length ^ k) true := rfl
      rw [henc_rep, List.map_map]
      refine (List.map_congr_left fun y _ => ?_).trans (List.map_id _)
      exact c1.outputAlphabet.right_inv y
    obtain ⟨s2, hs2, hr2⟩ := PvsNP.Units.m2_exp_clock_aux.exp2_run
      (List.replicate (a.length ^ k) true)
    rw [List.length_replicate] at hs2 hr2
    have h2 : (flip bind (Turing.TM2.step PvsNP.Units.m2_exp_clock_aux.exp2TM.m))^[s2]
        (some (Turing.initList PvsNP.Units.m2_exp_clock_aux.exp2TM
          ((List.map c1.outputAlphabet.invFun
            (PvsNP.encodeString (List.replicate (a.length ^ k) true))).map φ))) =
        some (Turing.haltList PvsNP.Units.m2_exp_clock_aux.exp2TM
          (List.replicate (2 ^ (a.length ^ k)) true)) := by
      rw [hφ]; exact hr2
    obtain ⟨n, hn, _, hrun⟩ := PvsNP.Units.m2_poly_clock.comp_run φ d hd
      (List.map c1.inputAlphabet.invFun (PvsNP.encodeString a))
      (List.map c1.outputAlphabet.invFun
        (PvsNP.encodeString (List.replicate (a.length ^ k) true)))
      (List.replicate (2 ^ (a.length ^ k)) true)
      r1.steps s2 r1.evals_in_steps h2
    have hlen_o1 : (List.map c1.outputAlphabet.invFun
        (PvsNP.encodeString (List.replicate (a.length ^ k) true))).length = a.length ^ k := by
      change (List.map c1.outputAlphabet.invFun (List.replicate (a.length ^ k) true)).length =
        a.length ^ k
      simp
    have hb1 : r1.steps ≤ c1.time.eval a.length := r1.steps_le_m
    have hbound : n ≤ (C + 9) * 2 ^ (a.length ^ k) + 2 := by
      have := htime a.length
      omega
    exact ⟨n, hbound, hrun⟩
  refine ⟨C + 9, {
    tm := PvsNP.Units.m2_poly_clock.comp c1.tm PvsNP.Units.m2_exp_clock_aux.exp2TM φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := fun n => (C + 9) * 2 ^ (n ^ k) + 2
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), by
          have h := (Classical.choose_spec (key a)).2
          have henc2 : PvsNP.encodeString (List.replicate (2 ^ (a.length ^ k)) true) =
              List.replicate (2 ^ (a.length ^ k)) true := rfl
          rw [henc2]
          simp only [Option.map_some, Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl]
          erw [List.map_id]
          exact h⟩,
        by
          have h := (Classical.choose_spec (key a)).1
          have henc : PvsNP.encodeString a = a := rfl
          simpa [henc] using h⟩
  }, fun n => by simp⟩
