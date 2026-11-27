import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_padded_test_exp

namespace PvsNP.Units.tc_exp_prefix_ext

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.LenCmp
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem succD_len (q : Bool) (s : List Bool) :
    (fstRun succD succFin q s).length ≤ s.length + 1 := by
  induction s generalizing q with
  | nil => cases q <;> simp [fstRun, succFin]
  | cons b l ih =>
    have h1 := ih b
    have h2 := ih false
    cases q <;> simp [fstRun, succD] <;> omega

theorem succB_len (s : List Bool) : (succB s).length ≤ s.length + 1 :=
  succD_len true s

theorem cpt_succB_local :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) succB :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) succB succD succFin true
    (fun _ => rfl)

def isNonEmptyδ : Bool → Bool → Bool × Option Bool
  | _, _ => (true, none)

def isNonEmptyFin : Bool → Option Bool
  | false => some false
  | true => some true

theorem isNonEmpty_run (x : List Bool) (q : Bool) :
    fstRun isNonEmptyδ isNonEmptyFin q x =
      Computability.encodeBool (if q then true else decide (x ≠ [])) := by
  induction x generalizing q with
  | nil => cases q <;> rfl
  | cons _ t ih =>
    simp only [fstRun, isNonEmptyδ, Option.toList_none, List.nil_append]
    rw [ih true]
    cases q <;> rfl

theorem cpt_isNonEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => decide (x ≠ [])) := by
  refine fst_polyTime (fun x : List Bool => x) Computability.encodeBool
    (fun x : List Bool => decide (x ≠ [])) isNonEmptyδ isNonEmptyFin false ?_
  intro x
  simpa using (isNonEmpty_run x false).symm

def extStep (a : List Bool) (st : List Bool) : List Bool :=
  let x := (unpairB st).1
  let r1 := (unpairB st).2
  let budget := (unpairB r1).1
  let r2 := (unpairB r1).2
  let cur := (unpairB r2).1
  let fl := (unpairB r2).2
  let lenOk := if decide (cur.length ≤ x.length) then [true] else []
  let vOk := if V (pairB a (pairB (x ++ cur) budget), []) then [true] else []
  let hit := sel lenOk [] vOk
  let fl' := sel fl hit [true]
  pairB x (pairB budget (pairB (succB cur) fl'))

theorem extStep_length (a : List Bool) (st : List Bool) :
    (extStep a st).length ≤ st.length + 6 := by
  dsimp only [extStep]
  simp only [pairB_length]
  have h1 := unpairB_length st
  have h2 := unpairB_length (unpairB st).2
  have h3 := unpairB_length (unpairB (unpairB st).2).2
  have hs := succB_len (unpairB (unpairB (unpairB st).2).2).1
  have hfl : (sel (unpairB (unpairB (unpairB st).2).2).2
      (sel (if decide ((unpairB (unpairB (unpairB st).2).2).1.length ≤ (unpairB st).1.length)
          then [true] else []) []
        (if V (pairB a (pairB ((unpairB st).1 ++ (unpairB (unpairB (unpairB st).2).2).1)
          (unpairB (unpairB st).2).1), []) then [true] else []))
      [true]).length ≤ 1 := by
    unfold sel
    split_ifs <;> simp
  omega

theorem cpt_extStep (a : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (extStep a) := by
  have hx := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hbud := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hcur := cpt_unpairB1_1 hr2
  have hfl := cpt_unpairB2_1 hr2
  have hlenBool : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun st => decide ((unpairB (unpairB (unpairB st).2).2).1.length ≤ (unpairB st).1.length)) :=
    cpt_comp (cpt_pair hx hcur) lenLE_polyTime
  have hlenOk := cpt_bitFlag hlenBool
  have hqry := cpt_pairB2 (cpt_const a) (cpt_pairB2 (cpt_app2 hx hcur) hbud)
  have hVBool : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun st => V (pairB a (pairB ((unpairB st).1 ++ (unpairB (unpairB (unpairB st).2).2).1)
        (unpairB (unpairB st).2).1), [])) :=
    cpt_comp (cpt_pair hqry (cpt_const [])) (cpt_V cpt_sstep)
  have hvOk := cpt_bitFlag hVBool
  have hhit := cpt_sel hlenOk (cpt_const []) hvOk
  have hfl' := cpt_sel hfl hhit (cpt_const [true])
  have hcur' := cpt_comp hcur cpt_succB_local
  exact cpt_pairB2 hx (cpt_pairB2 hbud (cpt_pairB2 hcur' hfl'))

theorem extStep_iter (a : List Bool) :
    ∀ (m : ℕ) (x budget cur fl : List Bool),
      ∃ fl' : List Bool,
        (extStep a)^[m] (pairB x (pairB budget (pairB cur fl))) =
          pairB x (pairB budget (pairB (succB^[m] cur) fl')) ∧
        (fl' ≠ [] ↔ fl ≠ [] ∨
          ∃ j : ℕ, j < m ∧ (succB^[j] cur).length ≤ x.length ∧
            V (pairB a (pairB (x ++ succB^[j] cur) budget), []) = true) := by
  intro m
  induction m with
  | zero =>
    intro x budget cur fl
    refine ⟨fl, rfl, ?_⟩
    simp
  | succ m ih =>
    intro x budget cur fl
    let lenOk := if decide (cur.length ≤ x.length) then [true] else []
    let vOk := if V (pairB a (pairB (x ++ cur) budget), []) then [true] else []
    let hit := sel lenOk [] vOk
    let fl1 := sel fl hit [true]
    have hst : extStep a (pairB x (pairB budget (pairB cur fl))) =
        pairB x (pairB budget (pairB (succB cur) fl1)) := by
      simp [extStep, unpairB_pairB, lenOk, vOk, hit, fl1]
    have hfl1 : fl1 ≠ [] ↔ fl ≠ [] ∨
        (cur.length ≤ x.length ∧ V (pairB a (pairB (x ++ cur) budget), []) = true) := by
      by_cases hfe : fl = []
      · by_cases hle : cur.length ≤ x.length
        · cases hvv : V (pairB a (pairB (x ++ cur) budget), []) <;>
            simp [fl1, hit, lenOk, vOk, sel, hfe, hle, hvv]
        · simp [fl1, hit, lenOk, vOk, sel, hfe, hle]
      · simp [fl1, sel, hfe]
    obtain ⟨fl', hrun, hiff⟩ := ih x budget (succB cur) fl1
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hst, hrun, Function.iterate_succ_apply]
    · rw [hiff, hfl1]
      constructor
      · intro h
        rcases h with (hf | ⟨hle, hvv⟩) | ⟨j, hj, hle, hvv⟩
        · exact Or.inl hf
        · exact Or.inr ⟨0, Nat.zero_lt_succ m, hle, hvv⟩
        · exact Or.inr ⟨j + 1, by omega, by rwa [Function.iterate_succ_apply],
            by rwa [Function.iterate_succ_apply]⟩
      · intro h
        rcases h with hf | ⟨j, hj, hle, hvv⟩
        · exact Or.inl (Or.inl hf)
        · cases j with
          | zero => exact Or.inl (Or.inr ⟨hle, hvv⟩)
          | succ j' =>
            rw [Function.iterate_succ_apply] at hle hvv
            exact Or.inr ⟨j', by omega, hle, hvv⟩

def runExt (a s : List Bool) : List Bool :=
  (extStep a)^[(hd s).length] (pairB (dropN s) (pairB (hd s) (pairB [] [])))

def extDec (a s : List Bool) : Bool :=
  decide ((unpairB (unpairB (unpairB (runExt a s)).2).2).2 ≠ [])

theorem cpt_extDec (a : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (extDec a) := by
  have harg := cpt_pairB2 cpt_dropN (cpt_pairB2 cpt_hd (cpt_pairB2 (cpt_const []) (cpt_const [])))
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (runExt a) :=
    cpt_iterGrow (cpt_extStep a) 6 (extStep_length a) cpt_hd harg
  have hfl := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hrun))
  unfold extDec
  exact cpt_comp (f := fun s => (unpairB (unpairB (unpairB (runExt a s)).2).2).2)
    (g := fun l : List Bool => decide (l ≠ [])) hfl cpt_isNonEmpty

theorem exists_budget_exp (d k : ℕ) :
    ∃ K : ℕ, ∀ n : ℕ,
      2 ^ (n + 1) ≤ 2 ^ (n ^ K) + K ∧
      d * (2 ^ ((2 * n) ^ k) + k) + d ≤ 2 ^ (n ^ K) + K := by
  let C : ℕ := d * (k + 2)
  let K0 : ℕ := 2 * k + C + 3
  let K : ℕ := K0 + 4 + d * (2 ^ (2 ^ k) + k) + d
  refine ⟨K, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h2n : 2 * n ≤ 2 := by omega
    have hpow : (2 * n) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left h2n k
    have h1 : 2 ^ (n + 1) ≤ 4 := by
      interval_cases n <;> simp
    have h2 : d * (2 ^ ((2 * n) ^ k) + k) + d ≤ d * (2 ^ (2 ^ k) + k) + d := by
      have hp : 2 ^ ((2 * n) ^ k) ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) hpow
      have hm := Nat.mul_le_mul_left d (Nat.add_le_add_right hp k)
      omega
    have hK1 : 4 ≤ K := by dsimp only [K]; omega
    have hK2 : d * (2 ^ (2 ^ k) + k) + d ≤ K := by dsimp only [K]; omega
    exact ⟨(h1.trans hK1).trans (Nat.le_add_left _ _),
      (h2.trans hK2).trans (Nat.le_add_left _ _)⟩
  · have h2n : (2 * n) ^ k ≤ n ^ (2 * k) := by
      calc (2 * n) ^ k
          = 2 ^ k * n ^ k := Nat.mul_pow 2 n k
        _ ≤ n ^ k * n ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn k)
        _ = n ^ (k + k) := (Nat.pow_add n k k).symm
        _ = n ^ (2 * k) := by rw [Nat.two_mul]
    have h1pow : n + 1 ≤ n ^ K := by
      have hsq : n + 1 ≤ n ^ 2 := by
        rw [pow_two]
        nlinarith
      have hKge : 2 ≤ K := by dsimp only [K, K0]; omega
      exact hsq.trans (Nat.pow_le_pow_right (by omega) hKge)
    have h1 : 2 ^ (n + 1) ≤ 2 ^ (n ^ K) + K :=
      (Nat.pow_le_pow_right (by omega) h1pow).trans (Nat.le_add_right _ _)
    have hdom : d * (2 ^ ((2 * n) ^ k) + k) + d ≤ C * 2 ^ (n ^ (2 * k)) := by
      have hp : 2 ^ ((2 * n) ^ k) ≤ 2 ^ (n ^ (2 * k)) := Nat.pow_le_pow_right (by omega) h2n
      have hk1 : k ≤ k * 2 ^ (n ^ (2 * k)) := Nat.le_mul_of_pos_right k (Nat.two_pow_pos _)
      have h1' : 1 ≤ 2 ^ (n ^ (2 * k)) := Nat.one_le_two_pow
      have hsum : 2 ^ ((2 * n) ^ k) + k + 1 ≤ (k + 2) * 2 ^ (n ^ (2 * k)) := by
        have hr : (k + 2) * 2 ^ (n ^ (2 * k)) =
            2 ^ (n ^ (2 * k)) + k * 2 ^ (n ^ (2 * k)) + 2 ^ (n ^ (2 * k)) := by ring
        omega
      calc d * (2 ^ ((2 * n) ^ k) + k) + d
          = d * (2 ^ ((2 * n) ^ k) + k + 1) := by ring
        _ ≤ d * ((k + 2) * 2 ^ (n ^ (2 * k))) := Nat.mul_le_mul_left d hsum
        _ = C * 2 ^ (n ^ (2 * k)) := by dsimp only [C]; ring
    have hC2 : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
    have hCmul : C * 2 ^ (n ^ (2 * k)) ≤ 2 ^ (C + n ^ (2 * k)) := by
      rw [Nat.pow_add 2 C (n ^ (2 * k))]
      exact Nat.mul_le_mul_right _ hC2
    have hCn : C ≤ n ^ (2 * k + C) := by
      have h2nC : 2 ^ C ≤ n ^ C := Nat.pow_le_pow_left hn C
      have hp : n ^ C ≤ n ^ (2 * k + C) := Nat.pow_le_pow_right (by omega) (by omega)
      exact (hC2.trans h2nC).trans hp
    have h2kn : n ^ (2 * k) ≤ n ^ (2 * k + C) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hexp : C + n ^ (2 * k) ≤ n ^ K := by
      have hs : C + n ^ (2 * k) ≤ 2 * n ^ (2 * k + C) := by omega
      have hm : 2 * n ^ (2 * k + C) ≤ n * n ^ (2 * k + C) := Nat.mul_le_mul_right _ hn
      have hsucc : n * n ^ (2 * k + C) = n ^ (2 * k + C + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hKge : 2 * k + C + 1 ≤ K := by dsimp only [K, K0]; omega
      exact ((hs.trans hm).trans hsucc.le).trans (Nat.pow_le_pow_right (by omega) hKge)
    have h2 : d * (2 ^ ((2 * n) ^ k) + k) + d ≤ 2 ^ (n ^ K) + K :=
      ((hdom.trans hCmul).trans (Nat.pow_le_pow_right (by omega) hexp)).trans (Nat.le_add_right _ _)
    exact ⟨h1, h2⟩

theorem exp_prefix_ext_aux :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, (∃ y : List Bool, y.length ≤ x.length ∧ x ++ y ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, hM⟩
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  obtain ⟨K, hK⟩ := exists_budget_exp d k
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hh : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => extDec (encCode c) p.1) := by
    rw [henc]
    exact cpt_comp cpt_fst (cpt_extDec (encCode c))
  obtain ⟨j, M', hM'⟩ :=
    PvsNP.Units.m2_padded_test_exp K (fun x : List Bool => x) (fun _ : List Bool => [])
      (fun p : List Bool × List Bool => extDec (encCode c) p.1) cpt_id (cpt_const []) hh
  refine ⟨j,
    fun x => extDec (encCode c) (List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x),
    M', fun x => ?_, hM'⟩
  set T := 2 ^ (x.length ^ K) + K
  have hT1 : 2 ^ (x.length + 1) ≤ T := (hK x.length).1
  have hT2 : d * (2 ^ ((2 * x.length) ^ k) + k) + d ≤ T := (hK x.length).2
  have hV_iff : ∀ y : List Bool, y.length ≤ x.length →
      (V (pairB (encCode c) (pairB (x ++ y) (un T)), []) = true ↔ f (x ++ y) = true) := by
    intro y hy
    have hrun := (M.outputsFun (x ++ y)).evals_in_steps
    have hsteps : (M.outputsFun (x ++ y)).steps ≤ M.time (x ++ y).length :=
      (M.outputsFun (x ++ y)).steps_le_m
    have hle1 : (x ++ y).length ≤ 2 * x.length := by
      simp only [List.length_append]
      omega
    have hle2 : M.time (x ++ y).length ≤ 2 ^ ((2 * x.length) ^ k) + k := by
      have h1 := hM (x ++ y).length
      have h2 : (x ++ y).length ^ k ≤ (2 * x.length) ^ k := Nat.pow_le_pow_left hle1 k
      have h3 : 2 ^ ((x ++ y).length ^ k) ≤ 2 ^ ((2 * x.length) ^ k) :=
        Nat.pow_le_pow_right (by omega) h2
      omega
    have hleT : d * (M.outputsFun (x ++ y)).steps + d ≤ T := by
      have hm := Nat.mul_le_mul_left d (hsteps.trans hle2)
      omega
    have ho : c.outputsWithin ((x ++ y).map (fun b => cond b 1 0))
        (d * (M.outputsFun (x ++ y)).steps + d) [bitCode (f (x ++ y))] :=
      hc (x ++ y) (f (x ++ y)) (M.outputsFun (x ++ y)).steps hrun
    have hoT := Code.outputsWithin_mono c _ hleT _ ho
    rw [V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
    constructor
    · intro h1
      have heq : [1] = [bitCode (f (x ++ y))] := h1.2.symm.trans hoT.2
      cases hfv : f (x ++ y) with
      | true => rfl
      | false =>
        rw [hfv] at heq
        simp [bitCode] at heq
    · intro hfv
      rw [hfv] at hoT
      exact hoT
  have hhd : hd (List.replicate T true ++ false :: x) = un T := hd_un T x
  have hdrop : dropN (List.replicate T true ++ false :: x) = x := dropN_un T x
  obtain ⟨fl', hrunExt, hflIff⟩ := extStep_iter (encCode c) T x (un T) [] []
  have hdecEq : extDec (encCode c) (List.replicate T true ++ false :: x) = true ↔ fl' ≠ [] := by
    unfold extDec runExt
    rw [hhd, hdrop, un_length, hrunExt, unpairB_pairB, unpairB_pairB, unpairB_pairB,
      decide_eq_true_eq]
  rw [hdecEq, hflIff]
  simp only [ne_eq, not_true_eq_false, false_or]
  constructor
  · rintro ⟨y, hy, hxyL⟩
    refine ⟨idx y, ?_, ?_, ?_⟩
    · have hidx := idx_lt_of_length_le hy
      omega
    · have hci : succB^[idx y] [] = y := cand_idx y
      rwa [hci]
    · have hci : succB^[idx y] [] = y := cand_idx y
      rw [hci]
      exact (hV_iff y hy).2 ((hf (x ++ y)).1 hxyL)
  · rintro ⟨i, _, hlen, hVi⟩
    exact ⟨succB^[i] [], hlen, (hf _).2 ((hV_iff (succB^[i] []) hlen).1 hVi)⟩

end PvsNP.Units.tc_exp_prefix_ext

/-- Exponential time is closed under short extensions `∃ y, |y| ≤ |x| ∧ x ++ y ∈ L`. -/
theorem PvsNP.Units.tc_exp_prefix_ext :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, (∃ y : List Bool, y.length ≤ x.length ∧ x ++ y ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_prefix_ext.exp_prefix_ext_aux
