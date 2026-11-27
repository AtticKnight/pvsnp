import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_padded_np_nexp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem hd_eq_un (w : List Bool) : hd w = un (hd w).length := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | false => rfl
    | true =>
      simp only [hd, List.takeWhile_cons, id_eq, ↓reduceIte, List.length_cons, un,
        List.replicate_succ] at ih ⊢
      exact congrArg (true :: ·) ih

theorem poly_le_const_pow (p : Polynomial ℕ) :
    ∃ A d : ℕ, ∀ m : ℕ, p.eval m ≤ A * (m + 1) ^ d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨A1, d1, h1⟩ := hp
    obtain ⟨A2, d2, h2⟩ := hq
    refine ⟨A1 + A2, max d1 d2, fun m => ?_⟩
    rw [Polynomial.eval_add, Nat.add_mul]
    have hm1 : 1 ≤ m + 1 := Nat.succ_pos m
    have e1 : A1 * (m + 1) ^ d1 ≤ A1 * (m + 1) ^ max d1 d2 :=
      Nat.mul_le_mul_left A1 (Nat.pow_le_pow_right hm1 (le_max_left d1 d2))
    have e2 : A2 * (m + 1) ^ d2 ≤ A2 * (m + 1) ^ max d1 d2 :=
      Nat.mul_le_mul_left A2 (Nat.pow_le_pow_right hm1 (le_max_right d1 d2))
    exact Nat.add_le_add ((h1 m).trans e1) ((h2 m).trans e2)
  | monomial d c =>
    refine ⟨c, d, fun m => ?_⟩
    rw [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.le_succ m) d)

theorem exp_pad_bound (p : Polynomial ℕ) (k : ℕ) :
    ∃ j : ℕ, ∀ n : ℕ,
      (2 ^ (n ^ k) + k) + 1 + p.eval ((2 ^ (n ^ k) + k) + 1 + n) ≤ 2 ^ (n ^ j) + j := by
  obtain ⟨A, d, hAd⟩ := poly_le_const_pow p
  let M : ℕ := k + 2
  let C0 : ℕ := (A + 1) * (M + 3) ^ (d + 1)
  let E : ℕ := d + 1
  let j0 : ℕ := k + 1 + C0 + E + 1
  let j : ℕ := j0 + C0 * 2 ^ E
  have hbound : ∀ n : ℕ,
      (2 ^ (n ^ k) + k) + 1 + p.eval ((2 ^ (n ^ k) + k) + 1 + n) ≤
        C0 * 2 ^ (E * n ^ (k + 1)) := by
    intro n
    set B := (2 ^ (n ^ k) + k) + 1 + n
    have hpow_le : 2 ^ (n ^ k) ≤ 2 * 2 ^ (n ^ (k + 1)) := by
      cases n with
      | zero =>
        cases k <;> simp
      | succ n' =>
        have h1 : 2 ^ ((n' + 1) ^ k) ≤ 2 ^ ((n' + 1) ^ (k + 1)) :=
          Nat.pow_le_pow_right (by omega)
            (Nat.pow_le_pow_right (Nat.succ_pos n') (Nat.le_succ k))
        omega
    have hn_le : n ≤ 2 ^ (n ^ (k + 1)) :=
      (Nat.le_self_pow (Nat.succ_ne_zero k) n).trans Nat.lt_two_pow_self.le
    have h1_le : 1 ≤ 2 ^ (n ^ (k + 1)) := Nat.one_le_two_pow
    have hB1 : B + 1 ≤ (M + 3) * 2 ^ (n ^ (k + 1)) := by
      have hM : (M + 3) * 2 ^ (n ^ (k + 1)) =
          2 * 2 ^ (n ^ (k + 1)) + 2 ^ (n ^ (k + 1)) + M * 2 ^ (n ^ (k + 1)) := by ring
      have hM2 : M ≤ M * 2 ^ (n ^ (k + 1)) := Nat.le_mul_of_pos_right M (Nat.two_pow_pos _)
      dsimp only [B, M] at hM hM2 ⊢
      omega
    have hB_pow : B + 1 ≤ (B + 1) ^ E :=
      Nat.le_self_pow (Nat.succ_ne_zero d) (B + 1)
    have hpB : p.eval B ≤ A * (B + 1) ^ E := by
      have h1 := hAd B
      have h2 : (B + 1) ^ d ≤ (B + 1) ^ E :=
        Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.le_succ d)
      exact h1.trans (Nat.mul_le_mul_left A h2)
    have hsum : (2 ^ (n ^ k) + k) + 1 + p.eval B ≤ (A + 1) * (B + 1) ^ E := by
      have hlin : (2 ^ (n ^ k) + k) + 1 ≤ B + 1 := by dsimp only [B]; omega
      have hring : (A + 1) * (B + 1) ^ E = (B + 1) ^ E + A * (B + 1) ^ E := by ring
      rw [hring]
      exact Nat.add_le_add (hlin.trans hB_pow) hpB
    have hpowE : (B + 1) ^ E ≤ (M + 3) ^ E * 2 ^ (E * n ^ (k + 1)) := by
      calc (B + 1) ^ E
          ≤ ((M + 3) * 2 ^ (n ^ (k + 1))) ^ E := Nat.pow_le_pow_left hB1 E
        _ = (M + 3) ^ E * (2 ^ (n ^ (k + 1))) ^ E := Nat.mul_pow _ _ _
        _ = (M + 3) ^ E * 2 ^ (n ^ (k + 1) * E) := by rw [← Nat.pow_mul]
        _ = (M + 3) ^ E * 2 ^ (E * n ^ (k + 1)) := by rw [Nat.mul_comm (n ^ (k + 1)) E]
    calc (2 ^ (n ^ k) + k) + 1 + p.eval B
        ≤ (A + 1) * (B + 1) ^ E := hsum
      _ ≤ (A + 1) * ((M + 3) ^ E * 2 ^ (E * n ^ (k + 1))) := Nat.mul_le_mul_left _ hpowE
      _ = C0 * 2 ^ (E * n ^ (k + 1)) := by dsimp only [C0, E]; ring
  refine ⟨j, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hnk : n ^ (k + 1) ≤ 1 := by
      interval_cases n <;> simp
    have hE : E * n ^ (k + 1) ≤ E := by
      calc E * n ^ (k + 1) ≤ E * 1 := Nat.mul_le_mul_left E hnk
        _ = E := Nat.mul_one E
    have h1 := hbound n
    have h2 : C0 * 2 ^ (E * n ^ (k + 1)) ≤ C0 * 2 ^ E :=
      Nat.mul_le_mul_left C0 (Nat.pow_le_pow_right (by omega) hE)
    have h3 : C0 * 2 ^ E ≤ j := Nat.le_add_left _ _
    exact (h1.trans h2).trans (h3.trans (Nat.le_add_left _ _))
  · have hC0 : C0 ≤ 2 ^ C0 := Nat.lt_two_pow_self.le
    have h1 : C0 * 2 ^ (E * n ^ (k + 1)) ≤ 2 ^ (C0 + E * n ^ (k + 1)) := by
      rw [Nat.pow_add 2 C0 (E * n ^ (k + 1))]
      exact Nat.mul_le_mul_right _ hC0
    have hnC0 : C0 ≤ n ^ (k + 1 + C0 + E) := by
      have hlt : C0 ≤ 2 ^ C0 := Nat.lt_two_pow_self.le
      have h2n : 2 ^ C0 ≤ n ^ C0 := Nat.pow_le_pow_left hn C0
      have hpow : n ^ C0 ≤ n ^ (k + 1 + C0 + E) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact (hlt.trans h2n).trans hpow
    have hnE : E * n ^ (k + 1) ≤ n ^ (k + 1 + C0 + E) := by
      have hlt : E ≤ 2 ^ E := Nat.lt_two_pow_self.le
      have h2n : 2 ^ E ≤ n ^ E := Nat.pow_le_pow_left hn E
      calc E * n ^ (k + 1)
          ≤ n ^ E * n ^ (k + 1) := Nat.mul_le_mul_right _ (hlt.trans h2n)
        _ = n ^ (E + (k + 1)) := (Nat.pow_add n E (k + 1)).symm
        _ ≤ n ^ (k + 1 + C0 + E) := Nat.pow_le_pow_right (by omega) (by omega)
    have hexp : C0 + E * n ^ (k + 1) ≤ n ^ j := by
      have h2 : C0 + E * n ^ (k + 1) ≤ 2 * n ^ (k + 1 + C0 + E) := by omega
      have hmul : 2 * n ^ (k + 1 + C0 + E) ≤ n * n ^ (k + 1 + C0 + E) :=
        Nat.mul_le_mul_right _ hn
      have hsucc : n * n ^ (k + 1 + C0 + E) = n ^ j0 := by
        dsimp only [j0]
        rw [Nat.pow_succ, Nat.mul_comm]
      have hj0 : n ^ j0 ≤ n ^ j :=
        Nat.pow_le_pow_right (by omega) (Nat.le_add_right j0 _)
      exact ((h2.trans hmul).trans hsucc.le).trans hj0
    exact ((hbound n).trans h1).trans
      ((Nat.pow_le_pow_right (by omega) hexp).trans (Nat.le_add_right _ _))

theorem cpt_padVer (V0 : List Bool × List Bool → Bool)
    (hV0 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool V0) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun q : List Bool × List Bool => V0 (hd q.2 ++ false :: q.1, dropN q.2)) := by
  have henc : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
    funext ⟨x, y⟩
    simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have harg1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => hd (unpairB s).2 ++ false :: (unpairB s).1) :=
    cpt_app2 (cpt_hd1 cpt_unpairB2) (cpt_cons1 false cpt_unpairB1)
  have harg2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => dropN (unpairB s).2) :=
    cpt_dropN1 cpt_unpairB2
  have hmap := cpt_comp (cpt_comp cpt_pairB (cpt_pair harg1 harg2)) hV0
  have hfun : (fun q : List Bool × List Bool =>
      V0 (hd (unpairB (pairB q.1 q.2)).2 ++ false :: (unpairB (pairB q.1 q.2)).1,
        dropN (unpairB (pairB q.1 q.2)).2)) =
      (fun q : List Bool × List Bool => V0 (hd q.2 ++ false :: q.1, dropN q.2)) := by
    funext ⟨x, c⟩
    simp [unpairB_pairB]
  rw [hfun] at hmap
  rw [henc]
  exact hmap

theorem padded_np_nexp_aux :
    ∀ (L : Language Bool) (k : ℕ),
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈
        PvsNP.NP →
      ∃ (V : List Bool × List Bool → Bool) (j : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ j) + j ∧ V (x, w) = true := by
  intro L k hpad
  let Lpad : Language Bool :=
    {s : List Bool | ∃ x : List Bool, x ∈ L ∧
      s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x}
  obtain ⟨R, p, ⟨V0, hVR, hVc⟩, hlen, hmem⟩ :=
    L045 Lpad ((PvsNP.Units.fr_ladner.NP_iff Lpad).1 hpad)
  obtain ⟨j, hj⟩ := exp_pad_bound p k
  refine ⟨fun q => V0 (hd q.2 ++ false :: q.1, dropN q.2), j, cpt_padVer V0 hVc, fun x => ?_⟩
  constructor
  · intro hx
    let s : List Bool := List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x
    have hsLpad : s ∈ Lpad := ⟨x, hx, rfl⟩
    obtain ⟨w0, hw0⟩ := (hmem s).1 hsLpad
    have hV0w : V0 (s, w0) = true := (hVR (s, w0)).1 hw0
    have hw0len : w0.length ≤ p.eval s.length := hlen s w0 hw0
    let w : List Bool := List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: w0
    have hlenS : s.length = (2 ^ (x.length ^ k) + k) + 1 + x.length := by
      simp only [s, List.length_append, List.length_replicate, List.length_cons]
      omega
    have hlenW : w.length ≤ 2 ^ (x.length ^ j) + j := by
      have hwEq : w.length = (2 ^ (x.length ^ k) + k) + 1 + w0.length := by
        simp only [w, List.length_append, List.length_replicate, List.length_cons]
        omega
      rw [hlenS] at hw0len
      have hjx := hj x.length
      omega
    refine ⟨w, hlenW, ?_⟩
    have hhd : hd w = List.replicate (2 ^ (x.length ^ k) + k) true :=
      hd_un (2 ^ (x.length ^ k) + k) w0
    have hdrop : dropN w = w0 :=
      dropN_un (2 ^ (x.length ^ k) + k) w0
    dsimp only
    rw [hhd, hdrop]
    exact hV0w
  · rintro ⟨w, _, hVw⟩
    have hmemPad : hd w ++ false :: x ∈ Lpad := (hmem _).2 ⟨dropN w, (hVR _).2 hVw⟩
    obtain ⟨x', hx'L, hEq⟩ := hmemPad
    have hdropEq := congrArg dropN hEq
    have hL : dropN (hd w ++ false :: x) = x := by
      rw [hd_eq_un w]
      exact dropN_un (hd w).length x
    have hR : dropN (List.replicate (2 ^ (x'.length ^ k) + k) true ++ false :: x') = x' :=
      dropN_un (2 ^ (x'.length ^ k) + k) x'
    rw [hL, hR] at hdropEq
    rw [hdropEq]
    exact hx'L

end PvsNP.Units.m2_padded_np_nexp

/-- Downward translation: if an exponential padding of `L` is in NP, then `L` is in NEXP. -/
theorem PvsNP.Units.m2_padded_np_nexp :
    ∀ (L : Language Bool) (k : ℕ),
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈
        PvsNP.NP →
      ∃ (V : List Bool × List Bool → Bool) (j : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ j) + j ∧ V (x, w) = true :=
  PvsNP.Units.m2_padded_np_nexp.padded_np_nexp_aux
