import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tl_lang_len_square_p

namespace PvsNP.Units.tl_lang_len_tri_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-- One step of the triangular-number search: the state is `pairB k (pairB fnd x)`
where `k` is the unary counter being tried, `fnd` is `[]` (not found yet) or
`[true]` (found), and `x` is the input. The step increments `k` and sets `fnd`
to `[true]` when `k * (k + 1) = 2 * x.length`. -/
def triStep (s : List Bool) : List Bool :=
  let k := (unpairB s).1
  let fnd := (unpairB (unpairB s).2).1
  let x := (unpairB (unpairB s).2).2
  let tri := mulU k (true :: k)
  let dbl := x ++ x
  let eqF := sel (leFlag tri dbl) [] (sel (leFlag dbl tri) [] [true])
  let fnd' := sel fnd eqF [true]
  pairB (true :: k) (pairB fnd' x)

theorem cpt_triStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) triStep := by
  have hk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hfnd : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hk1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => true :: (unpairB s).1) := cpt_cons1 true hk
  have htri : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (unpairB s).1 (true :: (unpairB s).1)) := cpt_mulU2 hk hk1
  have hdbl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).2) :=
    cpt_comp (cpt_pair hx hx) cpt_append
  have heqF := cpt_sel (cpt_leFlag htri hdbl) (cpt_const [])
    (cpt_sel (cpt_leFlag hdbl htri) (cpt_const []) (cpt_const [true]))
  have hfnd' := cpt_sel hfnd heqF (cpt_const [true])
  exact cpt_pairB2 (cpt_cons1 true hk) (cpt_pairB2 hfnd' hx)

theorem triStep_length (s : List Bool) : (triStep s).length ≤ s.length + 6 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have heqF : (sel (leFlag (mulU (unpairB s).1 (true :: (unpairB s).1))
      ((unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).2)) []
      (sel (leFlag ((unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).2)
        (mulU (unpairB s).1 (true :: (unpairB s).1))) [] [true])).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  have hfnd' : (sel (unpairB (unpairB s).2).1
      (sel (leFlag (mulU (unpairB s).1 (true :: (unpairB s).1))
        ((unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).2)) []
        (sel (leFlag ((unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).2)
          (mulU (unpairB s).1 (true :: (unpairB s).1))) [] [true]))
      [true]).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  simp only [triStep, pairB_length, List.length_cons]
  omega

theorem triStep_iter_iff (n : ℕ) (k₀ fnd₀ x : List Bool) (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    (unpairB (unpairB (triStep^[n] (pairB k₀ (pairB fnd₀ x)))).2).1 = [true] ↔
      (fnd₀ = [true] ∨ ∃ j < n, (k₀.length + j) * (k₀.length + j + 1) = 2 * x.length) := by
  induction n generalizing k₀ fnd₀ with
  | zero =>
    simp [unpairB_pairB]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hmul : (mulU k₀ (true :: k₀)).length = k₀.length * (k₀.length + 1) := by
      rw [PvsNP.Units.tl_lang_len_square_p.mulU_length_eq, List.length_cons]
    have hdbl : (x ++ x).length = 2 * x.length := by
      rw [List.length_append]; omega
    have hstep : triStep (pairB k₀ (pairB fnd₀ x)) =
        pairB (true :: k₀) (pairB
          (sel fnd₀ (if (mulU k₀ (true :: k₀)).length = (x ++ x).length then [true] else []) [true]) x) := by
      simp only [triStep, unpairB_pairB,
        PvsNP.Units.tl_lang_len_square_p.eqFlag_eq]
    rw [hstep]
    let fnd' := sel fnd₀ (if (mulU k₀ (true :: k₀)).length = (x ++ x).length then [true] else []) [true]
    have hfnd' : fnd' = [] ∨ fnd' = [true] := by
      dsimp [fnd']; unfold sel; split_ifs <;> simp
    rw [ih (true :: k₀) fnd' hfnd']
    have hfnd'_iff : fnd' = [true] ↔
        (fnd₀ = [true] ∨ k₀.length * (k₀.length + 1) = 2 * x.length) := by
      dsimp [fnd']; unfold sel
      rcases hfnd with rfl | rfl
      · simp [hmul, hdbl]
      · simp
    rw [hfnd'_iff, List.length_cons]
    constructor
    · rintro ((h0 | hsq) | ⟨j, hj, hjsq⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨0, Nat.succ_pos m, by simpa using hsq⟩
      · exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by convert hjsq using 2 <;> omega⟩
    · rintro (h0 | ⟨j, hj, hjsq⟩)
      · exact Or.inl (Or.inl h0)
      · cases j with
        | zero => exact Or.inl (Or.inr (by simpa using hjsq))
        | succ j' => exact Or.inr ⟨j', Nat.lt_of_succ_lt_succ hj, by convert hjsq using 2 <;> omega⟩

theorem triStep_iter_or (n : ℕ) (k₀ fnd₀ x : List Bool) (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    let r := (unpairB (unpairB (triStep^[n] (pairB k₀ (pairB fnd₀ x)))).2).1
    r = [] ∨ r = [true] := by
  induction n generalizing k₀ fnd₀ with
  | zero => simpa [unpairB_pairB] using hfnd
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : triStep (pairB k₀ (pairB fnd₀ x)) =
        pairB (true :: k₀) (pairB
          (sel fnd₀ (if (mulU k₀ (true :: k₀)).length = (x ++ x).length then [true] else []) [true]) x) := by
      simp only [triStep, unpairB_pairB,
        PvsNP.Units.tl_lang_len_square_p.eqFlag_eq]
    rw [hstep]
    let fnd' := sel fnd₀ (if (mulU k₀ (true :: k₀)).length = (x ++ x).length then [true] else []) [true]
    have hfnd' : fnd' = [] ∨ fnd' = [true] := by
      dsimp [fnd']; unfold sel; split_ifs <;> simp
    exact ih (true :: k₀) fnd' hfnd'

end PvsNP.Units.tl_lang_len_tri_p

theorem PvsNP.Units.tl_lang_len_tri_p :
    ({x : List Bool | ∃ k : ℕ, 2 * x.length = k * (k + 1)} : Language Bool) ∈ PvsNP.P := by
  have hInit : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
  have hIter := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_iterGrow
    PvsNP.Units.tl_lang_len_tri_p.cpt_triStep 6
    PvsNP.Units.tl_lang_len_tri_p.triStep_length
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_cons1 true
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
    hInit
  have hFnd := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hIter
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB1_1
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2)
  have hDec := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hFnd
    PvsNP.Units.tl_lang_len_square_p.cpt_nonEmpty
  refine ⟨_, hDec, ?_⟩
  intro x
  change (∃ k : ℕ, 2 * x.length = k * (k + 1)) ↔
    (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_tri_p.triStep^[(true :: x).length]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1.isEmpty) = true
  simp only [List.length_cons]
  have hiff := PvsNP.Units.tl_lang_len_tri_p.triStep_iter_iff (x.length + 1) [] [] x (Or.inl rfl)
  have hor := PvsNP.Units.tl_lang_len_tri_p.triStep_iter_or (x.length + 1) [] [] x (Or.inl rfl)
  simp only [List.length_nil, zero_add] at hiff
  have hiff' : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_tri_p.triStep^[x.length + 1]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1 = [true] ↔
      ∃ j < x.length + 1, j * (j + 1) = 2 * x.length := by
    rw [hiff]
    constructor
    · rintro (h | h)
      · exact absurd h (by simp)
      · exact h
    · exact Or.inr
  have hne : (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_tri_p.triStep^[x.length + 1]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1.isEmpty) = true ↔
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.tl_lang_len_tri_p.triStep^[x.length + 1]
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1 = [true] := by
    rcases hor with h | h <;> rw [h] <;> simp
  rw [hne, hiff']
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk.symm⟩
    -- `k * (k + 1) = 2 * x.length` forces `k ≤ x.length`: otherwise
    -- `k * (k + 1) ≥ (x.length + 1) * (x.length + 2) > 2 * x.length`.
    by_contra hlt
    push_neg at hlt
    have h1 : x.length + 1 ≤ k := hlt
    have h2 : (x.length + 1) * (x.length + 2) ≤ k * (k + 1) :=
      Nat.mul_le_mul h1 (by omega)
    have h3 : (x.length + 1) * (x.length + 2) > 2 * x.length := by
      have heq : (x.length + 1) * (x.length + 2)
          = x.length * x.length + 3 * x.length + 2 := by ring
      omega
    omega
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj.symm⟩
