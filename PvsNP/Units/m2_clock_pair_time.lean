import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_clock_pair_time

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

noncomputable def dupBound :
    ∃ q : Polynomial ℕ,
      ComputableInTime (fun x : List Bool => x)
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
        (fun x : List Bool => (x, x)) (fun n => q.eval n) :=
  time_of_polyTime cpt_dup

noncomputable def pPoly : Polynomial ℕ :=
  Classical.choose dupBound + Polynomial.C 8 * Polynomial.X + Polynomial.C 7

theorem clock_pair_aux :
    ∀ (t : ℕ → ℕ) (c : ℕ),
      (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
          (fun x : List Bool => List.replicate (t x.length) true), ∀ n : ℕ, M.time n ≤ c * t n + c) →
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair
          (fun x : List Bool => (List.replicate (t x.length) true, x)),
        ∀ n : ℕ, M.time n ≤ c * t n + c + 2 * t n + pPoly.eval n := by
  classical
  rintro t c ⟨M_t, hMt⟩
  obtain ⟨c1, hc1⟩ := Classical.choose_spec dupBound
  let e₀ : Bool → M_t.tm.Γ M_t.tm.k₀ := M_t.inputAlphabet.invFun
  let e₁ : M_t.tm.Γ M_t.tm.k₁ → Bool := M_t.outputAlphabet
  let c2 : FinTM2 := firstM M_t.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → c2.Γ c2.k₀ :=
    fun x => (Equiv.refl (Bool ⊕ Bool)).invFun (c1.outputAlphabet x)
  let d : Option (c2.Γ c2.k₀) :=
    if h : Nonempty (c2.Γ c2.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.Γ c2.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.Γ c2.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let ft : List Bool → List Bool := fun x => List.replicate (t x.length) true
  let T : ℕ → ℕ := fun n => c * t n + c + 2 * t n + pPoly.eval n
  have key : ∀ x : List Bool, ∃ n, n ≤ T x.length ∧
      (flip bind (TM2.step (prog c1.tm c2 φ d)))^[n]
          (some (initList (comp c1.tm c2 φ d)
            (List.map c1.inputAlphabet.invFun (PvsNP.encodeString x)))) =
        some (haltList (comp c1.tm c2 φ d)
          (List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair (ft x, x)))) := by
    intro x
    have r1 := c1.outputsFun x
    have hs : (flip bind (TM2.step M_t.tm.m))^[(M_t.outputsFun x).steps]
        (some (initList M_t.tm (x.map e₀))) =
        some (haltList M_t.tm (List.map M_t.outputAlphabet.invFun (ft x))) :=
      (M_t.outputsFun x).evals_in_steps
    obtain ⟨n2, hn2, hrun2⟩ :=
      first_run (M := M_t.tm) e₀ e₁ x x (List.map M_t.outputAlphabet.invFun (ft x))
        (M_t.outputsFun x).steps hs
    have hm : (List.map M_t.outputAlphabet.invFun (ft x)).map e₁ = ft x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (ft x)]
      exact List.map_congr_left fun y _ => M_t.outputAlphabet.right_inv y
    rw [hm] at hrun2
    have hφ : (List.map c1.outputAlphabet.invFun
          (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))).map φ =
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have hrun2' : (flip bind (TM2.step c2.m))^[n2]
        (some (initList c2 ((List.map c1.outputAlphabet.invFun
          (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))).map φ))) =
        some (haltList c2 (List.map (Equiv.refl (Bool ⊕ Bool)).invFun
          (PvsNP.encodePair (ft x, x)))) := by
      have hid : List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair (ft x, x)) =
          PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (ft x, x) := by
        simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
          Computability.encodingProd, Computability.encodingList]
      exact (congrArg (fun l : List (c2.Γ c2.k₀) =>
        (flip bind (TM2.step c2.m))^[n2] (some (initList c2 l))) hφ).trans
        (hrun2.trans (congrArg (fun l : List (c2.Γ c2.k₁) =>
          some (haltList c2 l)) hid.symm))
    obtain ⟨n, hn, -, hrun⟩ :=
      comp_run (M1 := c1.tm) (M2 := c2) φ d hd _ _ _ r1.steps n2 r1.evals_in_steps hrun2'
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ (Classical.choose dupBound).eval x.length :=
      r1.steps_le_m.trans (hc1 x.length)
    have b_s : (M_t.outputsFun x).steps ≤ c * t x.length + c :=
      (M_t.outputsFun x).steps_le_m.trans (hMt x.length)
    have b_len : (List.map M_t.outputAlphabet.invFun (ft x)).length = t x.length := by
      simp [ft]
    have b2 : n2 ≤ c * t x.length + c + 2 * x.length + 2 * x.length + 2 * t x.length + 5 := by
      rw [b_len] at hn2
      omega
    have b_enc : (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x)).length =
        2 * x.length := by
      simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair]
      omega
    have hp : pPoly.eval x.length = (Classical.choose dupBound).eval x.length + 8 * x.length + 7 := by
      simp [pPoly]
    simp only [T, List.length_map, b_enc, hp]
    omega
  refine ⟨{
    tm := comp c1.tm c2 φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun x =>
      ⟨⟨Classical.choose (key x), (Classical.choose_spec (key x)).2⟩,
        (Classical.choose_spec (key x)).1⟩ }, fun _ => le_rfl⟩

end PvsNP.Units.m2_clock_pair_time

theorem PvsNP.Units.m2_clock_pair_time :
    ∃ p : Polynomial ℕ, ∀ (t : ℕ → ℕ) (c : ℕ),
      (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
          (fun x : List Bool => List.replicate (t x.length) true), ∀ n : ℕ, M.time n ≤ c * t n + c) →
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair
          (fun x : List Bool => (List.replicate (t x.length) true, x)),
        ∀ n : ℕ, M.time n ≤ c * t n + c + 2 * t n + p.eval n :=
  ⟨PvsNP.Units.m2_clock_pair_time.pPoly, PvsNP.Units.m2_clock_pair_time.clock_pair_aux⟩
