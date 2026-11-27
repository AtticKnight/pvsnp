import Mathlib
import PvsNP.Defs
import CookLevin

/-
Predicted statements, new proofs over the campaign's definitions and Mathlib's TM2 model: the identity is
polynomial-time (Mathlib's `Turing.idComputableInPolyTime`); P in the time-function form of Mathlib's
`Turing.TM2ComputableInTime` with the bound `n ^ k + k` or a polynomial (upstream lean/PEqualNP/Library/L003.lean
and L004.lean of github.com/open-goat/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9, Apache
License 2.0, restated); a decider within `t` is one within any larger `t'` (upstream L002, restated); and the
vendored SAT string encoding `SATToSATStr.satToStr` is injective (upstream L026 for the vendored encoding; the
round trip is `SATToSATStr.strBits_satToStr` and `CnfWellFormed.parseTotal_encodeCnf` of the vendored library).
No upstream or campaign file is copied.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_p_dtime_poly

/-- The identity on binary strings is polynomial-time computable. -/
theorem id_polytime : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
  ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩

/-- Raise the time function of a machine to any pointwise larger one. -/
def raise {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (M : Turing.TM2ComputableInTime ea eb f) (t : ℕ → ℕ) (h : ∀ n, M.time n ≤ t n) :
    Turing.TM2ComputableInTime ea eb f where
  toTM2ComputableAux := M.toTM2ComputableAux
  time := t
  outputsFun a :=
    { steps := (M.outputsFun a).steps
      evals_in_steps := (M.outputsFun a).evals_in_steps
      steps_le_m := (M.outputsFun a).steps_le_m.trans (h _) }

/-- A machine within a polynomial bound, read as a polynomial-time machine. -/
def toPoly {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (M : Turing.TM2ComputableInTime ea eb f) (p : Polynomial ℕ) (h : ∀ n, M.time n ≤ p.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := M.toTM2ComputableAux
  time := p
  outputsFun a :=
    { steps := (M.outputsFun a).steps
      evals_in_steps := (M.outputsFun a).evals_in_steps
      steps_le_m := (M.outputsFun a).steps_le_m.trans (h _) }

theorem poly_bound (p : Polynomial ℕ) : ∃ k : ℕ, ∀ n : ℕ, p.eval n ≤ n ^ k + k := by
  -- every term a_i n^i is at most a_i n^d; and C n^d ≤ n^(d+C) for n ≥ 2
  refine ⟨p.natDegree + p.eval 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have : p.eval 0 ≤ p.eval 1 := by
        rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
        exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (by
          rcases i with _ | i <;> simp)
      simp only [zero_pow_eq]
      split_ifs <;> omega
    · simp only [one_pow]
      omega
  · have hle : p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      simp only [one_pow, mul_one]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by
        have := Finset.mem_range.mp hi; omega))
    have hC : p.eval 1 ≤ n ^ p.eval 1 :=
      (Nat.lt_pow_self (by omega : 1 < n)).le
    calc p.eval n ≤ p.eval 1 * n ^ p.natDegree := hle
      _ ≤ n ^ p.eval 1 * n ^ p.natDegree := Nat.mul_le_mul_right _ hC
      _ = n ^ (p.natDegree + p.eval 1) := by rw [← pow_add, add_comm]
      _ ≤ _ := Nat.le_add_right _ _

/-- P in the time-function form, with the bound `n ^ k + k`. -/
theorem p_time_normal : ∀ L : Language Bool, L ∈ PvsNP.P ↔
    ∃ (k : ℕ) (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ n ^ k + k := by
  intro L
  constructor
  · intro hL
    obtain ⟨f, ⟨M⟩, hf⟩ := hL
    obtain ⟨k, hk⟩ := poly_bound M.time
    exact ⟨k, f, M.toTM2ComputableInTime, hf, hk⟩
  · rintro ⟨k, f, M, hf, hk⟩
    refine ⟨f, ⟨toPoly M (Polynomial.X ^ k + Polynomial.C k) fun n => ?_⟩, hf⟩
    simpa using hk n

/-- P in the time-function form, with a polynomial bound. -/
theorem p_time_poly : ∀ L : Language Bool, L ∈ PvsNP.P ↔
    ∃ (p : Polynomial ℕ) (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ p.eval n := by
  intro L
  constructor
  · intro hL
    obtain ⟨f, ⟨M⟩, hf⟩ := hL
    exact ⟨M.time, f, M.toTM2ComputableInTime, hf, fun n => le_rfl⟩
  · rintro ⟨p, f, M, hf, hp⟩
    exact ⟨f, ⟨toPoly M p hp⟩, hf⟩

/-- A decider within `t` steps is one within any pointwise larger `t'` (upstream L002). -/
theorem time_mono : ∀ (t t' : ℕ → ℕ) (f : List Bool → Bool), (∀ n : ℕ, t n ≤ t' n) →
    (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f, ∀ n : ℕ, M.time n ≤ t n) →
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f, ∀ n : ℕ, M.time n ≤ t' n := by
  rintro t t' f h ⟨M, hM⟩
  exact ⟨M, fun n => (hM n).trans (h n)⟩

/-- Reading back the vendored SAT string of a formula gives the formula. -/
theorem cnfOf_satToStr : ∀ N : cnf, SATStr.cnfOf (SATToSATStr.satToStr N) = N := fun N => by
  unfold SATStr.cnfOf
  rw [SATToSATStr.strBits_satToStr, CnfWellFormed.parseTotal_encodeCnf]

/-- The vendored SAT string encoding is injective (upstream L026 for the vendored encoding). -/
theorem satToStr_injective : Function.Injective SATToSATStr.satToStr := fun N M h => by
  rw [← cnfOf_satToStr N, ← cnfOf_satToStr M, h]



theorem h_id :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
  PvsNP.Units.m2_p_dtime_poly.id_polytime


theorem h_id2 :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (id : List Bool → List Bool) :=
  PvsNP.Units.m2_p_dtime_poly.id_polytime


theorem h_pk :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔ ∃ (k : ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ n ^ k + k :=
  PvsNP.Units.m2_p_dtime_poly.p_time_normal


theorem h_pp :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔ ∃ (p : Polynomial ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ p.eval n :=
  PvsNP.Units.m2_p_dtime_poly.p_time_poly


theorem h_mono :
    ∀ (t t' : ℕ → ℕ) (f : List Bool → Bool), (∀ n : ℕ, t n ≤ t' n) → (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f, ∀ n : ℕ, M.time n ≤ t n) → ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f, ∀ n : ℕ, M.time n ≤ t' n :=
  PvsNP.Units.m2_p_dtime_poly.time_mono


theorem h_poly :
    ∀ p : Polynomial ℕ, ∃ k : ℕ, ∀ n : ℕ, p.eval n ≤ n ^ k + k :=
  PvsNP.Units.m2_p_dtime_poly.poly_bound


theorem h_cnf :
    ∀ N : cnf, SATStr.cnfOf (SATToSATStr.satToStr N) = N :=
  PvsNP.Units.m2_p_dtime_poly.cnfOf_satToStr


end PvsNP.Units.m2_p_dtime_poly

theorem PvsNP.Units.m2_p_dtime_poly :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔
      ∃ (p : Polynomial ℕ) (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ p.eval n :=
  PvsNP.Units.m2_p_dtime_poly.h_pp
