import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_mod_all_p

/-- One step of the value-mod-`m` automaton: add the bit's contribution,
double the power of two (all mod `m`). -/
def step (m : ℕ) (hm : 0 < m) (s : Fin m × Fin m) (b : Bool) : Fin m × Fin m :=
  if b then (⟨(s.1.val + s.2.val) % m, Nat.mod_lt _ hm⟩,
      ⟨(2 * s.2.val) % m, Nat.mod_lt _ hm⟩)
  else (s.1, ⟨(2 * s.2.val) % m, Nat.mod_lt _ hm⟩)

/-- Accept when the value read so far is 0 mod `m`. -/
def accept (m : ℕ) (s : Fin m × Fin m) : Bool :=
  decide (s.1.val = 0)

/-- Folding the automaton over `x` from `(r, p)` adds `p` times the binary
value of `x` to `r`, and multiplies `p` by `2 ^ x.length` (both mod `m`). -/
theorem foldl_step (m : ℕ) (hm : 0 < m) (x : List Bool) (r p : Fin m) :
    (x.foldl (step m hm) (r, p)).1.val
        ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) [MOD m] ∧
      (x.foldl (step m hm) (r, p)).2.val ≡ p.val * 2 ^ x.length [MOD m] := by
  induction x generalizing r p with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp [Nat.ofDigits_nil]
      exact Nat.ModEq.refl _
    · simp
      exact Nat.ModEq.refl _
  | cons b xs ih =>
    cases b with
    | false =>
      show (xs.foldl (step m hm) (r, ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩)).1.val
            ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) ((false :: xs).map Bool.toNat) [MOD m] ∧
          (xs.foldl (step m hm) (r, ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩)).2.val
            ≡ p.val * 2 ^ (false :: xs).length [MOD m]
      obtain ⟨ih1, ih2⟩ := ih r ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩
      constructor
      · apply ih1.trans
        simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_false]
        have hA : (2 * p.val) % m * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            ≡ (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) [MOD m] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have h := Nat.ModEq.add_left r.val hA
        have hring : r.val + (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            = r.val + p.val * (0 + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by ring
        rw [hring] at h
        exact h
      · apply ih2.trans
        simp only [List.length_cons, pow_succ]
        have hA : (2 * p.val) % m * 2 ^ xs.length
            ≡ (2 * p.val) * 2 ^ xs.length [MOD m] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hring : (2 * p.val) * 2 ^ xs.length = p.val * (2 ^ xs.length * 2) := by ring
        rw [hring] at hA
        exact hA
    | true =>
      show (xs.foldl (step m hm)
            (⟨(r.val + p.val) % m, Nat.mod_lt _ hm⟩,
              ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩)).1.val
            ≡ r.val + p.val * Nat.ofDigits (2 : ℕ) ((true :: xs).map Bool.toNat) [MOD m] ∧
          (xs.foldl (step m hm)
            (⟨(r.val + p.val) % m, Nat.mod_lt _ hm⟩,
              ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩)).2.val
            ≡ p.val * 2 ^ (true :: xs).length [MOD m]
      obtain ⟨ih1, ih2⟩ := ih ⟨(r.val + p.val) % m, Nat.mod_lt _ hm⟩
        ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩
      constructor
      · apply ih1.trans
        simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_true]
        have hA : (2 * p.val) % m * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            ≡ (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) [MOD m] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hX : (r.val + p.val) % m ≡ r.val + p.val [MOD m] := Nat.mod_modEq _ _
        have h := hX.add hA
        have hring : (r.val + p.val) + (2 * p.val) * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
            = r.val + p.val * (1 + 2 * Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)) := by ring
        rw [hring] at h
        exact h
      · apply ih2.trans
        simp only [List.length_cons, pow_succ]
        have hA : (2 * p.val) % m * 2 ^ xs.length
            ≡ (2 * p.val) * 2 ^ xs.length [MOD m] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
        have hring : (2 * p.val) * 2 ^ xs.length = p.val * (2 ^ xs.length * 2) := by ring
        rw [hring] at hA
        exact hA

/-- The automaton accepts exactly the strings whose binary value is 0 mod `m`. -/
theorem accept_iff (m : ℕ) (hm : 0 < m) (x : List Bool) :
    accept m (x.foldl (step m hm) (⟨0, hm⟩, ⟨1 % m, Nat.mod_lt _ hm⟩)) = true ↔
      Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m = 0 := by
  obtain ⟨h1, -⟩ := foldl_step m hm x ⟨0, hm⟩ ⟨1 % m, Nat.mod_lt _ hm⟩
  simp only [Nat.zero_add] at h1
  have h1' : (x.foldl (step m hm) (⟨0, hm⟩, ⟨1 % m, Nat.mod_lt _ hm⟩)).1.val % m
      = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m := by
    have h2 : (1 % m) * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)
        ≡ Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) [MOD m] := by
      have h3 := Nat.ModEq.mul_right (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))
        (Nat.mod_modEq 1 m)
      simpa using h3
    exact h1.trans h2
  simp only [accept, decide_eq_true_eq]
  constructor
  · intro h
    rw [h] at h1'
    simpa using h1'.symm
  · intro h
    have hlt := (x.foldl (step m hm) (⟨0, hm⟩, ⟨1 % m, Nat.mod_lt _ hm⟩)).1.isLt
    rw [h] at h1'
    rwa [Nat.mod_eq_of_lt hlt] at h1'

private theorem val_mod_pos_in_p (m : ℕ) (hm : 0 < m) :
    ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m = 0} :
      Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m = 0} :
        Language Bool)
      = {x : List Bool |
        accept m (x.foldl (step m hm) (⟨0, hm⟩, ⟨1 % m, Nat.mod_lt _ hm⟩)) = true} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact (accept_iff m hm x).symm
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p (Fin m × Fin m) (step m hm)
    (⟨0, hm⟩, ⟨1 % m, Nat.mod_lt _ hm⟩) (accept m)

private theorem count_eq_in_p (r : ℕ) :
    ({x : List Bool | x.count true = r} : Language Bool) ∈ PvsNP.P := by
  let δ : Fin (r + 2) → Bool → Fin (r + 2) :=
    fun q b => if b then ⟨min (q.val + 1) (r + 1), by omega⟩ else q
  have hfold : ∀ (x : List Bool) (q : Fin (r + 2)),
      (x.foldl δ q).val = min (q.val + x.count true) (r + 1) := by
    intro x
    induction x with
    | nil =>
      intro q
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      omega
    | cons b y ih =>
      intro q
      cases b with
      | false =>
        simp only [List.foldl_cons, δ, Bool.false_eq_true, ↓reduceIte,
          List.count_cons_of_ne (by decide : false ≠ true)]
        exact ih q
      | true =>
        simp only [List.foldl_cons, δ, ↓reduceIte, List.count_cons_self]
        rw [ih]
        dsimp only
        omega
  have hdfa := PvsNP.Units.m2_dfa_in_p (Fin (r + 2)) δ ⟨0, by omega⟩ (fun q => decide (q.val = r))
  have heq : ({x : List Bool | decide ((x.foldl δ ⟨0, by omega⟩).val = r) = true} : Language Bool) =
      ({x : List Bool | x.count true = r} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, decide_eq_true_eq, hfold x ⟨0, by omega⟩, Nat.zero_add]
    omega
  rwa [← heq]

private theorem value_eq_zero_iff (x : List Bool) :
    Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 0 ↔ x.count true = 0 := by
  induction x with
  | nil => simp
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_false, Nat.zero_add,
        List.count_cons_of_ne (by decide : false ≠ true)]
      constructor
      · intro h
        have : Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat) = 0 := by omega
        exact ih.mp this
      · intro h
        have := ih.mpr h
        omega
    | true =>
      simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_true, List.count_cons_self]
      constructor <;> intro h <;> omega

private theorem val_mod_zero_in_p :
    ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 0 = 0} :
      Language Bool) ∈ PvsNP.P := by
  have heq : ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 0 = 0} :
        Language Bool)
      = ({x : List Bool | x.count true = 0} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, Nat.mod_zero]
    exact value_eq_zero_iff x
  rw [heq]
  exact count_eq_in_p 0

theorem main :
    ∀ m : ℕ, ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m = 0} :
      Language Bool) ∈ PvsNP.P := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact val_mod_zero_in_p
  · exact val_mod_pos_in_p m hm

end PvsNP.Units.tl_lang_val_mod_all_p

theorem PvsNP.Units.tl_lang_val_mod_all_p :
    ∀ m : ℕ, ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % m = 0} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_mod_all_p.main
