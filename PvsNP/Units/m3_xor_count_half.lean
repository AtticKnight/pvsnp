import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_xor_count_half

private def par (vs a : List var) : Bool :=
  decide ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1)

private theorem filter_cons_not_mem (vs a : List var) (x : var) (hx : x ∉ vs) :
    vs.filter (fun v => decide (v ∈ x :: a)) = vs.filter (fun v => decide (v ∈ a)) := by
  apply List.filter_congr
  intro v hv
  have hne : v ≠ x := fun h => hx (h ▸ hv)
  simp [hne]

private theorem filter_cons_mem_len (vs a : List var) (x : var)
    (hnd : vs.Nodup) (hxvs : x ∈ vs) (hxa : x ∉ a) :
    (vs.filter (fun v => decide (v ∈ x :: a))).length =
      (vs.filter (fun v => decide (v ∈ a))).length + 1 := by
  induction vs with
  | nil => cases hxvs
  | cons y ys ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.1 hxvs with rfl | hmem
    · have hrest := filter_cons_not_mem ys a x hnd.1
      have h1 : decide (x ∈ x :: a) = true := by simp
      have h2 : decide (x ∈ a) = false := by simp [hxa]
      simp only [List.filter_cons, h1, h2, ↓reduceIte, Bool.false_eq_true, List.length_cons, hrest]
    · have hxy : y ≠ x := fun h => hnd.1 (h ▸ hmem)
      have hy : decide (y ∈ x :: a) = decide (y ∈ a) := by simp [hxy]
      simp only [List.filter_cons, hy]
      cases decide (y ∈ a) <;> simp only [↓reduceIte, Bool.false_eq_true, List.length_cons, ih hnd.2 hmem]

private theorem par_cons_not_mem (vs a : List var) (x : var) (hx : x ∉ vs) :
    par vs (x :: a) = par vs a := by
  unfold par
  rw [filter_cons_not_mem vs a x hx]

private theorem par_cons_mem (vs a : List var) (x : var)
    (hnd : vs.Nodup) (hxvs : x ∈ vs) (hxa : x ∉ a) :
    par vs (x :: a) = !(par vs a) := by
  unfold par
  rw [filter_cons_mem_len vs a x hnd hxvs hxa]
  have hmod : ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 0) ∨
      ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1) := by omega
  rcases hmod with h0 | h1
  · have h1' : ((vs.filter (fun v => decide (v ∈ a))).length + 1) % 2 = 1 := by omega
    simp [h0, h1']
  · have h0' : ((vs.filter (fun v => decide (v ∈ a))).length + 1) % 2 = 0 := by omega
    simp [h0', h1]

private theorem bool_not_beq_cases (b p : Bool) :
    ((b == p) = false ∧ ((!b) == p) = true) ∨ ((b == p) = true ∧ ((!b) == p) = false) := by
  cases b <;> cases p <;> decide

private theorem filter_bool_partition {α : Type} (l : List α) (f : α → Bool) (p : Bool) :
    (l.filter (fun a => f a == p)).length + (l.filter (fun a => ((!f a) == p))).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases bool_not_beq_cases (f a) p with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp only [List.filter_cons, h, h', ↓reduceIte, Bool.false_eq_true, List.length_cons]
      omega
    · simp only [List.filter_cons, h, h', ↓reduceIte, Bool.false_eq_true, List.length_cons]
      omega

private theorem filter_sublists_cons {α : Type} (x : α) (L : List α) (q : List α → Bool) :
    ((x :: L).sublists.filter q).length =
      (L.sublists.filter q).length + (L.sublists.filter (fun s => q (x :: s))).length := by
  rw [List.sublists_cons]
  change ((L.sublists.flatMap (fun s => [s, x :: s])).filter q).length = _
  rw [List.filter_flatMap, List.length_flatMap]
  induction L.sublists with
  | nil => simp
  | cons s ss ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons, List.filter_cons,
      List.filter_cons, List.filter_cons, List.filter_nil]
    by_cases h1 : q s = true <;> by_cases h2 : q (x :: s) = true
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      simp only [List.length_cons, List.length_nil]
      omega

private theorem sublists_filter_count (vs : List var) (hnd_vs : vs.Nodup) :
    ∀ (L : List var) (p : Bool), L.Nodup → (∃ v ∈ vs, v ∈ L) →
      (L.sublists.filter (fun a => par vs a == p)).length = 2 ^ (L.length - 1) := by
  intro L
  induction L with
  | nil =>
    intro p _ ⟨v, _, hv⟩
    cases hv
  | cons x L' ih =>
    intro p hndL ⟨v₀, hv₀vs, hv₀L⟩
    rw [List.nodup_cons] at hndL
    rw [filter_sublists_cons]
    simp only [List.length_cons, Nat.add_sub_cancel]
    have hnotmem : ∀ a ∈ L'.sublists, x ∉ a := by
      intro a ha hxa
      exact hndL.1 (List.Sublist.subset (List.mem_sublists.1 ha) hxa)
    by_cases hxv : x ∈ vs
    · have hmap : L'.sublists.filter (fun s => par vs (x :: s) == p) =
          L'.sublists.filter (fun a => (!(par vs a)) == p) := by
        apply List.filter_congr
        intro a ha
        simp only [par_cons_mem vs a x hnd_vs hxv (hnotmem a ha)]
      rw [hmap]
      by_cases hex : ∃ v ∈ vs, v ∈ L'
      · have h1 := ih p hndL.2 hex
        have h2 := ih (!p) hndL.2 hex
        have heq2 : L'.sublists.filter (fun a => (!(par vs a)) == p) =
            L'.sublists.filter (fun a => par vs a == !p) := by
          apply List.filter_congr
          intro a _
          cases par vs a <;> cases p <;> rfl
        rw [heq2, h1, h2]
        have hpos : 1 ≤ L'.length := by
          obtain ⟨v, _, hvL'⟩ := hex
          cases L' with
          | nil => cases hvL'
          | cons _ _ => simp
        have hpow : 2 ^ (L'.length - 1) + 2 ^ (L'.length - 1) = 2 ^ L'.length := by
          have : L'.length = (L'.length - 1) + 1 := by omega
          conv_rhs => rw [this, pow_succ]
          omega
        exact hpow
      · rw [filter_bool_partition, List.length_sublists]
    · rcases List.mem_cons.1 hv₀L with rfl | hv₀L'
      · exact absurd hv₀vs hxv
      · have hex : ∃ v ∈ vs, v ∈ L' := ⟨v₀, hv₀vs, hv₀L'⟩
        have hmap : L'.sublists.filter (fun s => par vs (x :: s) == p) =
            L'.sublists.filter (fun a => par vs a == p) := by
          apply List.filter_congr
          intro a _
          simp only [par_cons_not_mem vs a x hxv]
        rw [hmap, ih p hndL.2 hex]
        have hpos : 1 ≤ L'.length := by
          cases L' with
          | nil => cases hv₀L'
          | cons _ _ => simp
        have : L'.length = (L'.length - 1) + 1 := by omega
        conv_rhs => rw [this, pow_succ]
        omega

theorem main :
    ∀ (n : ℕ) (vs : List var) (p : Bool), vs ≠ [] → vs.Nodup → (∀ v ∈ vs, v < n) →
      ((List.range n).sublists.filter
          (fun a => decide ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1) == p)).length =
        2 ^ (n - 1) := by
  intro n vs p hne hnd hlt
  cases vs with
  | nil => exact absurd rfl hne
  | cons v₀ vs' =>
    have hv₀ : v₀ ∈ List.range n := List.mem_range.2 (hlt v₀ (List.mem_cons_self))
    have h := sublists_filter_count (v₀ :: vs') hnd (List.range n) p List.nodup_range
      ⟨v₀, List.mem_cons_self, hv₀⟩
    simpa [par, List.length_range] using h

end PvsNP.Units.m3_xor_count_half

theorem PvsNP.Units.m3_xor_count_half :
    ∀ (n : ℕ) (vs : List var) (p : Bool), vs ≠ [] → vs.Nodup → (∀ v ∈ vs, v < n) →
      ((List.range n).sublists.filter
          (fun a => decide ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1) == p)).length =
        2 ^ (n - 1) :=
  PvsNP.Units.m3_xor_count_half.main
