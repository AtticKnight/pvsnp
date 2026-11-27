import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_xor_affine_closure

open CookLevin

theorem parity3 (A B C : var → Bool) (vs : List var) :
    ((vs.filter (fun v => xor (xor (A v) (B v)) (C v))).length) % 2 =
      ((vs.filter A).length + (vs.filter B).length + (vs.filter C).length) % 2 := by
  induction vs with
  | nil => simp
  | cons x xs ih =>
    cases hA : A x <;> cases hB : B x <;> cases hC : C x <;>
      simp [hA, hB, hC] at ih ⊢ <;> omega

end PvsNP.Units.m3_xor_affine_closure

theorem PvsNP.Units.m3_xor_affine_closure :
    ∀ (S : List (List var × Bool)) (a b c : assgn),
      (∀ e ∈ S, decide ((e.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = e.2) →
      (∀ e ∈ S, decide ((e.1.filter (fun v => decide (v ∈ b))).length % 2 = 1) = e.2) →
      (∀ e ∈ S, decide ((e.1.filter (fun v => decide (v ∈ c))).length % 2 = 1) = e.2) →
      ∀ e ∈ S, decide ((e.1.filter (fun v => xor (xor (decide (v ∈ a)) (decide (v ∈ b))) (decide (v ∈ c)))).length % 2 = 1) = e.2 := by
  intro S a b c ha hb hc e he
  have h1 := ha e he
  have h2 := hb e he
  have h3 := hc e he
  have hp := PvsNP.Units.m3_xor_affine_closure.parity3 (fun v => decide (v ∈ a)) (fun v => decide (v ∈ b)) (fun v => decide (v ∈ c)) e.1
  rw [← h1] at h3 h2 ⊢
  generalize e.2 = p at *
  simp only [decide_eq_decide] at *
  omega
