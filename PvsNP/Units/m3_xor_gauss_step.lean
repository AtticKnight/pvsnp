import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_xor_gauss_step :
    ∀ (S : List (List var × Bool)) (e f : List var × Bool) (a : assgn),
      (∀ g ∈ e :: f :: S, decide ((g.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = g.2) ↔
        ∀ g ∈ e :: (e.1 ++ f.1, xor e.2 f.2) :: S, decide ((g.1.filter (fun v => decide (v ∈ a))).length % 2 = 1) = g.2 := by
  intro S e f a
  -- Parity of a concatenation is the xor of the parities.
  have hpar : ∀ l₁ l₂ : List var,
      decide (((l₁ ++ l₂).filter (fun v => decide (v ∈ a))).length % 2 = 1) =
        xor (decide ((l₁.filter (fun v => decide (v ∈ a))).length % 2 = 1))
          (decide ((l₂.filter (fun v => decide (v ∈ a))).length % 2 = 1)) := by
    intro l₁ l₂
    rw [List.filter_append, List.length_append]
    have hmod : ((l₁.filter (fun v => decide (v ∈ a))).length +
        (l₂.filter (fun v => decide (v ∈ a))).length) % 2 =
      (((l₁.filter (fun v => decide (v ∈ a))).length % 2 +
        (l₂.filter (fun v => decide (v ∈ a))).length % 2) % 2) :=
      Nat.add_mod _ _ 2
    rw [hmod]
    rcases Nat.mod_two_eq_zero_or_one ((l₁.filter (fun v => decide (v ∈ a))).length) with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one ((l₂.filter (fun v => decide (v ∈ a))).length) with hy | hy <;>
      simp [hx, hy]
  constructor
  · intro h
    rw [List.forall_mem_cons, List.forall_mem_cons] at h
    obtain ⟨he, hf, hS⟩ := h
    rw [List.forall_mem_cons, List.forall_mem_cons]
    refine ⟨he, ?_, hS⟩
    rw [hpar, he, hf]
  · intro h
    rw [List.forall_mem_cons, List.forall_mem_cons] at h
    obtain ⟨he, hcomb, hS⟩ := h
    rw [List.forall_mem_cons, List.forall_mem_cons]
    refine ⟨he, ?_, hS⟩
    rw [hpar, he] at hcomb
    exact Bool.xor_right_inj.mp hcomb
