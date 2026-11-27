import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_reverse_closed
import PvsNP.Units.m2_np_all_prefixes

/-- NP is closed under "every suffix is in L" (TM2). -/
theorem PvsNP.Units.tc_closure_every_suffix_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∀ y : List Bool, y <:+ x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have h1 : ({z : List Bool | z.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_reverse_closed L hL
  have h2 : ({x : List Bool | ∀ y : List Bool, y <+: x → y.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_all_prefixes _ h1
  have h3 : ({x : List Bool | ∀ y : List Bool, y <+: x.reverse → y.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_reverse_closed _ h2
  have heq : ({x : List Bool | ∀ y : List Bool, y <:+ x → y ∈ L} : Language Bool) =
      ({x : List Bool | ∀ y : List Bool, y <+: x.reverse → y.reverse ∈ L} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx y hy
      apply hx y.reverse
      obtain ⟨r, hr⟩ := hy
      refine ⟨r.reverse, ?_⟩
      have hrev := congrArg List.reverse hr
      simp only [List.reverse_append, List.reverse_reverse] at hrev
      exact hrev
    · intro hx y hy
      have hpre : y.reverse <+: x.reverse := by
        obtain ⟨r, hr⟩ := hy
        refine ⟨r.reverse, ?_⟩
        have hrev := congrArg List.reverse hr
        simp only [List.reverse_append] at hrev
        exact hrev
      have hmem := hx y.reverse hpre
      rw [List.reverse_reverse] at hmem
      exact hmem
  rw [heq]
  exact h3
