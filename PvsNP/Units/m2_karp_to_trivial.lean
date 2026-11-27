import Mathlib
import PvsNP.Defs
import CookLevin

/-- Only the empty language reduces to the empty language, and only the total
    language reduces to the total language: forward, the reduction's iff at `x`
    transports membership to a `False`/`True` target; backward, the identity
    machine (`Turing.idComputableInPolyTime`, as in `m2_karp_refl`) works. -/
theorem PvsNP.Units.m2_karp_to_trivial :
    ∀ L : Language Bool,
      (PvsNP.KarpReducible L ({x : List Bool | False} : Language Bool)
          ↔ ∀ x : List Bool, x ∉ L) ∧
        (PvsNP.KarpReducible L ({x : List Bool | True} : Language Bool)
          ↔ ∀ x : List Bool, x ∈ L) := by
  intro L
  constructor
  · constructor
    · rintro ⟨f, -, hiff⟩ x hx
      exact (hiff x).mp hx
    · intro h
      refine ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun x => ?_⟩
      constructor
      · intro hx
        exact absurd hx (h x)
      · intro hx
        exact absurd hx (fun h' => h')
  · constructor
    · rintro ⟨f, -, hiff⟩ x
      exact (hiff x).mpr True.intro
    · intro h
      refine ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun x => ?_⟩
      constructor
      · intro _
        exact True.intro
      · intro _
        exact h x
