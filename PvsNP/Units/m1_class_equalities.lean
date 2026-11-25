import Mathlib
import PvsNP.Defs
import CookLevin

/-- Bridge: given the two simulations (single-tape and multi-stack polynomial-time
computability coincide for every function), the single-tape classes are the TM2 classes.
Pure logic from the bridge hypothesis: each class is defined through
`PolyTimeComputable`, so the hypothesis rewrites every occurrence of the single-tape
notion into the multi-stack one. -/
theorem PvsNP.Units.m1_class_equalities :
    (∀ {α β A B : Type} [Finite A] [Finite B] (ea : α → List A) (eb : β → List B) (f : α → β),
      PvsNP.SingleTape.PolyTimeComputable ea eb f ↔ PvsNP.PolyTimeComputable ea eb f) →
    PvsNP.SingleTape.P = PvsNP.P ∧ PvsNP.SingleTape.NP = PvsNP.NP ∧
      PvsNP.SingleTape.coNP = PvsNP.coNP ∧
      ∀ L₁ L₂ : Language Bool,
        (PvsNP.SingleTape.KarpReducible L₁ L₂ ↔ PvsNP.KarpReducible L₁ L₂) ∧
        (PvsNP.SingleTape.NPHard L₂ ↔ PvsNP.NPHard L₂) ∧
        (PvsNP.SingleTape.NPComplete L₂ ↔ PvsNP.NPComplete L₂) := by
  intro H
  -- P: the decider is the same function, only the machine notion changes.
  have hP : PvsNP.SingleTape.P = PvsNP.P := by
    apply Set.ext
    intro L
    show PvsNP.SingleTape.PolyTimeDecidable L ↔ PvsNP.PolyTimeDecidable L
    simp only [PvsNP.SingleTape.PolyTimeDecidable, PvsNP.PolyTimeDecidable]
    constructor
    · rintro ⟨f, hf, hL⟩
      exact ⟨f, (H PvsNP.encodeString PvsNP.encodeAnswer f).mp hf, hL⟩
    · rintro ⟨f, hf, hL⟩
      exact ⟨f, (H PvsNP.encodeString PvsNP.encodeAnswer f).mpr hf, hL⟩
  -- NP: the verifier is the same function, only the machine notion changes.
  have hNP : PvsNP.SingleTape.NP = PvsNP.NP := by
    apply Set.ext
    intro L
    show (∃ V p, PvsNP.SingleTape.PolyTimeVerifier L V p) ↔
      (∃ V p, PvsNP.PolyTimeVerifier L V p)
    simp only [PvsNP.SingleTape.PolyTimeVerifier, PvsNP.PolyTimeVerifier]
    constructor
    · rintro ⟨V, p, hV, hL⟩
      exact ⟨V, p, (H PvsNP.encodePair PvsNP.encodeAnswer V).mp hV, hL⟩
    · rintro ⟨V, p, hV, hL⟩
      exact ⟨V, p, (H PvsNP.encodePair PvsNP.encodeAnswer V).mpr hV, hL⟩
  -- coNP: the complement of a language, so it follows from NP.
  have hcoNP : PvsNP.SingleTape.coNP = PvsNP.coNP := by
    apply Set.ext
    intro L
    show Lᶜ ∈ PvsNP.SingleTape.NP ↔ Lᶜ ∈ PvsNP.NP
    rw [hNP]
  -- Karp reductions: the reduction function is the same, only the machine notion changes.
  have hKarp : ∀ L₁ L₂ : Language Bool,
      PvsNP.SingleTape.KarpReducible L₁ L₂ ↔ PvsNP.KarpReducible L₁ L₂ := by
    intro L₁ L₂
    show (∃ f, PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f ∧
        ∀ x, x ∈ L₁ ↔ f x ∈ L₂) ↔
      (∃ f, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f ∧
        ∀ x, x ∈ L₁ ↔ f x ∈ L₂)
    constructor
    · rintro ⟨f, hf, hL⟩
      exact ⟨f, (H PvsNP.encodeString PvsNP.encodeString f).mp hf, hL⟩
    · rintro ⟨f, hf, hL⟩
      exact ⟨f, (H PvsNP.encodeString PvsNP.encodeString f).mpr hf, hL⟩
  -- NP-hardness: quantification over NP plus the reduction iff.
  have hHard : ∀ L₂ : Language Bool,
      PvsNP.SingleTape.NPHard L₂ ↔ PvsNP.NPHard L₂ := by
    intro L₂
    show (∀ L' ∈ PvsNP.SingleTape.NP, PvsNP.SingleTape.KarpReducible L' L₂) ↔
      (∀ L' ∈ PvsNP.NP, PvsNP.KarpReducible L' L₂)
    constructor
    · intro h L' hL'
      have hL'2 : L' ∈ PvsNP.SingleTape.NP := by rw [hNP]; exact hL'
      exact (hKarp L' L₂).mp (h L' hL'2)
    · intro h L' hL'
      have hL'2 : L' ∈ PvsNP.NP := by rw [← hNP]; exact hL'
      exact (hKarp L' L₂).mpr (h L' hL'2)
  -- NP-completeness: membership in NP plus NP-hardness.
  have hComp : ∀ L₂ : Language Bool,
      PvsNP.SingleTape.NPComplete L₂ ↔ PvsNP.NPComplete L₂ := by
    intro L₂
    show (L₂ ∈ PvsNP.SingleTape.NP ∧ PvsNP.SingleTape.NPHard L₂) ↔
      (L₂ ∈ PvsNP.NP ∧ PvsNP.NPHard L₂)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (hHard L₂).mp h2⟩
      rw [hNP] at h1
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (hHard L₂).mpr h2⟩
      rw [← hNP] at h1
      exact h1
  exact ⟨hP, hNP, hcoNP, fun L₁ L₂ => ⟨hKarp L₁ L₂, hHard L₂, hComp L₂⟩⟩
