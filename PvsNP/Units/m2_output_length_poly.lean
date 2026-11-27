import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- A polynomial-time function's output is polynomially long (TM2). -/
theorem PvsNP.Units.m2_output_length_poly :
    ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
      ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  intro f hf
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.output_length_poly f hf
