import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- A finite-state transducer computes a polynomial-time function (TM2): the transducer's
output function `F` is the library's `fstRun` (by induction on the input list, generalizing
the state), and `fstRun` is polynomial-time computable by the settled unit `fr_ladner`. -/
theorem PvsNP.Units.m2_transducer_polytime : ∀ (Q : Type) [Fintype Q]
    (δ : Q → Bool → Q × Option Bool) (fin : Q → Option Bool)
    (F : Q → List Bool → List Bool),
    (∀ q : Q, F q [] = (fin q).toList) →
    (∀ (q : Q) (b : Bool) (x : List Bool),
      F q (b :: x) = (δ q b).2.toList ++ F (δ q b).1 x) →
    ∀ q₀ : Q, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (F q₀) := by
  intro Q _ δ fin F h0 h1 q₀
  have hF : ∀ (q : Q) (l : List Bool),
      F q l = PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun δ fin q l := by
    intro q l
    induction l generalizing q with
    | nil => simp [h0, PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
    | cons b x ih =>
      simp [h1, ih, PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime
    PvsNP.encodeString PvsNP.encodeString (F q₀) δ fin q₀ (fun a => hF q₀ a)
