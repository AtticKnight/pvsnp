import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_linear_clock

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_transducer2_time

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem F_eq (Q : Type) (δ : Q → Bool → Q × Option Bool × Option Bool) (fin : Q → Option Bool)
    (F : Q → List Bool → List Bool) (h0 : ∀ q : Q, F q [] = (fin q).toList)
    (h1 : ∀ (q : Q) (b : Bool) (x : List Bool),
      F q (b :: x) = (δ q b).2.1.toList ++ (δ q b).2.2.toList ++ F (δ q b).1 x) :
    ∀ (x : List Bool) (q : Q), F q x = fstRun2 δ fin q x := by
  intro x
  induction x with
  | nil => intro q; rw [h0]; rfl
  | cons b l ih => intro q; rw [h1, ih]; rfl

end PvsNP.Units.m2_tm_transducer2_time

theorem PvsNP.Units.m2_tm_transducer2_time : ∀ (Q : Type) [Fintype Q] (δ : Q → Bool → Q × Option Bool × Option Bool) (fin : Q → Option Bool)
    (F : Q → List Bool → List Bool),
  (∀ q : Q, F q [] = (fin q).toList) →
    (∀ (q : Q) (b : Bool) (x : List Bool), F q (b :: x) = (δ q b).2.1.toList ++ (δ q b).2.2.toList ++ F (δ q b).1 x) →
      ∀ q₀ : Q, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (F q₀),
        ∀ n : ℕ, M.time n ≤ 2 * n + 3 := by
  intro Q _ δ fin F h0 h1 q₀
  exact PvsNP.Units.m2_linear_clock.fst2_time PvsNP.encodeString PvsNP.encodeString (F q₀) δ fin q₀
    (fun a => PvsNP.Units.m2_tm_transducer2_time.F_eq Q δ fin F h0 h1 a q₀)
