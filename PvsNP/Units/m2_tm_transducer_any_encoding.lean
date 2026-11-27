import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- A transducer run on the written input gives a polynomial-time function, whatever the finite
alphabets (TM2): `F` agrees with `fr_ladner`'s `fstRun` by induction on the input list
(generalizing the state), and `fst_polyTime` constructs the polynomial-time TM2 machine. -/
theorem PvsNP.Units.m2_tm_transducer_any_encoding :
    ∀ {α β αΓ βΓ : Type} [Fintype αΓ] (Q : Type) [Fintype Q] (ea : α → List αΓ)
      (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ)
      (fin : Q → Option βΓ) (F : Q → List αΓ → List βΓ),
      (∀ q : Q, F q [] = (fin q).toList) →
      (∀ (q : Q) (s : αΓ) (l : List αΓ), F q (s :: l) = (δ q s).2.toList ++ F (δ q s).1 l) →
      ∀ q₀ : Q, (∀ a : α, eb (f a) = F q₀ (ea a)) → PvsNP.PolyTimeComputable ea eb f := by
  intro α β αΓ βΓ _ Q _ ea eb f δ fin F h0 h1 q₀ hfa
  have hF : ∀ (q : Q) (l : List αΓ),
      F q l = PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun δ fin q l := by
    intro q l
    induction l generalizing q with
    | nil => simp [h0, PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
    | cons s l ih =>
      simp [h1, ih, PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime
    ea eb f δ fin q₀ (fun a => (hfa a).trans (hF q₀ (ea a)))
