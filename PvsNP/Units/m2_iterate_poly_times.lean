import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_poly_clock
import PvsNP.Units.m2_polytime_comp

/-
m2_iterate_poly_times: a polynomial-time map iterated a polynomial number of
times is polynomial-time. Pair the input with the unary clock
`1^(p(|x|))` (the settled unit m2_poly_clock, paired with the identity by the
settled cpt_pair), run the settled iteration machine
`Iter.iter_polyTime` of fr_ladner on the pair, and compose with the settled
unit m2_polytime_comp. The clock's length is `p(|x|)` by
`List.length_replicate`, so the pair-iteration is exactly `g^[p(|x|)]`.
-/

/-- A polynomial-time map iterated a polynomial number of times (TM2). -/
theorem PvsNP.Units.m2_iterate_poly_times :
    ∀ (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
        (∀ y : List Bool, (g y).length ≤ y.length + k) →
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
            (fun x : List Bool => g^[p.eval x.length] x) := by
  intro g k p hg hk
  obtain ⟨c⟩ := hg
  have hIter : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun q : List Bool × List Bool => g^[q.2.length] q.1) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.Iter.iter_polyTime g c k hk
  have hPair : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => (x, List.replicate (p.eval x.length) true)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
      (PvsNP.Units.m2_poly_clock p)
  have hComp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun q : List Bool × List Bool => g^[q.2.length] q.1) ∘
        (fun x : List Bool => (x, List.replicate (p.eval x.length) true))) :=
    PvsNP.Units.m2_polytime_comp _ _ _
      (fun x : List Bool => (x, List.replicate (p.eval x.length) true))
      (fun q : List Bool × List Bool => g^[q.2.length] q.1)
      hPair hIter
  have hEq : ((fun q : List Bool × List Bool => g^[q.2.length] q.1) ∘
        (fun x : List Bool => (x, List.replicate (p.eval x.length) true))) =
      (fun x : List Bool => g^[p.eval x.length] x) := by
    funext x
    simp [List.length_replicate]
  rw [← hEq]
  exact hComp
