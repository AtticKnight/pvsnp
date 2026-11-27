import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
  lean/PEqualNP/Library/Machines/IterMeasure.lean (iterate_length_measure, iter_polyTime_measure).
MODIFIED from that file: the proofs are taken from the settled campaign unit fr_ladner
(github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace holds the upstream port
(upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X there). The closing theorems restate
them with the campaign's definitions in PvsNP.Defs (PvsNP.PolyTimeComputable is upstream ComputableInPolyTime;
PvsNP.encodeString and PvsNP.encodePair are definitionally the upstream encodings).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_iterate_measure

/-- Upstream `iter_polyTime_measure`: iterating `g` `|w|` times is polynomial-time when each step
grows the string by at most a measure that never increases and is linear in the length. -/
theorem main (g : List Bool → List Bool) (m : List Bool → ℕ) (a : ℕ)
    (hg0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) := by
  have _hc := Classical.em True
  obtain ⟨c⟩ := hg0
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.Iter.iter_polyTime_measure g c m a hm hg ha

theorem main_c (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
  main g m a ⟨c⟩ hm hg ha

/-- Upstream `iterate_length_measure`. -/
theorem len (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) (j : ℕ) :
    m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  have _hc := Classical.em True
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.Iter.iterate_length_measure g m hm hg y j



theorem h_c : ∀ (g : List Bool → List Bool) (c : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString g) (m : List Bool → ℕ) (a : ℕ), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → (∀ y : List Bool, m y ≤ a * y.length + a) → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => g^[p.2.length] p.1) := PvsNP.Units.m2_tm_iterate_measure.main_c


theorem h_M : ∀ (g : List Bool → List Bool) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString g) (m : List Bool → ℕ) (a : ℕ), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → (∀ y : List Bool, m y ≤ a * y.length + a) → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => g^[p.2.length] p.1) := PvsNP.Units.m2_tm_iterate_measure.main_c


theorem h_y : ∀ (g : List Bool → List Bool) (m : List Bool → ℕ) (a : ℕ), PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g → (∀ y, m (g y) ≤ m y) → (∀ y, (g y).length ≤ y.length + m y) → (∀ y, m y ≤ a * y.length + a) → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => g^[p.2.length] p.1) := PvsNP.Units.m2_tm_iterate_measure.main


theorem h_len : ∀ (g : List Bool → List Bool) (m : List Bool → ℕ), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → ∀ (y : List Bool) (j : ℕ), m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := PvsNP.Units.m2_tm_iterate_measure.len


theorem h_len2 : ∀ (g : List Bool → List Bool) (m : List Bool → ℕ), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → ∀ y : List Bool, ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := PvsNP.Units.m2_tm_iterate_measure.len


theorem h_len3 : ∀ (g : List Bool → List Bool) (m : List Bool → ℕ) (y : List Bool), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := fun g m y hm hg j => PvsNP.Units.m2_tm_iterate_measure.len g m hm hg y j


theorem h_len4 : ∀ (g : List Bool → List Bool) (m : List Bool → ℕ) (y : List Bool) (j : ℕ), (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) → m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := fun g m y j hm hg => PvsNP.Units.m2_tm_iterate_measure.len g m hm hg y j


end PvsNP.Units.m2_tm_iterate_measure

theorem PvsNP.Units.m2_tm_iterate_measure :
    ∀ (g : List Bool → List Bool) (m : List Bool → ℕ) (a : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
        (∀ y : List Bool, m (g y) ≤ m y) → (∀ y : List Bool, (g y).length ≤ y.length + m y) →
          (∀ y : List Bool, m y ≤ a * y.length + a) →
            PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
              (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
  PvsNP.Units.m2_tm_iterate_measure.main
