import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.m2_x_karp_prepend_true

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library

/-- Strip a leading `true`; anything else goes to the fixed non-member `z`. -/
def strip (z : List Bool) : List Bool → List Bool :=
  fun x => sel (hd x) z x.tail

theorem strip_nil (z : List Bool) : strip z [] = z := by
  simp [strip, sel, hd]

theorem strip_false (z y : List Bool) : strip z (false :: y) = z := by
  simp [strip, sel, hd]

theorem strip_true (z y : List Bool) : strip z (true :: y) = y := by
  simp [strip, sel, hd]

theorem strip_polyTime (z : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (strip z) :=
  cpt_sel cpt_hd (cpt_const z) cpt_tail

theorem cons_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => true :: x) :=
  cpt_app2 (cpt_const [true]) cpt_id

end PvsNP.Units.m2_x_karp_prepend_true

theorem PvsNP.Units.m2_x_karp_prepend_true :
    ∀ L : Language Bool, (∃ z : List Bool, z ∉ L) →
      PvsNP.KarpReducible L ({x : List Bool | ∃ y ∈ L, x = true :: y} : Language Bool) ∧
        PvsNP.KarpReducible ({x : List Bool | ∃ y ∈ L, x = true :: y} : Language Bool) L := by
  intro L ⟨z, hz⟩
  refine ⟨⟨fun x => true :: x, PvsNP.Units.m2_x_karp_prepend_true.cons_polyTime, fun x => ?_⟩,
    ⟨PvsNP.Units.m2_x_karp_prepend_true.strip z,
      PvsNP.Units.m2_x_karp_prepend_true.strip_polyTime z, fun x => ?_⟩⟩
  · show x ∈ L ↔ ∃ y ∈ L, true :: x = true :: y
    simp
  · cases x with
    | nil =>
      rw [PvsNP.Units.m2_x_karp_prepend_true.strip_nil]
      constructor
      · rintro ⟨y, _, h⟩; cases h
      · intro h; exact absurd h hz
    | cons b y =>
      cases b with
      | false =>
        rw [PvsNP.Units.m2_x_karp_prepend_true.strip_false]
        constructor
        · rintro ⟨y', _, h⟩; cases h
        · intro h; exact absurd h hz
      | true =>
        rw [PvsNP.Units.m2_x_karp_prepend_true.strip_true]
        show (∃ y' ∈ L, true :: y = true :: y') ↔ y ∈ L
        simp
