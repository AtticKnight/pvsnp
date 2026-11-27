import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.fr_ladner

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

namespace PvsNP.Units.tc_closure_rev_factor_np

/-- Conversion along a pointwise equality (the private `cptc` of `fr_ladner`). -/
theorem conv {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- The `x` half of a `pairB`-packed input. -/
def getX (s : List Bool) : List Bool := (unpairB s).1

/-- The certificate half of a `pairB`-packed input. -/
def getC (s : List Bool) : List Bool := (unpairB s).2

/-- The first cut (unary `i`) of the packed certificate. -/
def cutA (s : List Bool) : List Bool := (unpairB (getC s)).1

/-- The second cut (unary `j`) of the packed certificate. -/
def cutB (s : List Bool) : List Bool := (unpairB (getC s)).2

/-- The prefix before the reversed factor. -/
def takePart (s : List Bool) : List Bool := (getX s).take (cutA s).length

/-- The suffix starting at the reversed factor. -/
def dropPart (s : List Bool) : List Bool := (getX s).drop (cutA s).length

/-- The reversed factor. -/
def revPart (s : List Bool) : List Bool := ((dropPart s).take (cutB s).length).reverse

/-- The suffix after the reversed factor. -/
def restPart (s : List Bool) : List Bool := (getX s).drop ((cutA s ++ cutB s).length)

/-- Reversing the factor of `x` delimited by the packed certificate. -/
def revFactorS (s : List Bool) : List Bool := takePart s ++ revPart s ++ restPart s

/-- The two-argument version: reverse a factor of `x` as delimited by `c`. -/
def revFactor (p : List Bool × List Bool) : List Bool := revFactorS (pairB p.1 p.2)

/-- Take by the length of the first component (settled unit, read at the library level). -/
theorem takeLen_lib : ComputableInPolyTime encodePair (fun x : List Bool => x)
    (fun p : List Bool × List Bool => p.2.take p.1.length) :=
  PvsNP.Units.m2_take_drop_length_polytime.1

/-- Drop by the length of the first component (settled unit, read at the library level). -/
theorem dropLen_lib : ComputableInPolyTime encodePair (fun x : List Bool => x)
    (fun p : List Bool × List Bool => p.2.drop p.1.length) :=
  PvsNP.Units.m2_take_drop_length_polytime.2

/-- Whole-string reversal is polynomial-time (settled unit, read at the library level). -/
theorem rev_lib : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x.reverse) :=
  PvsNP.Units.m2_reverse_polytime

theorem getX_poly : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    getX :=
  cpt_unpairB1

theorem getC_poly : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    getC :=
  cpt_unpairB2

theorem cutA_poly : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    cutA := by
  exact conv (cpt_comp getC_poly cpt_unpairB1) (fun s => rfl)

theorem cutB_poly : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    cutB := by
  exact conv (cpt_comp getC_poly cpt_unpairB2) (fun s => rfl)

theorem takePart_poly : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) takePart := by
  have hpair : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s : List Bool => (cutA s, getX s)) :=
    cpt_pair cutA_poly getX_poly
  exact conv (cpt_comp hpair takeLen_lib) (fun s => rfl)

theorem dropPart_poly : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) dropPart := by
  have hpair : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s : List Bool => (cutA s, getX s)) :=
    cpt_pair cutA_poly getX_poly
  exact conv (cpt_comp hpair dropLen_lib) (fun s => rfl)

theorem revPart_poly : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) revPart := by
  have hpair : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s : List Bool => (cutB s, dropPart s)) :=
    cpt_pair cutB_poly dropPart_poly
  have htake : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (dropPart s).take (cutB s).length) :=
    conv (cpt_comp hpair takeLen_lib) (fun s => rfl)
  exact conv (cpt_comp htake rev_lib) (fun s => rfl)

theorem restPart_poly : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) restPart := by
  have hab : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => cutA s ++ cutB s) :=
    cpt_app2 cutA_poly cutB_poly
  have hpair : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun s : List Bool => (cutA s ++ cutB s, getX s)) :=
    cpt_pair hab getX_poly
  exact conv (cpt_comp hpair dropLen_lib) (fun s => rfl)

theorem revFactorS_poly : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) revFactorS := by
  have h12 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => takePart s ++ revPart s) :=
    cpt_app2 takePart_poly revPart_poly
  exact conv (cpt_app2 h12 restPart_poly) (fun s => rfl)

theorem revFactor_poly_lib : ComputableInPolyTime encodePair (fun x : List Bool => x)
    revFactor := by
  have hPB : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) :=
    cpt_pairB
  exact conv (cpt_comp hPB revFactorS_poly) (fun p => rfl)

theorem revFactor_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    revFactor :=
  revFactor_poly_lib

end PvsNP.Units.tc_closure_rev_factor_np

/-- NP is closed under reversing a factor: the certificate is the two cut points
(encoded as the unary strings `u`, `v` themselves, packed with `pairB`), and the
verifier is the bounded projection of `L` along the polynomial-time map `revFactor`. -/
theorem PvsNP.Units.tc_closure_rev_factor_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} :
        Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have hp : ∀ n : ℕ, (Polynomial.C 2 * Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval n
      = 2 * n + 1 := by
    intro n
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have heq : ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧
        u ++ v.reverse ++ w ∈ L} : Language Bool)
      = {x : List Bool | ∃ c : List Bool,
          c.length ≤ (Polynomial.C 2 * Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval x.length ∧
            PvsNP.Units.tc_closure_rev_factor_np.revFactor (x, c) ∈ L} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, w, rfl, hmem⟩
      refine ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB u v, ?_, ?_⟩
      · rw [hp, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB_length]
        simp only [List.length_append]
        omega
      · have ht : (u ++ v ++ w).take u.length = u := by simp
        have hd : (u ++ v ++ w).drop u.length = v ++ w := by simp
        have htv : (v ++ w).take v.length = v := by simp
        have hdw : (u ++ v ++ w).drop (u.length + v.length) = w := by simp
        have hrev : PvsNP.Units.tc_closure_rev_factor_np.revFactor (u ++ v ++ w,
            PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB u v)
            = u ++ v.reverse ++ w := by
          simp only [PvsNP.Units.tc_closure_rev_factor_np.revFactor,
            PvsNP.Units.tc_closure_rev_factor_np.revFactorS,
            PvsNP.Units.tc_closure_rev_factor_np.takePart,
            PvsNP.Units.tc_closure_rev_factor_np.revPart,
            PvsNP.Units.tc_closure_rev_factor_np.restPart,
            PvsNP.Units.tc_closure_rev_factor_np.dropPart,
            PvsNP.Units.tc_closure_rev_factor_np.getX,
            PvsNP.Units.tc_closure_rev_factor_np.cutA,
            PvsNP.Units.tc_closure_rev_factor_np.cutB,
            PvsNP.Units.tc_closure_rev_factor_np.getC,
            PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
            List.length_append, ht, hd, htv, hdw]
        rw [hrev]
        exact hmem
    · rintro ⟨c, _hc, hmem⟩
      have h1 : (x.drop (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length).take
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length
          = (x.take ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length)).drop
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length := by
        rw [List.drop_take, Nat.add_sub_cancel_left]
      have h2 : x.take (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
          ++ (x.take ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length)).drop
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
          = x.take ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length) := by
        have h := List.take_append_drop
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
          (x.take ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length))
        rwa [List.take_take, Nat.min_eq_left (Nat.le_add_right
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length)] at h
      have hxu : x.take (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
          ++ (x.drop (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length).take
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length
          ++ x.drop ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length) = x := by
        rw [h1, h2]
        exact List.take_append_drop _ x
      have hrev : PvsNP.Units.tc_closure_rev_factor_np.revFactor (x, c)
          = x.take (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length
            ++ ((x.drop (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length).take
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length).reverse
            ++ x.drop ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length) := by
        simp only [PvsNP.Units.tc_closure_rev_factor_np.revFactor,
          PvsNP.Units.tc_closure_rev_factor_np.revFactorS,
          PvsNP.Units.tc_closure_rev_factor_np.takePart,
          PvsNP.Units.tc_closure_rev_factor_np.revPart,
          PvsNP.Units.tc_closure_rev_factor_np.restPart,
          PvsNP.Units.tc_closure_rev_factor_np.dropPart,
          PvsNP.Units.tc_closure_rev_factor_np.getX,
          PvsNP.Units.tc_closure_rev_factor_np.cutA,
          PvsNP.Units.tc_closure_rev_factor_np.cutB,
          PvsNP.Units.tc_closure_rev_factor_np.getC,
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
          List.length_append]
      refine ⟨x.take (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length,
        (x.drop (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length).take
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length,
        x.drop ((PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).1.length +
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB c).2.length),
        hxu.symm, ?_⟩
      rw [← hrev]
      exact hmem
  rw [heq]
  exact PvsNP.Units.m2_np_projection L
    PvsNP.Units.tc_closure_rev_factor_np.revFactor
    (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) hL
    PvsNP.Units.tc_closure_rev_factor_np.revFactor_poly
