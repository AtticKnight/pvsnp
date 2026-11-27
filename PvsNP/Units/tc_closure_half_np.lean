import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_inv_hom_closed

/-
NP is closed under first halves. This is the settled projection unit `m2_np_projection` with the
bound p = X (witness c, |c| <= |x|) and g (x, c) = x ++ take |x| (c ++ x): the second part always has
length |x|, and equals y when c = y has length |x|. The function g is polynomial-time by iterating |x|
times the settled one-symbol step `m2_inv_hom_closed.ihStep` (with h b = [b]) through the iteration
machine `Iter.iter_polyTime` and the combinators of the settled unit `m2_np_projection`.
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_half_np

open PvsNP.Units.m2_np_projection.PEqualNP.Library
open PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime ea eb f)
    (e : ∀ a, f a = f' a) :
    PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- The singleton homomorphism. -/
def sg : Bool → List Bool := fun b => [b]

/-- g (x, c) = x ++ take |x| (c ++ x), as |x| moves of the step. -/
def halfF (p : List Bool × List Bool) : List Bool :=
  (unpairB ((PvsNP.Units.m2_inv_hom_closed.ihStep sg)^[p.1.length] (pairB (p.2 ++ p.1) p.1))).2

theorem run_take : ∀ (n : ℕ) (r o : List Bool), n ≤ r.length →
    (PvsNP.Units.m2_inv_hom_closed.ihStep sg)^[n] (pairB r o) = pairB (r.drop n) (o ++ r.take n)
  | 0, r, o, _ => by simp
  | n + 1, [], o, h => by simp at h
  | n + 1, b :: r, o, h => by
    rw [Function.iterate_succ_apply, PvsNP.Units.m2_inv_hom_closed.ihStep_pairB]
    rw [run_take n r (o ++ sg b) (by simp only [List.length_cons] at h; omega)]
    simp [sg, List.append_assoc]

theorem halfF_eq (x c : List Bool) : halfF (x, c) = x ++ (c ++ x).take x.length := by
  show (unpairB ((PvsNP.Units.m2_inv_hom_closed.ihStep sg)^[x.length] (pairB (c ++ x) x))).2 = _
  rw [run_take x.length (c ++ x) x (by simp only [List.length_append]; omega)]
  simp [unpairB_pairB]

theorem cpt_halfF :
    PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair (fun x : List Bool => x) halfF := by
  obtain ⟨c⟩ := PvsNP.Units.m2_inv_hom_closed.cpt_ihStep sg
  have hI : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => (PvsNP.Units.m2_inv_hom_closed.ihStep sg)^[q.2.length] q.1) :=
    Machines.Iter.iter_polyTime (PvsNP.Units.m2_inv_hom_closed.ihStep sg) c _
      (PvsNP.Units.m2_inv_hom_closed.ihStep_len sg)
  have hSA : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.2 ++ p.1) :=
    cptp (Machines.cpt_comp Machines.cpt_swap Machines.cpt_append) (fun _ => rfl)
  have hA : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB (p.2 ++ p.1) p.1) :=
    cptp (Machines.cpt_comp (Universal.cpt_pairG hSA Machines.cpt_fst) Universal.cpt_pairB)
      (fun _ => rfl)
  have hB : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (pairB (p.2 ++ p.1) p.1, p.1)) :=
    Universal.cpt_pairG hA Machines.cpt_fst
  exact cptp (Machines.cpt_comp (Machines.cpt_comp hB hI) Universal.cpt_unpairB2) (fun _ => rfl)

end PvsNP.Units.tc_closure_half_np

theorem PvsNP.Units.tc_closure_half_np :
∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      PvsNP.Units.tc_closure_half_np.halfF := PvsNP.Units.tc_closure_half_np.cpt_halfF
  have h := PvsNP.Units.m2_np_projection L PvsNP.Units.tc_closure_half_np.halfF
    Polynomial.X hL hg
  have e : ({x : List Bool | ∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L} : Language Bool) =
      ({x : List Bool | ∃ c : List Bool, c.length ≤ Polynomial.eval x.length Polynomial.X ∧
        PvsNP.Units.tc_closure_half_np.halfF (x, c) ∈ L} : Language Bool) := by
    apply Set.ext
    intro x
    simp only [Set.mem_setOf_eq, Polynomial.eval_X, PvsNP.Units.tc_closure_half_np.halfF_eq]
    constructor
    · rintro ⟨y, hy, hm⟩
      refine ⟨y, hy.le, ?_⟩
      have ht : (y ++ x).take y.length = y := by
        first
          | simp
          | exact List.take_left' rfl
          | simp [List.take_append]
      rw [← hy, ht]
      exact hm
    · rintro ⟨c, _, hm⟩
      refine ⟨(c ++ x).take x.length, ?_, hm⟩
      simp only [List.length_take, List.length_append]
      omega
  rw [e]
  exact h
