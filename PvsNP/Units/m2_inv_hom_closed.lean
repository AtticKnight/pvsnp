import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed

/-
P and NP are closed under inverse homomorphisms: x ↦ x.flatMap h is polynomial-time (iterate
|x| times the step pairB r o ↦ pairB r.tail (o ++ h r.head), built from the combinators and the
iteration machine Iter.iter_polyTime of the settled unit m2_np_projection), then the settled
m2_p_down_closed and m2_np_down_closed.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_inv_hom_closed

open PvsNP.Units.m2_np_projection.PEqualNP.Library.Machines
open PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime ea eb f)
    (e : ∀ a, f a = f' a) :
    PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- The image of the first symbol of `r` (empty when `r` is empty). -/
def ihPiece (h : Bool → List Bool) (r : List Bool) : List Bool :=
  sel r [] (sel (hd r) (h false) (h true))

/-- One step: move the first symbol of the rest to the output, through `h`. -/
def ihStep (h : Bool → List Bool) (s : List Bool) : List Bool :=
  pairB (unpairB s).1.tail ((unpairB s).2 ++ ihPiece h (unpairB s).1)

theorem ihPiece_cons (h : Bool → List Bool) (b : Bool) (r : List Bool) :
    ihPiece h (b :: r) = h b := by
  cases b <;> simp [ihPiece, sel, hd]

theorem ihStep_pairB (h : Bool → List Bool) (b : Bool) (r o : List Bool) :
    ihStep h (pairB (b :: r) o) = pairB r (o ++ h b) := by
  simp only [ihStep, unpairB_pairB, List.tail_cons, ihPiece_cons]

theorem ih_run (h : Bool → List Bool) :
    ∀ (r o : List Bool), (ihStep h)^[r.length] (pairB r o) = pairB [] (o ++ r.flatMap h)
  | [], o => by simp
  | b :: r, o => by
    rw [List.length_cons, Function.iterate_succ_apply, ihStep_pairB, ih_run h r]
    simp [List.append_assoc]

theorem ihStep_len (h : Bool → List Bool) (s : List Bool) :
    (ihStep h s).length ≤ s.length + ((h false).length + (h true).length + 1) := by
  have h1 := unpairB_length s
  have h2 : (ihPiece h (unpairB s).1).length ≤ (h false).length + (h true).length := by
    unfold ihPiece sel
    split_ifs <;> first | omega | simp
  simp only [ihStep, pairB_length, List.length_append, List.length_tail]
  omega

theorem cpt_ihStep (h : Bool → List Bool) :
    PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (ihStep h) := by
  have hR : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).1) := cpt_unpairB1
  have hO : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).2) := cpt_unpairB2
  have hRt := cpt_comp hR cpt_tail
  have hHd := cpt_comp hR cpt_hd
  have hP := cpt_sel hR (cpt_const []) (cpt_sel hHd (cpt_const (h false)) (cpt_const (h true)))
  have hO' := cpt_app2 hO hP
  exact cptp (cpt_pairB2 hRt hO') (fun _ => rfl)

theorem cpt_flatMap (h : Bool → List Bool) :
    PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x.flatMap h) := by
  obtain ⟨c⟩ := cpt_ihStep h
  have hI : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.m2_np_projection.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => (ihStep h)^[p.2.length] p.1) :=
    Iter.iter_polyTime (ihStep h) c _ (ihStep_len h)
  have hP0 : PvsNP.Units.m2_np_projection.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun x => pairB x []) :=
    cptp (cpt_pairB2 cpt_id (cpt_const [])) (fun _ => rfl)
  have hIn := cpt_pair hP0 cpt_id
  have hAll := cpt_comp (cpt_comp hIn hI) cpt_unpairB2
  refine cptp hAll (fun x => ?_)
  show (unpairB ((ihStep h)^[x.length] (pairB x []))).2 = x.flatMap h
  rw [ih_run h x []]
  simp [unpairB_pairB]

end PvsNP.Units.m2_inv_hom_closed

theorem PvsNP.Units.m2_inv_hom_closed :
∀ (h : Bool → List Bool) (L : Language Bool),
  (L ∈ PvsNP.P → ({x : List Bool | x.flatMap h ∈ L} : Language Bool) ∈ PvsNP.P) ∧
    (L ∈ PvsNP.NP → ({x : List Bool | x.flatMap h ∈ L} : Language Bool) ∈ PvsNP.NP) := by
  intro h L
  have hF : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.flatMap h) := PvsNP.Units.m2_inv_hom_closed.cpt_flatMap h
  constructor
  · intro hL
    exact PvsNP.Units.m2_p_down_closed _ L ⟨fun x : List Bool => x.flatMap h, hF, fun _ => Iff.rfl⟩ hL
  · intro hL
    exact PvsNP.Units.m2_np_down_closed _ L ⟨fun x : List Bool => x.flatMap h, hF, fun _ => Iff.rfl⟩ hL
