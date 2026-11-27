import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_interleave

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def headBit (l : List Bool) : List Bool :=
  sel l [] (sel (hd l) [false] [true])

lemma headBit_cons (b : Bool) (l : List Bool) : headBit (b :: l) = [b] := by
  cases b <;> simp [headBit, hd, sel]

lemma headBit_len (l : List Bool) : (headBit l).length ≤ 1 := by
  unfold headBit sel
  split_ifs <;> simp

def zipStep (s : List Bool) : List Bool :=
  let uv := (unpairB s).1
  let out := (unpairB s).2
  let u := (unpairB uv).1
  let v := (unpairB uv).2
  pairB (pairB u.tail v.tail) (out ++ (headBit u ++ headBit v))

lemma zipStep_pairB (a b : Bool) (u v out : List Bool) :
    zipStep (pairB (pairB (a :: u) (b :: v)) out) =
      pairB (pairB u v) (out ++ [a, b]) := by
  simp only [zipStep, unpairB_pairB, List.tail_cons, headBit_cons, List.cons_append, List.nil_append]

lemma zipStep_iter :
    ∀ (u v out : List Bool), u.length ≤ v.length →
      (unpairB (zipStep^[u.length] (pairB (pairB u v) out))).2 =
        out ++ (List.zipWith (fun a b => [a, b]) u v).flatten
  | [], v, out, _ => by simp [unpairB_pairB]
  | a :: u, [], _, h => by simp at h
  | a :: u, b :: v, out, h => by
    have h' : u.length ≤ v.length := by
      simp only [List.length_cons] at h
      omega
    rw [List.length_cons, Function.iterate_succ_apply, zipStep_pairB,
      zipStep_iter u v (out ++ [a, b]) h']
    simp [List.zipWith_cons_cons, List.append_assoc]

lemma zipStep_len (s : List Bool) : (zipStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have ha := headBit_len (unpairB (unpairB s).1).1
  have hb := headBit_len (unpairB (unpairB s).1).2
  simp only [zipStep, pairB_length, List.length_append, List.length_tail]
  omega

lemma cpt_headBit {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => headBit (f s)) :=
  cptp (cpt_sel hf (cpt_const []) (cpt_sel (cpt_hd1 hf) (cpt_const [false]) (cpt_const [true])))
    (fun _ => rfl)

lemma cpt_zipStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) zipStep := by
  have hUV : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hOut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).1).1) :=
    cptp (cpt_comp hUV cpt_unpairB1) (fun _ => rfl)
  have hV : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).1).2) :=
    cptp (cpt_comp hUV cpt_unpairB2) (fun _ => rfl)
  have hNewUV := cpt_pairB2 (cpt_tail1 hU) (cpt_tail1 hV)
  have hNewOut := cpt_app2 hOut (cpt_app2 (cpt_headBit hU) (cpt_headBit hV))
  exact cptp (cpt_pairB2 hNewUV hNewOut) (fun _ => rfl)

lemma unpairB_half_cons (x : List Bool) :
    unpairB (half x ++ false :: x) = (x.take (x.length / 2), x.drop (x.length / 2)) := by
  rw [half_eq]
  simp [unpairB, un]

lemma half_cons_eq_pairB (x : List Bool) :
    half x ++ false :: x = pairB (x.take (x.length / 2)) (x.drop (x.length / 2)) := by
  rw [half_eq, pairB, List.length_take, Nat.min_eq_left (Nat.div_le_self x.length 2),
    List.take_append_drop]

end PvsNP.Units.tf_fun_interleave

theorem PvsNP.Units.tf_fun_interleave :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        (List.zipWith (fun a b => [a, b]) (x.take (x.length / 2)) (x.drop (x.length / 2))).flatten) := by
  open PvsNP.Units.fr_ladner.PEqualNP.Library in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner in
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => pairB (half x ++ false :: x) []) :=
    cpt_pairB2 hCut (cpt_const [])
  have hRun := cpt_iterGrow PvsNP.Units.tf_fun_interleave.cpt_zipStep 5
    PvsNP.Units.tf_fun_interleave.zipStep_len cpt_half hInit
  have hOut := cpt_comp hRun cpt_unpairB2
  have heq :
      (fun x : List Bool =>
        (unpairB (PvsNP.Units.tf_fun_interleave.zipStep^[(half x).length]
          (pairB (half x ++ false :: x) []))).2) =
      (fun x : List Bool =>
        (List.zipWith (fun a b => [a, b]) (x.take (x.length / 2)) (x.drop (x.length / 2))).flatten) := by
    funext x
    rw [PvsNP.Units.tf_fun_interleave.half_cons_eq_pairB x, half_eq, un_length]
    have hlen : x.length / 2 = (x.take (x.length / 2)).length := by
      rw [List.length_take, Nat.min_eq_left (Nat.div_le_self x.length 2)]
    have hle : (x.take (x.length / 2)).length ≤ (x.drop (x.length / 2)).length := by
      simp only [List.length_take, List.length_drop]
      omega
    have hz := PvsNP.Units.tf_fun_interleave.zipStep_iter
      (x.take (x.length / 2)) (x.drop (x.length / 2)) [] hle
    rw [← hlen, List.nil_append] at hz
    exact hz
  rw [← heq]
  exact hOut
