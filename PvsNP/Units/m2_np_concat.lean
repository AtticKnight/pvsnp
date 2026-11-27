import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_reverse_polytime

namespace PvsNP.Units.m2_np_concat_aux

open PvsNP.Units.m2_np_projection.PEqualNP.Library
open PvsNP.Units.m2_np_projection.PEqualNP.Library.Machines
open PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem tail_iter_eq_drop {α : Type} (n : ℕ) (l : List α) :
    List.tail^[n] l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l with
    | nil => simp
    | cons a l => simp

private theorem tail_iter_isEmpty_iff {α : Type} (n : ℕ) (l : List α) :
    (List.tail^[n] l).isEmpty = true ↔ l.length ≤ n := by
  rw [tail_iter_eq_drop, List.isEmpty_iff, List.drop_eq_nil_iff]

private theorem poly_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

private theorem ne_true_run (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_isNonempty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, ne_true_run, Computability.encodeBool])

private theorem comb4 (a b c d : Bool) :
    (!(sel (if a = true then [true] else []) []
        (sel (if b = true then [true] else []) []
          (sel (if c = true then [true] else []) []
            (if d = true then [true] else [])))).isEmpty) =
      (a && b && c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [sel]

def concatV (f₁ f₂ : List Bool × List Bool → Bool) (q : List Bool × List Bool) : Bool :=
  let c₁ := (unpairB (unpairB q.2).1).1
  let c₂ := (unpairB (unpairB q.2).1).2
  let w₁ := (unpairB (unpairB q.2).2).1
  let w₂ := (unpairB (unpairB q.2).2).2
  let u := (List.tail^[c₂.length] q.1.reverse).reverse
  let v := List.tail^[c₁.length] q.1
  (List.tail^[(c₁ ++ c₂).length] q.1).isEmpty &&
    (List.tail^[q.1.length] (c₁ ++ c₂)).isEmpty &&
    f₁ (u, w₁) && f₂ (v, w₂)

theorem cpt_concatV (f₁ f₂ : List Bool × List Bool → Bool)
    (hf₁ : ComputableInPolyTime encodePair Computability.encodeBool f₁)
    (hf₂ : ComputableInPolyTime encodePair Computability.encodeBool f₂) :
    ComputableInPolyTime encodePair Computability.encodeBool (concatV f₁ f₂) := by
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hW : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hC1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).1).1) :=
    cptp (cpt_comp (cpt_comp hW cpt_unpairB1) cpt_unpairB1) (fun _ => rfl)
  have hC2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).1).2) :=
    cptp (cpt_comp (cpt_comp hW cpt_unpairB1) cpt_unpairB2) (fun _ => rfl)
  have hW1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).1) :=
    cptp (cpt_comp (cpt_comp hW cpt_unpairB2) cpt_unpairB1) (fun _ => rfl)
  have hW2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).2) :=
    cptp (cpt_comp (cpt_comp hW cpt_unpairB2) cpt_unpairB2) (fun _ => rfl)
  have hC12 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).1).1 ++
        (unpairB (unpairB (unpairB s).2).1).2) :=
    cpt_app2 hC1 hC2
  have hTailX := cpt_iterLen cpt_tail (fun l => by cases l <;> simp) hC12 hX
  have hTailC := cpt_iterLen cpt_tail (fun l => by cases l <;> simp) hX hC12
  have hRev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.reverse) := PvsNP.Units.m2_reverse_polytime
  have hU := cpt_comp (cpt_iterLen cpt_tail (fun l => by cases l <;> simp) hC2
    (cpt_comp hX hRev)) hRev
  have hV := cpt_iterLen cpt_tail (fun l => by cases l <;> simp) hC1 hX
  have fl1 := cpt_sel hTailX (cpt_const [true]) (cpt_const [])
  have fl2 := cpt_sel hTailC (cpt_const [true]) (cpt_const [])
  have fl3 := cpt_bitFlag (cpt_comp (cpt_pair hU hW1) hf₁)
  have fl4 := cpt_bitFlag (cpt_comp (cpt_pair hV hW2) hf₂)
  have all := cpt_sel fl1 (cpt_const [])
    (cpt_sel fl2 (cpt_const []) (cpt_sel fl3 (cpt_const []) fl4))
  have hS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => concatV f₁ f₂ ((unpairB s).1, (unpairB s).2)) := by
    refine cptp (cpt_comp all cpt_isNonempty) (fun s => ?_)
    have e1 : ∀ l : List Bool, sel l [true] [] = if l.isEmpty then [true] else [] := by
      intro l; cases l <;> rfl
    simp only [e1, concatV]
    exact comb4 _ _ _ _
  exact cptp (cpt_comp cpt_pairB hS) (fun q => by
    obtain ⟨x, w⟩ := q
    simp only [unpairB_pairB])

end PvsNP.Units.m2_np_concat_aux

theorem PvsNP.Units.m2_np_concat : ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
  ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.NP := by
  intro L₁ L₂ hL₁ hL₂
  obtain ⟨R₁, p₁, ⟨f₁, hf₁, c₁⟩, hbd₁, hmem₁⟩ :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.L045 L₁
      ((PvsNP.Units.m2_np_projection.NP_iff L₁).1 hL₁)
  obtain ⟨R₂, p₂, ⟨f₂, hf₂, c₂⟩, hbd₂, hmem₂⟩ :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.L045 L₂
      ((PvsNP.Units.m2_np_projection.NP_iff L₂).1 hL₂)
  refine ⟨PvsNP.Units.m2_np_concat_aux.concatV f₁ f₂,
    Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * p₁ + Polynomial.C 2 * p₂ + Polynomial.C 7,
    PvsNP.Units.m2_np_concat_aux.cpt_concatV f₁ f₂ c₁ c₂, fun x => ?_⟩
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    obtain ⟨w₁, hw₁⟩ := (hmem₁ u).1 hu
    obtain ⟨w₂, hw₂⟩ := (hmem₂ v).1 hv
    refine ⟨PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.pairB
      (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.pairB u v)
      (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.pairB w₁ w₂), ?_, ?_⟩
    · have hb₁ := (hbd₁ u w₁ hw₁).trans
        (PvsNP.Units.m2_np_concat_aux.poly_mono p₁ (Nat.le_add_right u.length v.length))
      have hb₂ := (hbd₂ v w₂ hw₂).trans
        (PvsNP.Units.m2_np_concat_aux.poly_mono p₂ (Nat.le_add_left v.length u.length))
      simp only [PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.pairB_length,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        List.length_append]
      omega
    · simp only [PvsNP.Units.m2_np_concat_aux.concatV,
        PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.unpairB_pairB,
        Bool.and_eq_true]
      have hlen₁ : (List.tail^[(u ++ v).length] (u ++ v)).isEmpty = true := by
        rw [PvsNP.Units.m2_np_concat_aux.tail_iter_isEmpty_iff]
      have hu' : (List.tail^[v.length] (u ++ v).reverse).reverse = u := by
        rw [PvsNP.Units.m2_np_concat_aux.tail_iter_eq_drop, List.reverse_append,
          List.drop_left' (by simp), List.reverse_reverse]
      have hv' : List.tail^[u.length] (u ++ v) = v := by
        rw [PvsNP.Units.m2_np_concat_aux.tail_iter_eq_drop, List.drop_left]
      rw [hlen₁, hu', hv', (hf₁ _).1 hw₁, (hf₂ _).1 hw₂]
      simp
  · rintro ⟨w, -, hw⟩
    simp only [PvsNP.Units.m2_np_concat_aux.concatV, Bool.and_eq_true] at hw
    rcases hw with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    rw [PvsNP.Units.m2_np_concat_aux.tail_iter_isEmpty_iff] at h1 h2
    set c₁ := (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.unpairB w).1).1
    set c₂ := (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.unpairB w).1).2
    have hlen : x.length = c₁.length + c₂.length := by
      simp only [List.length_append] at h1 h2
      omega
    have heq : x = (List.tail^[c₂.length] x.reverse).reverse ++ List.tail^[c₁.length] x := by
      rw [PvsNP.Units.m2_np_concat_aux.tail_iter_eq_drop,
        PvsNP.Units.m2_np_concat_aux.tail_iter_eq_drop]
      have htake : (x.reverse.drop c₂.length).reverse = x.take c₁.length := by
        rw [List.reverse_drop, List.reverse_reverse, List.length_reverse, hlen, Nat.add_sub_cancel]
      rw [htake, List.take_append_drop]
    exact ⟨_, _, heq, (hmem₁ _).2 ⟨_, (hf₁ _).2 h3⟩, (hmem₂ _).2 ⟨_, (hf₂ _).2 h4⟩⟩
