import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

namespace PvsNP.Units.m2_unary_pad_np

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def upPadA (s : List Bool) : List Bool := dropN (s ++ [false])

theorem up_hd_split (s : List Bool) : upPadA s = [] ∨ s = hd s ++ false :: dropN s := by
  induction s with
  | nil => left; simp [upPadA, dropN]
  | cons b r ih =>
    cases b
    · right; simp [hd, dropN]
    · have h1 : hd (true :: r) = true :: hd r := by simp [hd]
      have h2 : dropN (true :: r) = dropN r := by simp [dropN]
      rcases ih with h | h
      · left
        have h3 : upPadA (true :: r) = upPadA r := by simp [upPadA, dropN]
        rw [h3]; exact h
      · right
        rw [h1, h2]
        exact congrArg (List.cons true) h

theorem up_hd_eq_un (s : List Bool) : hd s = un (hd s).length :=
  un_length_eq _ (fun b hb => by
    have hall : ∀ l : List Bool, ∀ b ∈ l.takeWhile id, b = true := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        cases a
        · simp
        · intro b hb
          simp only [List.takeWhile_cons, id, ite_true, List.mem_cons] at hb
          rcases hb with hb | hb
          · exact hb
          · exact ih b hb
    exact hall s b hb)

theorem cpt_upPadA : CPT upPadA :=
  cptU (cpt_comp (cpt_app2 cpt_id (cpt_const [false])) cpt_dropN) (fun _ => rfl)

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

private theorem combU (A : List Bool) (a b : Bool) :
    (!(sel A [] (sel (if a then [true] else []) []
      (sel (if b then [true] else []) [] [true]))).isEmpty) =
      (!A.isEmpty && (a && b)) := by
  cases A <;> cases a <;> cases b <;> simp [sel]

def upV (fR : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  !(upPadA p.1).isEmpty && (decide (p.2.length ≤ (hd p.1).length) && fR (dropN p.1, p.2))

private theorem cpt_upVS {fR : List Bool × List Bool → Bool}
    (hfR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => upV fR ((unpairB s).1, (unpairB s).2)) := by
  have hy : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have fA : CPT (fun s => upPadA (unpairB s).1) := cpt_comp hy cpt_upPadA
  have f1 := cpt_bitFlag (cpt_comp (cpt_pair (cpt_hd1 hy) hw) LenCmp.lenLE_polyTime)
  have f2 := cpt_bitFlag (cpt_comp (cpt_pair (cpt_dropN1 hy) hw) hfR)
  have all := cpt_sel fA (cpt_const []) (cpt_sel f1 (cpt_const [])
    (cpt_sel f2 (cpt_const []) (cpt_const [true])))
  exact cptU (cpt_comp all cpt_neU) (fun s => combU _ _ _)

theorem cpt_upV {fR : List Bool × List Bool → Bool}
    (hfR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool (upV fR) :=
  cptU (cpt_comp cpt_pairB (cpt_upVS hfR)) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

theorem unaryPad_NP (V : List Bool × List Bool → Bool)
    (hV : ComputableInPolyTime encodePair Computability.encodeBool V) :
    ({y : List Bool | ∃ (t : ℕ) (x w : List Bool),
      y = List.replicate t true ++ false :: x ∧ w.length ≤ t ∧ V (x, w) = true} : Language Bool) ∈
      PvsNP.NP := by
  refine ⟨upV V, Polynomial.X, cpt_upV hV, fun y => ?_⟩
  rw [Polynomial.eval_X]
  constructor
  · rintro ⟨t, x, w, rfl, hwt, hxw⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · have h1 : hd (List.replicate t true ++ false :: x) = un t := hd_un t x
      have h2 : dropN (List.replicate t true ++ false :: x) = x := dropN_un t x
      have h3 : upPadA (List.replicate t true ++ false :: x) = x ++ [false] := by
        have e : (List.replicate t true ++ false :: x) ++ [false] =
            un t ++ false :: (x ++ [false]) := by simp [un]
        rw [upPadA, e, dropN_un]
      show upV V (List.replicate t true ++ false :: x, w) = true
      simp only [upV, h1, h2, h3, un_length]
      simp [hwt, hxw]
  · rintro ⟨w, -, hVy⟩
    have hV' : upV V (y, w) = true := hVy
    simp only [upV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hV'
    obtain ⟨hA, hlen, hf⟩ := hV'
    have hA' : upPadA y ≠ [] := by
      intro h
      rw [h] at hA
      simp at hA
    have hs := (up_hd_split y).resolve_left hA'
    refine ⟨(hd y).length, dropN y, w, ?_, hlen, hf⟩
    have hu : hd y = List.replicate (hd y).length true := up_hd_eq_un y
    rw [← hu]
    exact hs

end PvsNP.Units.m2_unary_pad_np

theorem PvsNP.Units.m2_unary_pad_np :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      ({y : List Bool | ∃ (t : ℕ) (x w : List Bool),
          y = List.replicate t true ++ false :: x ∧ w.length ≤ t ∧ V (x, w) = true} : Language Bool) ∈ PvsNP.NP := by
  intro V hV
  exact PvsNP.Units.m2_unary_pad_np.unaryPad_NP V hV
