import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_ite_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_p_all_suffixes

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def sufStep (d : List Bool → Bool) (s : List Bool) : List Bool :=
  let cur := (unpairB s).1
  let ok := decide ((unpairB s).2 = [true])
  pairB cur.tail (if ok && d cur then [true] else [false])

theorem unpairB_weighted (u : List Bool) :
    2 * (unpairB u).1.length + (unpairB u).2.length ≤ u.length := by
  have h1 : (unpairB u).1.length ≤ (u.takeWhile id).length := by simp [unpairB]
  have h2 : (unpairB u).1.length + (unpairB u).2.length ≤ (u.dropWhile id).length := by
    simp only [unpairB]
    have htd := List.take_append_drop (u.takeWhile id).length (u.dropWhile id).tail
    have hl := congrArg List.length htd
    simp only [List.length_append, List.length_tail] at hl
    omega
  have h3 : (u.takeWhile id).length + (u.dropWhile id).length = u.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

theorem sufStep_len (d : List Bool → Bool) (s : List Bool) :
    (sufStep d s).length ≤ s.length + 2 := by
  unfold sufStep
  rw [pairB_length]
  have hw := unpairB_weighted s
  have htl : (unpairB s).1.tail.length ≤ (unpairB s).1.length := by rw [List.length_tail]; omega
  split_ifs <;> simp <;> omega

theorem cpt_sufStep {d : List Bool → Bool}
    (hd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer d) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (sufStep d) := by
  have hcur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hokStr : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hok : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((unpairB s).2 = [true])) :=
    cpt_comp (PvsNP.Units.m2_pair_build_polytime _ _ hokStr (cpt_const [true]))
      PvsNP.Units.m2_eq_polytime
  have hdcur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => d (unpairB s).1) :=
    cpt_comp hcur hd
  have hcomb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((unpairB s).2 = [true]) && d (unpairB s).1) :=
    PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hok hdcur
  have hflag : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if (decide ((unpairB s).2 = [true]) && d (unpairB s).1) = true then [true] else [false]) :=
    PvsNP.Units.m2_ite_polytime _ _ _ hcomb (cpt_const [true]) (cpt_const [false])
  exact cpt_pairB2 (cpt_tail1 hcur) hflag

def sufOk (d : List Bool → Bool) : List Bool → Bool
  | [] => d []
  | b :: xs => d (b :: xs) && sufOk d xs

theorem sufStep_iter (d : List Bool → Bool) :
    ∀ (x : List Bool) (ok : Bool),
      (sufStep d)^[x.length + 1] (pairB x (if ok then [true] else [false])) =
        pairB [] (if ok && sufOk d x then [true] else [false]) := by
  intro x
  induction x with
  | nil =>
    intro ok
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, sufStep, unpairB_pairB,
      List.tail_nil, sufOk]
    cases ok <;> simp
  | cons b xs ih =>
    intro ok
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sufStep d (pairB (b :: xs) (if ok then [true] else [false])) =
        pairB xs (if ok && d (b :: xs) then [true] else [false]) := by
      simp only [sufStep, unpairB_pairB, List.tail_cons]
      cases ok <;> simp
    rw [h1, ih (ok && d (b :: xs))]
    simp only [sufOk, Bool.and_assoc]
    rfl

theorem sufOk_iff (d : List Bool → Bool) (x : List Bool) :
    sufOk d x = true ↔ ∀ y : List Bool, y <:+ x → d y = true := by
  induction x with
  | nil =>
    simp only [sufOk, List.suffix_nil]
    constructor
    · rintro h y rfl; exact h
    · intro h; exact h [] rfl
  | cons b xs ih =>
    simp only [sufOk, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hd, hxs⟩ y hy
      obtain ⟨t, ht⟩ := hy
      cases t with
      | nil =>
        simp only [List.nil_append] at ht
        rw [ht]
        exact hd
      | cons a t =>
        simp only [List.cons_append, List.cons.injEq] at ht
        exact hxs y ⟨t, ht.2⟩
    · intro h
      refine ⟨h (b :: xs) List.suffix_rfl, fun y hy => ?_⟩
      exact h y (hy.trans (List.suffix_cons b xs))

def sufDec (d : List Bool → Bool) (x : List Bool) : Bool :=
  decide ((unpairB ((sufStep d)^[(true :: x).length] (pairB x [true]))).2 = [true])

theorem cpt_sufDec {d : List Bool → Bool}
    (hd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer d) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (sufDec d) := by
  have hInit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => pairB x [true]) :=
    cpt_pairB2 cpt_id (cpt_const [true])
  have hClk : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => true :: x) := by
    have h := cpt_app2 (cpt_const [true]) cpt_id
    have heq : (fun x : List Bool => [true] ++ x) = (fun x => true :: x) := rfl
    rwa [heq] at h
  have hIter := PvsNP.Units.m2_iterate_polytime (sufStep d) 2 (cpt_sufStep hd) (sufStep_len d)
  have hRun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => (sufStep d)^[(true :: x).length] (pairB x [true])) :=
    cpt_comp (f := fun x => (pairB x [true], true :: x))
      (g := fun p : List Bool × List Bool => (sufStep d)^[p.2.length] p.1)
      (PvsNP.Units.m2_pair_build_polytime _ _ hInit hClk) hIter
  have hOut : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => (unpairB ((sufStep d)^[(true :: x).length] (pairB x [true]))).2) :=
    cpt_unpairB2_1 hRun
  exact cpt_comp
    (f := fun x => ((unpairB ((sufStep d)^[(true :: x).length] (pairB x [true]))).2, [true]))
    (g := fun p : List Bool × List Bool => decide (p.1 = p.2))
    (PvsNP.Units.m2_pair_build_polytime _ _ hOut (cpt_const [true]))
    PvsNP.Units.m2_eq_polytime

end PvsNP.Units.m2_p_all_suffixes

/-- P is closed under "every suffix is in L" (TM2). -/
theorem PvsNP.Units.m2_p_all_suffixes :
    ∀ L ∈ PvsNP.P, ({x : List Bool | ∀ y : List Bool, y <:+ x → y ∈ L} : Language Bool) ∈ PvsNP.P := by
  rintro L ⟨d, hd, hdec⟩
  refine ⟨PvsNP.Units.m2_p_all_suffixes.sufDec d, PvsNP.Units.m2_p_all_suffixes.cpt_sufDec hd, fun x => ?_⟩
  show (∀ y : List Bool, y <:+ x → y ∈ L) ↔ PvsNP.Units.m2_p_all_suffixes.sufDec d x = true
  have hiter := PvsNP.Units.m2_p_all_suffixes.sufStep_iter d x true
  simp only [↓reduceIte, Bool.true_and] at hiter
  have hdecEq : PvsNP.Units.m2_p_all_suffixes.sufDec d x = PvsNP.Units.m2_p_all_suffixes.sufOk d x := by
    unfold PvsNP.Units.m2_p_all_suffixes.sufDec
    rw [List.length_cons, hiter, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
    cases PvsNP.Units.m2_p_all_suffixes.sufOk d x <;> rfl
  rw [hdecEq, PvsNP.Units.m2_p_all_suffixes.sufOk_iff]
  exact forall_congr' fun y => imp_congr_right fun _ => hdec y
