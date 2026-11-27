import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner (`pairB`, `unpairB`, `unpairB_pairB`, `pairB_length`,
`sel`, `cpt_pairB`, `cpt_pairB2`, `cpt_unpairB1`, `cpt_unpairB2`, `cpt_unpairB1_1`, `cpt_unpairB2_1`,
`cpt_app2`, `cpt_cons1`, `cpt_const`, `cpt_id`, `cpt_pair`, `cpt_sel`, `fst_polyTime`,
`Iter.iter_polyTime`), m2_transducer_polytime, and m2_polytime_comp of github.com/makedotfun/pvsnp
(Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.tr_rel_sublist

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem map_true_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => u.map (fun _ => true)) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some true))
    (fun _ => none)
    (fun _ u => u.map (fun _ => true))
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

private theorem unpairB_map_true (u x : List Bool) :
    unpairB (u.map (fun _ => true) ++ false :: x) = (x.take u.length, x.drop u.length) := by
  have h1 : (u.map (fun _ => true) ++ false :: x).takeWhile id = u.map (fun _ => true) := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  have h2 : (u.map (fun _ => true) ++ false :: x).dropWhile id = false :: x := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  simp [unpairB]

private def tailStrAux : Bool → List Bool → List Bool
  | _, [] => []
  | false, _ :: t => tailStrAux true t
  | true, b :: t => b :: tailStrAux true t

private theorem tailStrAux_true (l : List Bool) : tailStrAux true l = l := by
  induction l with
  | nil => rfl
  | cons b t ih => simp [tailStrAux, ih]

private theorem tailStr_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun l : List Bool => l.tail) := by
  have h := PvsNP.Units.m2_transducer_polytime Bool
    (fun started b => if started then (true, some b) else (true, none))
    (fun _ => none)
    tailStrAux
    (fun s => by cases s <;> rfl)
    (fun s b t => by cases s <;> rfl)
    false
  have heq : tailStrAux false = (fun l : List Bool => l.tail) := by
    funext l; cases l with | nil => rfl | cons _ t => simp [tailStrAux, tailStrAux_true]
  rwa [heq] at h

private def headTagAux : Bool → List Bool → List Bool
  | _, [] => []
  | false, true :: t => true :: headTagAux true t
  | false, false :: t => false :: headTagAux true t
  | true, _ :: t => headTagAux true t

private theorem headTagAux_true (l : List Bool) : headTagAux true l = [] := by
  induction l with
  | nil => rfl
  | cons _ t ih => simp [headTagAux, ih]

private theorem headTag_eq (l : List Bool) :
    headTagAux false l = match l with | [] => [] | b :: _ => [b] := by
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [headTagAux, headTagAux_true]

private theorem headTag_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun l : List Bool => match l with | [] => [] | b :: _ => [b]) := by
  have h := PvsNP.Units.m2_transducer_polytime Bool
    (fun seen b => if seen then (true, none) else (true, some b))
    (fun _ => none)
    headTagAux
    (fun s => by cases s <;> rfl)
    (fun s b t => by cases s <;> cases b <;> rfl)
    false
  have heq : headTagAux false = (fun l : List Bool => match l with | [] => [] | b :: _ => [b]) :=
    funext headTag_eq
  rwa [heq] at h

private def headIsTrueAux : Bool → List Bool → List Bool
  | _, [] => []
  | false, true :: t => true :: headIsTrueAux true t
  | false, false :: t => headIsTrueAux true t
  | true, _ :: t => headIsTrueAux true t

private theorem headIsTrueAux_true (l : List Bool) : headIsTrueAux true l = [] := by
  induction l with
  | nil => rfl
  | cons _ t ih => simp [headIsTrueAux, ih]

private theorem headIsTrue_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun l : List Bool => if l.head? = some true then [true] else []) := by
  have h := PvsNP.Units.m2_transducer_polytime Bool
    (fun seen b => if seen then (true, none) else if b then (true, some true) else (true, none))
    (fun _ => none)
    headIsTrueAux
    (fun s => by cases s <;> rfl)
    (fun s b t => by cases s <;> cases b <;> rfl)
    false
  have heq : headIsTrueAux false = (fun l : List Bool => if l.head? = some true then [true] else []) := by
    funext l; cases l with | nil => rfl | cons b t => cases b <;> simp [headIsTrueAux, headIsTrueAux_true]
  rwa [heq] at h

private theorem isEmpty_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool))) (fun q => some q) false l =
      [false] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [fstRun, ih]

private theorem cpt_isEmpty :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun l : List Bool => l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
    (fun q => some q) true (fun l => by
      cases l with
      | nil => rfl
      | cons _ l =>
        simp [fstRun, isEmpty_true, PvsNP.encodeString, PvsNP.encodeAnswer,
          Computability.encodingList, Computability.encodeBool])

-- State: pairB x y
private def rawSubStep (st : List Bool) : List Bool :=
  let x := (unpairB st).1
  let y := (unpairB st).2
  let xT := if x.head? = some true then [true] else []
  let yT := if y.head? = some true then [true] else []
  let eqHeads := sel xT (sel yT [true] []) (sel yT [] [true])
  let bothNe := sel x [] (sel y [] eqHeads)
  let x' := sel bothNe x x.tail
  pairB x' y.tail

private def subStep (st : List Bool) : List Bool :=
  let ns := rawSubStep st
  sel (ns.drop st.length) ns st

private theorem subStep_length_le (st : List Bool) :
    (subStep st).length ≤ st.length + 0 := by
  unfold subStep sel
  dsimp only
  split_ifs with h
  · have hle := List.drop_eq_nil_iff.1 h; omega
  · omega

private theorem subStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString subStep := by
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).1) := cpt_unpairB1
  have hy : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).2) := cpt_unpairB2
  have hxT := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hx headIsTrue_poly
  have hyT := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hy headIsTrue_poly
  have heqH := cpt_sel hxT (cpt_sel hyT (cpt_const [true]) (cpt_const []))
    (cpt_sel hyT (cpt_const []) (cpt_const [true]))
  have hboth := cpt_sel hx (cpt_const []) (cpt_sel hy (cpt_const []) heqH)
  have hxTail := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hx tailStr_poly
  have hyTail := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hy tailStr_poly
  have hx' := cpt_sel hboth hx hxTail
  have hraw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rawSubStep :=
    cpt_pairB2 hx' hyTail
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (st.map (fun _ => true) ++ false :: rawSubStep st)).2) :=
    cpt_unpairB2_1 (cpt_app2 map_true_poly (cpt_cons1 false hraw))
  have hsel : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        sel (unpairB (st.map (fun _ => true) ++ false :: rawSubStep st)).2 (rawSubStep st) st) :=
    cpt_sel hdrop hraw cpt_id
  have heq : (fun st : List Bool =>
      sel (unpairB (st.map (fun _ => true) ++ false :: rawSubStep st)).2 (rawSubStep st) st) = subStep := by
    funext st
    simp only [subStep, unpairB_map_true]
  rwa [heq] at hsel

private theorem subStep_nil_left (b : Bool) (ys : List Bool) :
    subStep (pairB [] (b :: ys)) = pairB [] ys := by
  have hraw : rawSubStep (pairB [] (b :: ys)) = pairB [] ys := by
    unfold rawSubStep; simp [unpairB_pairB, sel]
  have hlen : (rawSubStep (pairB [] (b :: ys))).length ≤ (pairB [] (b :: ys)).length := by
    rw [hraw]; simp [pairB_length]
  unfold subStep; dsimp only
  rw [List.drop_eq_nil_iff.2 hlen]; simp [sel, hraw]

private theorem subStep_cons_cons (a b : Bool) (xs ys : List Bool) :
    subStep (pairB (a :: xs) (b :: ys)) = pairB (if a = b then xs else a :: xs) ys := by
  have hraw : rawSubStep (pairB (a :: xs) (b :: ys)) = pairB (if a = b then xs else a :: xs) ys := by
    unfold rawSubStep
    simp only [unpairB_pairB]
    cases a <;> cases b <;> simp [sel]
  have hlen : (rawSubStep (pairB (a :: xs) (b :: ys))).length ≤ (pairB (a :: xs) (b :: ys)).length := by
    rw [hraw]
    simp only [pairB_length]
    split_ifs <;> simp <;> omega
  unfold subStep; dsimp only
  rw [List.drop_eq_nil_iff.2 hlen]; simp [sel, hraw]

private theorem iter_subStep :
    ∀ (y x : List Bool),
      ((unpairB (subStep^[y.length] (pairB x y))).1).isEmpty = true ↔ List.Sublist x y := by
  intro y
  induction y with
  | nil =>
    intro x
    simp only [List.length_nil, Function.iterate_zero, id_eq, unpairB_pairB]
    cases x with
    | nil => simp
    | cons a xs => simp
  | cons b ys ih =>
    intro x
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | nil =>
      rw [subStep_nil_left, ih []]
      simp
    | cons a xs =>
      rw [subStep_cons_cons]
      by_cases hab : a = b
      · subst hab
        simp only [↓reduceIte, ih xs]
        exact List.cons_sublist_cons.symm
      · simp only [hab, ↓reduceIte, ih (a :: xs)]
        constructor
        · intro h; exact List.Sublist.cons b h
        · intro h
          cases h with
          | cons _ h' => exact h'
          | cons_cons _ _ => exact absurd rfl hab

theorem main :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool, List.Sublist p.1 p.2 ↔ f p = true := by
  obtain ⟨cStep⟩ := subStep_poly
  have hIter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun q : List Bool × List Bool => subStep^[q.2.length] q.1) :=
    Iter.iter_polyTime subStep cStep 0 subStep_length_le
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => pairB q.1 q.2) := by
    rw [← encodePair_eq]; exact cpt_pairB
  have hPairIter := cpt_pair cpt_id cpt_unpairB2
  have hRun := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hPairIter hIter
  have hOut := cpt_unpairB1_1 hRun
  have hBoolS := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hOut cpt_isEmpty
  have hBoolP := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpb hBoolS
  let f : List Bool × List Bool → Bool := fun p =>
    ((unpairB (subStep^[p.2.length] (pairB p.1 p.2))).1).isEmpty
  have hfEq : (((fun l : List Bool => l.isEmpty) ∘
        (fun s : List Bool =>
          (unpairB (((fun q : List Bool × List Bool => subStep^[q.2.length] q.1) ∘
            (fun s : List Bool => (s, (unpairB s).2))) s)).1)) ∘
      (fun q : List Bool × List Bool => pairB q.1 q.2)) = f := by
    funext ⟨x, y⟩
    simp only [Function.comp_apply, unpairB_pairB, f]
  refine ⟨f, by rwa [hfEq] at hBoolP, fun ⟨x, y⟩ => (iter_subStep y x).symm⟩

end PvsNP.Units.tr_rel_sublist

theorem PvsNP.Units.tr_rel_sublist :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool, List.Sublist p.1 p.2 ↔ f p = true :=
  PvsNP.Units.tr_rel_sublist.main
