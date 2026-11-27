import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_eq_polytime

/-
Built on the settled units PvsNP.Units.fr_ladner (`unpairB`, `cpt_unpairB1_1`, `cpt_unpairB2_1`,
`cpt_app2`, `cpt_cons1`, `cpt_id`, `cpt_pair`), m2_transducer_polytime, m2_polytime_comp, and
m2_eq_polytime of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.tl_lang_anti_square_p

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private def halfU : Bool → List Bool → List Bool
  | _, [] => []
  | false, _ :: t => halfU true t
  | true, _ :: t => true :: halfU false t

private theorem halfU_length (b : Bool) (l : List Bool) :
    (halfU b l).length = if b then (l.length + 1) / 2 else l.length / 2 := by
  induction l generalizing b with
  | nil => cases b <;> simp [halfU]
  | cons _ t ih =>
    cases b with
    | false =>
      simp only [halfU, ih true, ↓reduceIte, List.length_cons, Bool.false_eq_true]
    | true =>
      simp only [halfU, ih false, List.length_cons, Bool.false_eq_true, ↓reduceIte]
      omega

private theorem halfU_all_true (b : Bool) (l : List Bool) :
    halfU b l = List.replicate (halfU b l).length true := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons _ t ih =>
    cases b with
    | false => simpa [halfU] using ih true
    | true =>
      simp only [halfU, List.length_cons, List.replicate_succ]
      congr 1
      exact ih false

private theorem halfU_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (halfU false) :=
  PvsNP.Units.m2_transducer_polytime Bool
    (fun st _ => if st then (false, some true) else (true, none))
    (fun _ => none)
    halfU
    (fun st => by cases st <;> rfl)
    (fun st _ l => by cases st <;> rfl)
    false

private theorem map_not_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => u.map not) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ b => ((), some (!b)))
    (fun _ => none)
    (fun _ u => u.map not)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

private theorem unpairB_rep_true (n : ℕ) (x : List Bool) :
    unpairB (List.replicate n true ++ false :: x) = (x.take n, x.drop n) := by
  have h1 : (List.replicate n true ++ false :: x).takeWhile id = List.replicate n true := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ]
  have h2 : (List.replicate n true ++ false :: x).dropWhile id = false :: x := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ]
  simp [unpairB]

theorem main :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y.map not} : Language Bool) ∈ PvsNP.P := by
  have hcode : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => halfU false x ++ false :: x) :=
    cpt_app2 halfU_poly (cpt_cons1 false cpt_id)
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (unpairB (halfU false x ++ false :: x)).1) :=
    cpt_unpairB1_1 hcode
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (unpairB (halfU false x ++ false :: x)).2) :=
    cpt_unpairB2_1 hcode
  have h1not : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map not) ∘ (fun x : List Bool => (unpairB (halfU false x ++ false :: x)).1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 map_not_poly
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool =>
        ((unpairB (halfU false x ++ false :: x)).2,
         ((unpairB (halfU false x ++ false :: x)).1).map not)) := by
    rw [← encodePair_eq]
    exact cpt_pair h2 h1not
  have hdec := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    _ _ hpair PvsNP.Units.m2_eq_polytime
  refine ⟨_, hdec, fun x => ?_⟩
  change (∃ y : List Bool, x = y ++ y.map not) ↔ _
  simp only [Function.comp_apply, decide_eq_true_eq]
  have hrep : halfU false x = List.replicate (x.length / 2) true := by
    rw [halfU_all_true false x, halfU_length]
    rfl
  rw [hrep, unpairB_rep_true]
  constructor
  · rintro ⟨y, rfl⟩
    have hlen : (y ++ y.map not).length / 2 = y.length := by
      simp [List.length_append, List.length_map]
      omega
    rw [hlen, List.drop_left, List.take_left]
  · intro heq
    refine ⟨x.take (x.length / 2), ?_⟩
    rw [← heq, List.take_append_drop]

end PvsNP.Units.tl_lang_anti_square_p

theorem PvsNP.Units.tl_lang_anti_square_p :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y.map not} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_anti_square_p.main
