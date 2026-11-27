import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner (`unpairB`, `cpt_pairB`, `cpt_unpairB1`,
`cpt_unpairB2`, `cpt_unpairB1_1`, `cpt_unpairB2_1`, `cpt_app2`, `cpt_cons1`),
m2_transducer_polytime, and m2_polytime_comp of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.m2_tm_unary_min_max

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

private theorem map_true_eq_replicate (l : List Bool) :
    l.map (fun _ => true) = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons _ t ih => simp [ih, List.replicate_succ]

private theorem unpairB_map_true (u x : List Bool) :
    unpairB (u.map (fun _ => true) ++ false :: x) = (x.take u.length, x.drop u.length) := by
  have h1 : (u.map (fun _ => true) ++ false :: x).takeWhile id = u.map (fun _ => true) := by
    induction u with
    | nil => simp
    | cons _ t ih => simp [ih]
  have h2 : (u.map (fun _ => true) ++ false :: x).dropWhile id = false :: x := by
    induction u with
    | nil => simp
    | cons _ t ih => simp [ih]
  simp [unpairB, h1, h2]

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => List.replicate (min p.1.length p.2.length) true) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => List.replicate (max p.1.length p.2.length) true) := by
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    rw [← encodePair_eq]
    exact cpt_pairB
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).1.map (fun _ => true)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1) (fun u => u.map (fun _ => true)) cpt_unpairB1 map_true_poly
  have hcode : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2) :=
    cpt_app2 hmap (cpt_cons1 false cpt_unpairB2)
  have htakeS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).1) :=
    cpt_unpairB1_1 hcode
  have hdropS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).2) :=
    cpt_unpairB2_1 hcode
  have hminS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘
        (fun s : List Bool => (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).1)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      _ _ htakeS map_true_poly
  have hmaxRaw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).1 ++
        (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).2) :=
    cpt_app2 cpt_unpairB1 hdropS
  have hmaxS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘
        (fun s : List Bool => (unpairB s).1 ++
          (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      _ _ hmaxRaw map_true_poly
  have hminP : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (((fun u : List Bool => u.map (fun _ => true)) ∘
        (fun s : List Bool => (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).1)) ∘
        (fun p : List Bool × List Bool => pairB p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString _ _ hpb hminS
  have hmaxP : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (((fun u : List Bool => u.map (fun _ => true)) ∘
        (fun s : List Bool => (unpairB s).1 ++
          (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).2)) ∘
        (fun p : List Bool × List Bool => pairB p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString _ _ hpb hmaxS
  have heq_min : (((fun u : List Bool => u.map (fun _ => true)) ∘
      (fun s : List Bool => (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).1)) ∘
      (fun p : List Bool × List Bool => pairB p.1 p.2)) =
      (fun p : List Bool × List Bool => List.replicate (min p.1.length p.2.length) true) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB]
    rw [unpairB_map_true, map_true_eq_replicate, List.length_take]
  have heq_max : (((fun u : List Bool => u.map (fun _ => true)) ∘
      (fun s : List Bool => (unpairB s).1 ++
        (unpairB ((unpairB s).1.map (fun _ => true) ++ false :: (unpairB s).2)).2)) ∘
      (fun p : List Bool × List Bool => pairB p.1 p.2)) =
      (fun p : List Bool × List Bool => List.replicate (max p.1.length p.2.length) true) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB]
    rw [unpairB_map_true, map_true_eq_replicate, List.length_append, List.length_drop]
    congr 1
    omega
  exact ⟨by rwa [heq_min] at hminP, by rwa [heq_max] at hmaxP⟩

end PvsNP.Units.m2_tm_unary_min_max

theorem PvsNP.Units.m2_tm_unary_min_max :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => List.replicate (min p.1.length p.2.length) true) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => List.replicate (max p.1.length p.2.length) true) :=
  PvsNP.Units.m2_tm_unary_min_max.main
