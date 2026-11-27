import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

set_option autoImplicit false

theorem PvsNP.Units.m2_tm_y_even_odd_positions :
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => (List.range ((x.length + 1) / 2)).map (fun i => x.getD (2 * i) false)) ∧
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => (List.range (x.length / 2)).map (fun i => x.getD (2 * i + 1) false)) := by
  let δ : Bool → Bool → Bool × Option Bool := fun q b =>
    match q with
    | true => (false, some b)
    | false => (true, none)
  let fin : Bool → Option Bool := fun _ => none
  let F : Bool → List Bool → List Bool := fun q x =>
    match q with
    | true => (List.range ((x.length + 1) / 2)).map (fun i => x.getD (2 * i) false)
    | false => (List.range (x.length / 2)).map (fun i => x.getD (2 * i + 1) false)
  have h0 : ∀ q : Bool, F q [] = (fin q).toList := by
    intro q
    cases q <;> rfl
  have h1 : ∀ (q : Bool) (b : Bool) (x : List Bool),
      F q (b :: x) = (δ q b).2.toList ++ F (δ q b).1 x := by
    intro q b x
    cases q with
    | true =>
      simp only [F, δ, List.length_cons, Option.toList_some, List.singleton_append]
      have hdiv : (x.length + 1 + 1) / 2 = x.length / 2 + 1 := by omega
      rw [hdiv, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.mul_zero, List.getD_cons_zero]
      congr 1
    | false =>
      simp only [F, δ, List.length_cons, Option.toList_none, List.nil_append]
      apply List.map_congr_left
      intro i _
      exact List.getD_cons_succ
  exact ⟨PvsNP.Units.m2_transducer_polytime Bool δ fin F h0 h1 true,
         PvsNP.Units.m2_transducer_polytime Bool δ fin F h0 h1 false⟩
