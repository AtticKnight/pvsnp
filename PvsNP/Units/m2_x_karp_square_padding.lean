import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_square_clock
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_prod_map_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_x_karp_square_padding

def padSq (x : List Bool) : List Bool :=
  List.replicate (x.length ^ 2) true ++ false :: x

private theorem cpt_cons_false :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => false :: x) := by
  have hp := PvsNP.Units.m2_pair_build_polytime
    (fun _ : List Bool => [false]) (fun x : List Bool => x)
    (PvsNP.Units.m2_const_polytime [false])
    PvsNP.Units.m2_prod_map_polytime.ident
  exact PvsNP.Units.m2_polytime_comp
    PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => ([false], x))
    (fun p : List Bool × List Bool => p.1 ++ p.2)
    hp PvsNP.Units.m2_pair_split_polytime.2.2

private theorem cpt_padSq :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString padSq := by
  have hp := PvsNP.Units.m2_pair_build_polytime
    (fun x : List Bool => List.replicate (x.length ^ 2) true)
    (fun x : List Bool => false :: x)
    PvsNP.Units.m2_square_clock.h_poly
    cpt_cons_false
  exact PvsNP.Units.m2_polytime_comp
    PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (List.replicate (x.length ^ 2) true, false :: x))
    (fun p : List Bool × List Bool => p.1 ++ p.2)
    hp PvsNP.Units.m2_pair_split_polytime.2.2

private theorem dropWhile_rep_false (n : ℕ) (x : List Bool) :
    (List.replicate n true ++ false :: x).dropWhile id = false :: x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem padSq_inj {x y : List Bool} (h : padSq x = padSq y) : x = y := by
  have h1 := congrArg (fun l : List Bool => l.dropWhile id) h
  simp only [padSq, dropWhile_rep_false] at h1
  exact (List.cons.inj h1).2

theorem main (L : Language Bool) : PvsNP.KarpReducible L
    ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ 2) true ++ false :: x} : Language Bool) := by
  refine ⟨padSq, cpt_padSq, fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    exact padSq_inj hxy ▸ hy

end PvsNP.Units.m2_x_karp_square_padding

theorem PvsNP.Units.m2_x_karp_square_padding :
    ∀ L : Language Bool, PvsNP.KarpReducible L
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ 2) true ++ false :: x} : Language Bool) :=
  PvsNP.Units.m2_x_karp_square_padding.main
