import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_reverse_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_np_length_projection

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem tail_iter (n : ℕ) : ∀ l : List Bool, List.tail^[n] l = l.drop n := by
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
    intro l
    rw [Function.iterate_succ_apply, ih]
    cases l with
    | nil => simp
    | cons a l => simp

def Z (s : List Bool) : List Bool := (unpairB s).2 ++ (unpairB s).1

def D (s : List Bool) : List Bool := List.tail^[((unpairB s).1).length] (Z s)

def T (s : List Bool) : List Bool := List.tail^[(D s).length] ((Z s).reverse)

def F (s : List Bool) : List Bool := (T s).reverse

theorem hZ : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) Z :=
  cpt_app2 cpt_unpairB2 cpt_unpairB1

theorem hD : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) D :=
  cpt_iterLen (g := List.tail) cpt_tail (fun s => by simp) cpt_unpairB1 hZ

theorem hT : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) T :=
  cpt_iterLen (g := List.tail) cpt_tail (fun s => by simp) hD
    (cpt_comp hZ PvsNP.Units.m2_reverse_polytime)

theorem hF : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) F := by
  have h := cpt_comp hT PvsNP.Units.m2_reverse_polytime
  exact h

def G (p : List Bool × List Bool) : List Bool := F (pairB p.1 p.2)

theorem hG : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString G := by
  have h := cpt_comp cpt_pairB hF
  exact h

theorem F_eq (x c : List Bool) : G (x, c) = (c ++ x).take x.length := by
  simp only [G, F, T, D, Z, unpairB_pairB, tail_iter]
  have hl : ((c ++ x).drop x.length).length = (c ++ x).length - x.length := List.length_drop
  rw [hl, List.drop_reverse, List.reverse_reverse]
  have hle : x.length ≤ (c ++ x).length := by simp
  rw [Nat.sub_sub_self hle]

end PvsNP.Units.m2_np_length_projection

open PvsNP.Units.m2_np_length_projection in
theorem PvsNP.Units.m2_np_length_projection :
    ∀ L ∈ PvsNP.NP, ({x : List Bool | ∃ y ∈ L, y.length = x.length} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have h := PvsNP.Units.m2_np_projection L G Polynomial.X hL hG
  have hset : ({x : List Bool | ∃ c : List Bool, c.length ≤ Polynomial.X.eval x.length ∧
      G (x, c) ∈ L} : Language Bool) =
      ({x : List Bool | ∃ y ∈ L, y.length = x.length} : Language Bool) := by
    ext x
    show (∃ c : List Bool, c.length ≤ Polynomial.X.eval x.length ∧ G (x, c) ∈ L) ↔
      (∃ y ∈ L, y.length = x.length)
    simp only [Polynomial.eval_X, F_eq]
    constructor
    · rintro ⟨c, _, hc⟩
      refine ⟨(c ++ x).take x.length, hc, ?_⟩
      simp
    · rintro ⟨y, hyL, hy⟩
      refine ⟨y, hy.le, ?_⟩
      rw [List.take_left' hy]
      exact hyL
  rw [← hset]
  exact h
