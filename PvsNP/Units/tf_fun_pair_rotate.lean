import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_rotate

/-- Rotating one binary string by the length of another takes polynomial time (TM2).
The rotation is built by iterating `rotate 1` (settled: `tf_fun_rotate`) as many
times as the first string is long (`m2_iterate_polytime`), after swapping the pair
(`cpt_swap` in `fr_ladner`), and composing the two machines (`m2_polytime_comp`). -/
theorem PvsNP.Units.tf_fun_pair_rotate :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2.rotate p.1.length) := by
  -- Iterating `rotate 1` n times is `rotate n`.
  have hrot : ∀ (n : ℕ) (b : List Bool),
      (fun x : List Bool => x.rotate 1)^[n] b = b.rotate n := by
    intro n b
    induction n with
    | zero => simp
    | succ n ih => simp [Function.iterate_succ_apply', ih, List.rotate_rotate]
  -- Iterating `rotate 1` by the second component's length is polytime.
  have hiter := PvsNP.Units.m2_iterate_polytime (fun x : List Bool => x.rotate 1) 0
    PvsNP.Units.tf_fun_rotate (fun y => by
      have h : (y.rotate 1).length = y.length := List.length_rotate y 1
      omega)
  -- Swapping the pair is polytime.
  have hswap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.2, p.1)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_swap
  -- Compose: swap, then iterate.
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeString (fun p : List Bool × List Bool => (p.2, p.1))
    (fun p : List Bool × List Bool => (fun x : List Bool => x.rotate 1)^[p.2.length] p.1)
    hswap hiter
  have hfun : ((fun p : List Bool × List Bool =>
        (fun x : List Bool => x.rotate 1)^[p.2.length] p.1) ∘
      (fun p : List Bool × List Bool => (p.2, p.1)))
      = (fun p : List Bool × List Bool => p.2.rotate p.1.length) := by
    funext ⟨a, b⟩
    exact hrot a.length b
  rw [hfun] at hcomp
  exact hcomp
