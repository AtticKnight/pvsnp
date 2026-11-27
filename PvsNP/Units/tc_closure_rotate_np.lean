import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_p_rotate_closed

/-
Built on the settled units m2_np_projection, m2_iterate_polytime and m2_p_rotate_closed of
github.com/makedotfun/pvsnp (Apache License 2.0), which this file imports.
-/

namespace PvsNP.Units.tc_closure_rotate_np

/-- Rotate the first component by the length of the second. -/
def g : List Bool × List Bool → List Bool :=
  fun p : List Bool × List Bool => (fun x : List Bool => x.rotate 1)^[p.2.length] p.1

theorem iter_rot (n : ℕ) : ∀ x : List Bool, (fun x : List Bool => x.rotate 1)^[n] x = x.rotate n := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', ih, List.rotate_rotate]

theorem g_eq (x c : List Bool) : g (x, c) = x.rotate c.length := by
  simp only [g]
  exact iter_rot c.length x

theorem cpt_g : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g :=
  PvsNP.Units.m2_iterate_polytime (fun x : List Bool => x.rotate 1) 0
    PvsNP.Units.m2_p_rotate_closed.cpt_rotate (fun y => by simp)

theorem set_eq (L : Language Bool) :
    ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) =
      ({x : List Bool | ∃ c : List Bool, c.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
        g (x, c) ∈ L} : Language Bool) := by
  ext x
  simp only [Set.mem_setOf_eq, g_eq, Polynomial.eval_X]
  constructor
  · rintro ⟨k, hk⟩
    rcases x with _ | ⟨a, l⟩
    · refine ⟨[], le_refl _, ?_⟩
      simpa using hk
    · refine ⟨List.replicate (k % (a :: l).length) false, ?_, ?_⟩
      · rw [List.length_replicate]
        exact le_of_lt (Nat.mod_lt _ (by simp))
      · rw [List.length_replicate, List.rotate_mod]
        exact hk
  · rintro ⟨c, -, hc⟩
    exact ⟨c.length, hc⟩

end PvsNP.Units.tc_closure_rotate_np

/-- NP is closed under cyclic shift: guess the shift as the length of a certificate. -/
theorem PvsNP.Units.tc_closure_rotate_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_rotate_np.set_eq L]
  exact PvsNP.Units.m2_np_projection L PvsNP.Units.tc_closure_rotate_np.g Polynomial.X hL
    PvsNP.Units.tc_closure_rotate_np.cpt_g
