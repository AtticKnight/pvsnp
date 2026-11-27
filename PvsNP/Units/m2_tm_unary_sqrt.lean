import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_mul_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_unary_sqrt

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def cnd (s : List Bool) : Bool :=
  decide ((List.replicate ((true :: (unpairB s).1).length * (true :: (unpairB s).1).length) true).length
    ≤ (unpairB s).2.length)

def stepA (s : List Bool) : List Bool := pairB (true :: (unpairB s).1) (unpairB s).2
def stepB (s : List Bool) : List Bool := pairB (unpairB s).1 (unpairB s).2

def step (s : List Bool) : List Bool := if cnd s = true then stepA s else stepB s

theorem hcnd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer cnd := by
  have hm := cpt_comp (cpt_pair (cpt_cons1 true cpt_unpairB1) (cpt_cons1 true cpt_unpairB1))
    PvsNP.Units.m2_mul_polytime
  have h := cpt_comp (cpt_pair hm cpt_unpairB2) PvsNP.Units.m2_len_le_polytime
  exact h

theorem hstep : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stepA :=
    cpt_pairB2 (cpt_cons1 true cpt_unpairB1) cpt_unpairB2
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stepB :=
    cpt_pairB2 cpt_unpairB1 cpt_unpairB2
  have h := PvsNP.Units.m2_ite_polytime cnd stepA stepB hcnd hA hB
  exact h

theorem step_len (s : List Bool) : (step s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  unfold step
  split
  · simp only [stepA, pairB_length, List.length_cons]; omega
  · simp only [stepB, pairB_length]; omega

def G (x : List Bool) : List Bool := step^[x.length] (pairB [] x)

theorem hG : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) G :=
  cpt_iterGrow hstep 3 step_len cpt_id (cpt_pairB2 (cpt_const []) cpt_id)

theorem iter_inv (x : List Bool) (i : ℕ) :
    step^[i] (pairB [] x) = pairB (List.replicate (min i (Nat.sqrt x.length)) true) x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : i < Nat.sqrt x.length
    · have hc : cnd (pairB (List.replicate (min i (Nat.sqrt x.length)) true) x) = true := by
        simp only [cnd, unpairB_pairB, List.length_replicate, List.length_cons,
          decide_eq_true_eq]
        rw [Nat.min_eq_left hi.le]
        exact Nat.le_sqrt.mp hi
      rw [step, hc]
      simp only [if_true, stepA, unpairB_pairB]
      rw [Nat.min_eq_left hi.le, Nat.min_eq_left (by omega)]
      simp [List.replicate_succ]
    · have hc : cnd (pairB (List.replicate (min i (Nat.sqrt x.length)) true) x) = false := by
        simp only [cnd, unpairB_pairB, List.length_replicate, List.length_cons,
          decide_eq_false_iff_not, not_le]
        rw [Nat.min_eq_right (by omega)]
        exact Nat.lt_succ_sqrt x.length
      rw [step, hc]
      simp only [Bool.false_eq_true, if_false, stepB, unpairB_pairB]
      rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem cc {f f' : List Bool → List Bool}
    (h : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f' := by
  obtain rfl : f = f' := funext e
  exact h

end PvsNP.Units.m2_tm_unary_sqrt

open PvsNP.Units.m2_tm_unary_sqrt in
open PvsNP.Units.fr_ladner.PEqualNP.Library in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
theorem PvsNP.Units.m2_tm_unary_sqrt :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (Nat.sqrt x.length) true) := by
  have h := cc (cpt_comp hG cpt_unpairB1)
    (f' := fun x : List Bool => List.replicate (Nat.sqrt x.length) true)
    (fun x => by
      simp only [G, iter_inv, unpairB_pairB]
      rw [Nat.min_eq_right (Nat.sqrt_le_self _)])
  exact h
