import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_ite_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_unary_divmod

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def gq (s : List Bool) : List Bool := (unpairB s).1
def gr (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def gy (s : List Bool) : List Bool := (unpairB (unpairB s).2).2

def cnd (s : List Bool) : Bool :=
  decide ((gy s).length ≤ (true :: gr s).length) && decide ((true :: gr s).length ≤ (gy s).length)

def stepA (s : List Bool) : List Bool := pairB (true :: gq s) (pairB [] (gy s))
def stepB (s : List Bool) : List Bool := pairB (gq s) (pairB (true :: gr s) (gy s))

def step (s : List Bool) : List Bool := if cnd s = true then stepA s else stepB s

theorem hgq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gq := by
  have h := cpt_unpairB1; exact h
theorem hgr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gr := by
  have h := cpt_comp cpt_unpairB2 cpt_unpairB1; exact h
theorem hgy : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gy := by
  have h := cpt_comp cpt_unpairB2 cpt_unpairB2; exact h

theorem hcnd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer cnd := by
  have h1 := cpt_comp (cpt_pair hgy (cpt_cons1 true hgr)) PvsNP.Units.m2_len_le_polytime
  have h2 := cpt_comp (cpt_pair (cpt_cons1 true hgr) hgy) PvsNP.Units.m2_len_le_polytime
  have h := PvsNP.Units.m2_bool_combine_polytime (fun a b => a && b) _ _ h1 h2
  exact h

theorem hstep : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString step := by
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stepA :=
    cpt_pairB2 (cpt_cons1 true hgq) (cpt_pairB2 (cpt_const []) hgy)
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stepB :=
    cpt_pairB2 hgq (cpt_pairB2 (cpt_cons1 true hgr) hgy)
  have h := PvsNP.Units.m2_ite_polytime cnd stepA stepB hcnd hA hB
  exact h

theorem step_len (s : List Bool) : (step s).length ≤ s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  unfold step stepA stepB gq gr gy
  split <;> simp only [pairB_length, List.length_cons, List.length_nil] <;> omega

def init (s : List Bool) : List Bool := pairB [] (pairB [] (unpairB s).2)

def G (s : List Bool) : List Bool := step^[(unpairB s).1.length] (init s)

theorem hG : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) G := by
  have hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
    have h := hstep; exact h
  have hi : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) init :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_unpairB2)
  exact cpt_iterGrow hs 4 step_len cpt_unpairB1 hi

theorem cptc' {f f' : List Bool × List Bool → List Bool}
    (h : ComputableInPolyTime encodePair (fun x : List Bool => x) f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime encodePair (fun x : List Bool => x) f' := by
  obtain rfl : f = f' := funext e
  exact h

def st (q r y : ℕ) (yl : List Bool) : List Bool :=
  pairB (List.replicate q true) (pairB (List.replicate r true) yl)

theorem iter_inv (yl : List Bool) (i : ℕ) :
    step^[i] (pairB [] (pairB [] yl)) =
      if yl.length = 0 then st 0 i 0 yl else st (i / yl.length) (i % yl.length) 0 yl := by
  induction i with
  | zero => split <;> simp [st]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hy : yl.length = 0
    · simp only [hy, if_true]
      have hc : cnd (st 0 i 0 yl) = false := by
        simp [cnd, gy, gr, st, unpairB_pairB, hy]
      rw [step, hc]
      simp only [Bool.false_eq_true, if_false, stepB, st, gq, gr, gy, unpairB_pairB]
      simp [List.replicate_succ]
    · simp only [hy, if_false]
      have hpos : 0 < yl.length := Nat.pos_of_ne_zero hy
      have hm := Nat.mod_lt i hpos
      by_cases he : i % yl.length + 1 = yl.length
      · have hc : cnd (st (i / yl.length) (i % yl.length) 0 yl) = true := by
          simp [cnd, gy, gr, st, unpairB_pairB]; omega
        rw [step, hc]
        simp only [if_true, stepA, st, gq, gy, unpairB_pairB]
        have hd : (i + 1) / yl.length = i / yl.length + 1 := by
          have := Nat.div_add_mod i yl.length
          have h2 : i + 1 = (i / yl.length + 1) * yl.length := by
            have hc' := Nat.mul_comm yl.length (i / yl.length)
            rw [Nat.add_mul]; omega
          rw [h2, Nat.mul_div_cancel _ hpos]
        have hmod : (i + 1) % yl.length = 0 := by
          have h2 : i + 1 = (i / yl.length + 1) * yl.length := by
            have := Nat.div_add_mod i yl.length
            have hc' := Nat.mul_comm yl.length (i / yl.length)
            rw [Nat.add_mul]; omega
          rw [h2, Nat.mul_mod_left]
        rw [hd, hmod]; simp [List.replicate_succ]
      · have hc : cnd (st (i / yl.length) (i % yl.length) 0 yl) = false := by
          simp [cnd, gy, gr, st, unpairB_pairB]; omega
        rw [step, hc]
        simp only [Bool.false_eq_true, if_false, stepB, st, gq, gr, gy, unpairB_pairB]
        have hmod : (i + 1) % yl.length = i % yl.length + 1 := by
          rw [Nat.add_mod]; rw [Nat.mod_eq_of_lt (a := 1) (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hd : (i + 1) / yl.length = i / yl.length := by
          have h1 := Nat.div_add_mod i yl.length
          have h2 := Nat.div_add_mod (i + 1) yl.length
          rw [hmod] at h2
          have : yl.length * ((i + 1) / yl.length) = yl.length * (i / yl.length) := by omega
          exact Nat.eq_of_mul_eq_mul_left hpos this
        rw [hd, hmod]; simp [List.replicate_succ]

theorem G_pair (x y : List Bool) :
    G (pairB x y) = st (x.length / y.length) (x.length % y.length) 0 y := by
  simp only [G, init, unpairB_pairB]
  rw [iter_inv]
  split
  · rename_i hy; simp [hy, st]
  · rfl

end PvsNP.Units.m2_tm_unary_divmod

open PvsNP.Units.m2_tm_unary_divmod in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
theorem PvsNP.Units.m2_tm_unary_divmod :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length / p.2.length) true) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true) := by
  constructor
  · have h := cptc' (cpt_comp cpt_pairB (cpt_comp hG cpt_unpairB1))
      (f' := fun p : List Bool × List Bool => List.replicate (p.1.length / p.2.length) true)
      (fun p => by simp [G_pair, PvsNP.Units.m2_tm_unary_divmod.st, unpairB_pairB])
    exact h
  · have h := cptc' (cpt_comp cpt_pairB (cpt_comp hG (cpt_comp cpt_unpairB2 cpt_unpairB1)))
      (f' := fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true)
      (fun p => by simp [G_pair, PvsNP.Units.m2_tm_unary_divmod.st, unpairB_pairB])
    exact h
