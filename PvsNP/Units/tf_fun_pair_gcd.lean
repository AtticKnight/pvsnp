import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_pair_mod
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_iterate_polytime

namespace PvsNP.Units.tf_fun_pair_gcd

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tr_rel_val_coprime (val val_bits val_lt_two_pow
  bits_length_le_of_lt_two_pow unpairB_weighted binAdd cpt_binAdd_fun canon canon_eq)

private def remWord (a b : List Bool) := Nat.bits (val a % val b)

private theorem rem_len (a b : List Bool) : (remWord a b).length ≤ a.length :=
  bits_length_le_of_lt_two_pow (lt_of_le_of_lt (Nat.mod_le _ _) (val_lt_two_pow a))

private theorem cpt_rem (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x => remWord (f x) (g x)) :=
  cpt_comp (f := fun x => (f x, g x)) (g := fun p : List Bool × List Bool => remWord p.1 p.2)
    (m2_pair_build_polytime f g hf hg) tf_fun_pair_mod

/-- Euclid twice. With remainder by zero defined as the dividend, either zero coordinate is stable. -/
private def twice (state : List Bool) : List Bool :=
  let a := (unpairB state).1
  let b := (unpairB state).2
  let r := remWord a b
  pairB r (remWord b r)

private theorem cpt_twice :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString twice := by
  have ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1) := cpt_unpairB1_1 cpt_id
  have hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2) := cpt_unpairB2_1 cpt_id
  have hr := cpt_rem _ _ ha hb
  exact cpt_pairB2 hr (cpt_rem _ _ hb hr)

private theorem twice_len (s : List Bool) : (twice s).length ≤ s.length + 1 := by
  have hw := unpairB_weighted s
  have h1 := rem_len (unpairB s).1 (unpairB s).2
  have h2 := rem_len (unpairB s).2 (remWord (unpairB s).1 (unpairB s).2)
  simp only [twice, pairB_length]
  omega

private theorem twice_bits (a b : ℕ) :
    twice (pairB (Nat.bits a) (Nat.bits b)) =
      pairB (Nat.bits (a % b)) (Nat.bits (b % (a % b))) := by
  simp only [twice, remWord, unpairB_pairB, val_bits]

private theorem halve (b r : ℕ) (hr : 0 < r) (hlt : r < b) : 2 * (b % r) < b := by
  by_cases h : 2 * r ≤ b
  · have := Nat.mod_lt b hr
    omega
  · have he : b % r = b - r := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hlt), Nat.mod_eq_of_lt (by omega : b - r < r)]
    rw [he]
    omega

private theorem gcd_twice (a b : ℕ) : Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) := by
  calc
    Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm _ _
    _ = Nat.gcd (a % b) b := Nat.gcd_rec b a
    _ = Nat.gcd (b % (a % b)) (a % b) := Nat.gcd_rec (a % b) b
    _ = Nat.gcd (a % b) (b % (a % b)) := Nat.gcd_comm _ _

private def valueOut (s : List Bool) := binAdd (unpairB s).1 (unpairB s).2

private theorem read_after (t a b : ℕ) (h : a = 0 ∨ b < 2 ^ t) :
    valueOut (twice^[t] (pairB (Nat.bits a) (Nat.bits b))) = Nat.bits (Nat.gcd a b) := by
  induction t generalizing a b with
  | zero =>
    have stop : a = 0 ∨ b = 0 := by simpa using h
    have emptyValue : val [] = 0 := rfl
    rcases stop with rfl | rfl <;>
      simp [valueOut, unpairB_pairB, binAdd, val_bits, emptyValue]
  | succ t ih =>
    rw [Function.iterate_succ_apply, twice_bits]
    have nextStep : a % b = 0 ∨ b % (a % b) < 2 ^ t := by
      by_cases hr : a % b = 0
      · exact Or.inl hr
      right
      rcases h with ha | hb
      · subst a
        simp at hr
      · by_cases hzero : b = 0
        · simp [hzero]
        · have hlt := Nat.mod_lt a (Nat.pos_of_ne_zero hzero)
          have hhalf := halve b (a % b) (Nat.pos_of_ne_zero hr) hlt
          rw [Nat.pow_succ] at hb
          omega
    rw [ih _ _ nextStep, ← gcd_twice]

private def compute (s : List Bool) :=
  valueOut (twice^[((unpairB s).2).length]
    (pairB (canon (unpairB s).1) (canon (unpairB s).2)))

private theorem cpt_compute :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString compute := by
  have ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1) := cpt_unpairB1_1 cpt_id
  have hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2) := cpt_unpairB2_1 cpt_id
  have init : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (canon (unpairB s).1) (canon (unpairB s).2)) :=
    cpt_pairB2 (cpt_binAdd_fun _ _ ha (cpt_const [])) (cpt_binAdd_fun _ _ hb (cpt_const []))
  have run : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => twice^[((unpairB s).2).length] (pairB (canon (unpairB s).1) (canon (unpairB s).2))) :=
    cpt_comp (f := fun s => (pairB (canon (unpairB s).1) (canon (unpairB s).2), (unpairB s).2))
      (g := fun p : List Bool × List Bool => twice^[p.2.length] p.1)
      (m2_pair_build_polytime _ _ init hb) (m2_iterate_polytime twice 1 cpt_twice twice_len)
  exact cpt_binAdd_fun _ _ (cpt_unpairB1_1 run) (cpt_unpairB2_1 run)

private theorem computed (p : List Bool × List Bool) :
    compute (pairB p.1 p.2) = Nat.bits (Nat.gcd (val p.1) (val p.2)) := by
  simp only [compute, unpairB_pairB, canon_eq]
  exact read_after p.2.length (val p.1) (val p.2) (Or.inr (val_lt_two_pow p.2))

end PvsNP.Units.tf_fun_pair_gcd

theorem PvsNP.Units.tf_fun_pair_gcd :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.gcd (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))
          (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => tf_fun_pair_gcd.compute (fr_ladner.PEqualNP.Library.Universal.pairB p.1 p.2)) :=
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
        (f := fun p : List Bool × List Bool => fr_ladner.PEqualNP.Library.Universal.pairB p.1 p.2)
        (g := tf_fun_pair_gcd.compute) fr_ladner.PEqualNP.Library.Universal.cpt_pairB tf_fun_pair_gcd.cpt_compute
  exact (funext tf_fun_pair_gcd.computed) ▸ h
