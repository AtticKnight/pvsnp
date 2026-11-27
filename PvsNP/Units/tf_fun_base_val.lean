import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tr_rel_val_dvd
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_base_val

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tr_rel_val_dvd

lemma val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val_nil]
  | cons b rest ih =>
    rw [val_cons, List.length_cons, pow_succ]
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    omega

lemma bits_eq_cons_div2 {n : ℕ} (hn : n ≠ 0) :
    Nat.bits n = decide (n % 2 = 1) :: Nat.bits (n / 2) := by
  by_cases hdiv : n / 2 = 0
  · have hn1 : n = 1 := by omega
    subst hn1
    decide
  · have hbit : Nat.bit (decide (n % 2 = 1)) (n / 2) = n := by
      cases h : decide (n % 2 = 1)
      · have : n % 2 = 0 := by
          have : n % 2 ≠ 1 := by simpa using h
          omega
        simp [Nat.bit]; omega
      · have : n % 2 = 1 := by simpa using h
        simp [Nat.bit]; omega
    conv_lhs => rw [← hbit]
    exact Nat.bits_append_bit (n / 2) (decide (n % 2 = 1)) (fun h => absurd h hdiv)

lemma val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp [val_nil]
    · rw [bits_eq_cons_div2 hn, val_cons, ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      cases h : decide (n % 2 = 1)
      · have : n % 2 = 0 := by
          have : n % 2 ≠ 1 := by simpa using h
          omega
        simp; omega
      · have : n % 2 = 1 := by simpa using h
        simp; omega

lemma bits_length_le_of_lt_pow : ∀ (k n : ℕ), n < 2 ^ k → (Nat.bits n).length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by simpa using hn
    subst h0; simp
  | succ k ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp
    · rw [bits_eq_cons_div2 h0, List.length_cons]
      have hdiv : n / 2 < 2 ^ k := by
        rw [pow_succ] at hn
        omega
      have := ih (n / 2) hdiv
      omega

lemma ofDigits3_append_singleton (xs : List ℕ) (d : ℕ) :
    Nat.ofDigits (3 : ℕ) (xs ++ [d]) = Nat.ofDigits (3 : ℕ) xs + 3 ^ xs.length * d := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.cons_append, Nat.ofDigits_cons, List.length_cons, ih, pow_succ]
    ring

def hornerStep (s : List Bool) : List Bool :=
  if !(unpairB s).1.isEmpty = true then
    pairB (unpairB s).1.tail
      (if (unpairB s).1.headD false = true then
        Nat.bits (val (unpairB s).2 + val ([true] ++ (unpairB s).2))
      else
        Nat.bits (val (unpairB s).2 + val ([false] ++ (unpairB s).2)))
  else
    s

lemma hornerStep_len (s : List Bool) : (hornerStep s).length ≤ s.length + 1 := by
  have h1 := unpairB_length s
  unfold hornerStep
  split_ifs with hne hhd
  · have hpos : 0 < (unpairB s).1.length := by
      cases h : (unpairB s).1 with
      | nil => simp [h] at hne
      | cons _ _ => simp
    have hv : val (unpairB s).2 < 2 ^ (unpairB s).2.length := val_lt_two_pow (unpairB s).2
    have hval1 : val (unpairB s).2 + val ([true] ++ (unpairB s).2) < 2 ^ ((unpairB s).2.length + 2) := by
      simp only [List.singleton_append, val_cons, Bool.toNat_true]
      rw [pow_succ, pow_succ]
      omega
    have hblen := bits_length_le_of_lt_pow ((unpairB s).2.length + 2) _ hval1
    simp only [pairB_length, List.length_tail]
    omega
  · have hpos : 0 < (unpairB s).1.length := by
      cases h : (unpairB s).1 with
      | nil => simp [h] at hne
      | cons _ _ => simp
    have hv : val (unpairB s).2 < 2 ^ (unpairB s).2.length := val_lt_two_pow (unpairB s).2
    have hval0 : val (unpairB s).2 + val ([false] ++ (unpairB s).2) < 2 ^ ((unpairB s).2.length + 2) := by
      simp only [List.singleton_append, val_cons, Bool.toNat_false]
      rw [pow_succ, pow_succ]
      omega
    have hblen := bits_length_le_of_lt_pow ((unpairB s).2.length + 2) _ hval0
    simp only [pairB_length, List.length_tail]
    omega
  · omega

lemma hornerStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString hornerStep := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2
  have hne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    (fun s => (unpairB s).1) (fun x => !x.isEmpty) h1 nonempty_poly
  have hhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    (fun s => (unpairB s).1) (fun x => x.headD false) h1 headD_false_poly
  have hp1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => ((unpairB s).2, [true] ++ (unpairB s).2)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ h2 (cpt_app2 (cpt_const [true]) h2)
  have hp0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => ((unpairB s).2, [false] ++ (unpairB s).2)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ h2 (cpt_app2 (cpt_const [false]) h2)
  have hadd1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun s => ((unpairB s).2, [true] ++ (unpairB s).2))
    (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2))
    hp1 PvsNP.Units.tf_fun_pair_add
  have hadd0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun s => ((unpairB s).2, [false] ++ (unpairB s).2))
    (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2))
    hp0 PvsNP.Units.tf_fun_pair_add
  have hacc := PvsNP.Units.m2_ite_polytime _ _ _ hhd hadd1 hadd0
  have hbody := cpt_pairB2 (cpt_tail1 h1) hacc
  exact PvsNP.Units.m2_ite_polytime _ _ _ hne hbody cpt_id

lemma hornerStep_cons (b : Bool) (u acc : List Bool) :
    ∃ acc' : List Bool,
      hornerStep (pairB (b :: u) acc) = pairB u acc' ∧
      val acc' = 3 * val acc + b.toNat := by
  cases b with
  | true =>
    refine ⟨Nat.bits (val acc + val ([true] ++ acc)), ?_, ?_⟩
    · unfold hornerStep; simp [unpairB_pairB]
    · rw [val_bits]; simp [val_cons]; omega
  | false =>
    refine ⟨Nat.bits (val acc + val ([false] ++ acc)), ?_, ?_⟩
    · unfold hornerStep; simp [unpairB_pairB]
    · rw [val_bits]; simp [val_cons]; omega

lemma hornerStep_iter (u v : List Bool) :
    ∀ acc : List Bool,
      ∃ acc' : List Bool,
        hornerStep^[u.length] (pairB (u ++ v) acc) = pairB v acc' ∧
        val acc' = val acc * 3 ^ u.length + Nat.ofDigits (3 : ℕ) (u.reverse.map Bool.toNat) := by
  induction u with
  | nil =>
    intro acc
    exact ⟨acc, rfl, by simp⟩
  | cons b u' ih =>
    intro acc
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.cons_append]
    obtain ⟨acc1, hstep, hval1⟩ := hornerStep_cons b (u' ++ v) acc
    rw [hstep]
    obtain ⟨acc', hiter, hval'⟩ := ih acc1
    refine ⟨acc', hiter, ?_⟩
    rw [hval', hval1, List.reverse_cons, List.map_append, List.map_singleton,
      ofDigits3_append_singleton, List.length_map, List.length_reverse, pow_succ]
    ring

lemma normalize_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (val x)) := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hnil : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun _ : List Bool => []) :=
    PvsNP.Units.m2_const_polytime []
  have hpair := PvsNP.Units.m2_pair_build_polytime (fun x : List Bool => x) (fun _ : List Bool => []) hid hnil
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, ([] : List Bool)))
    (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    hpair PvsNP.Units.tf_fun_pair_add
  have heq : ((fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) ∘
      (fun x : List Bool => (x, ([] : List Bool)))) =
      (fun x : List Bool => Nat.bits (val x)) := by
    funext x; simp [val]
  rwa [heq] at hcomp

theorem main_proof :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (3 : ℕ) (x.map Bool.toNat))) := by
  obtain ⟨ch⟩ := hornerStep_poly
  have hiter : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => hornerStep^[p.2.length] p.1) := by
    rw [← encodePair_eq]
    exact Iter.iter_polyTime hornerStep ch 1 hornerStep_len
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pairB x.reverse []) :=
    cpt_pairB2 PvsNP.Units.m2_reverse_polytime (cpt_const [])
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair := PvsNP.Units.m2_pair_build_polytime _ _ hinit hid
  have hrun := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    _ _ hpair hiter
  have hsnd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (fun s => (unpairB s).2) hrun cpt_unpairB2
  have hnorm := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ (fun x => Nat.bits (val x)) hsnd normalize_poly
  have heq : ((fun x : List Bool => Nat.bits (val x)) ∘
      ((fun s => (unpairB s).2) ∘
        ((fun p : List Bool × List Bool => hornerStep^[p.2.length] p.1) ∘
          (fun x : List Bool => (pairB x.reverse [], x))))) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (3 : ℕ) (x.map Bool.toNat))) := by
    funext x
    simp only [Function.comp_apply]
    obtain ⟨acc', hiter', hval'⟩ := hornerStep_iter x.reverse [] []
    simp only [List.append_nil, List.length_reverse, List.reverse_reverse, val_nil,
      Nat.zero_mul, Nat.zero_add] at hiter' hval'
    rw [hiter', unpairB_pairB, hval']
  rwa [heq] at hnorm

end PvsNP.Units.tf_fun_base_val

theorem PvsNP.Units.tf_fun_base_val :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (3 : ℕ) (x.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_base_val.main_proof
