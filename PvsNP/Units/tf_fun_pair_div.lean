import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.m2_tm_binary_half_double
import PvsNP.Units.m2_binary_le_polytime

/-
Built on the settled units PvsNP.Units.fr_ladner (pairB/unpairB, cpt_sel, cpt_app2, cpt_bitFlag,
cpt_iterGrow, cpt_pairB, cpt_comp), m2_transducer_polytime, m2_polytime_comp, m2_pair_build_polytime,
m2_take_drop_length_polytime, tf_fun_pair_add, tf_fun_pair_mul, tf_fun_succ, m2_tm_binary_half_double
and m2_binary_le_polytime of github.com/makedotfun/pvsnp. Binary search for the quotient a / b
(lo * b <= a < hi * b), with lo and hi kept at a fixed width, over |a| + 1 halvings; b = 0 gives [].
The search scaffolding (val, fit, midB, the padded-width lemmas) follows our own unit file for
tl_lang_val_pow_p (integer square root by binary search, same campaign).
-/

namespace PvsNP.Units.tf_fun_pair_div

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev PT (f : List Bool → List Bool) : Prop :=
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f

def val (l : List Bool) : ℕ := Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

theorem val_nil : val [] = 0 := by simp [val]

theorem val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  unfold val
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [Nat.bit0_bits m (by omega), List.map_cons, Nat.ofDigits_cons, ih m (by omega)]
        simp
    · rw [Nat.bit1_bits m, List.map_cons, Nat.ofDigits_cons, ih m (by omega)]
      simp
      ring

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val_nil]
  | cons b t ih =>
    rw [val_cons, List.length_cons, pow_succ]
    have := Bool.toNat_le b
    omega

theorem val_zeros (l : List Bool) (h : ∀ b ∈ l, b = false) : val l = 0 := by
  induction l with
  | nil => exact val_nil
  | cons b t ih =>
    rw [val_cons, h b (by simp), ih (fun c hc => h c (by simp [hc]))]
    rfl

theorem val_take_pad (z : List Bool) (hz : ∀ b ∈ z, b = false) (v : List Bool) :
    ∀ k, v.length ≤ k → val ((v ++ z).take k) = val v := by
  induction v with
  | nil =>
    intro k _
    rw [List.nil_append, val_nil]
    exact val_zeros _ (fun b hb => hz b (List.mem_of_mem_take hb))
  | cons b v ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    rw [List.cons_append, List.take_succ_cons, val_cons, val_cons,
      ih k' (by simp at hk; omega)]

def fit (w v : List Bool) : List Bool := (v ++ w.map (fun _ => false)).take w.length

theorem fit_length (w v : List Bool) : (fit w v).length = w.length := by
  simp only [fit, List.length_take, List.length_append, List.length_map]
  omega

theorem val_fit (w : List Bool) (m : ℕ) (h : m < 2 ^ w.length) : val (fit w (Nat.bits m)) = m := by
  have hb : (Nat.bits m).length ≤ w.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h
  unfold fit
  rw [val_take_pad _ (fun b hb => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb; rfl) _ _ hb, val_bits]

def midB (lo hi : List Bool) : List Bool :=
  Nat.bits (Nat.ofDigits (2 : ℕ) ((Nat.bits (val lo + val hi)).map Bool.toNat) / 2)

def cflag (m b a : List Bool) : List Bool :=
  if decide (val (Nat.bits (val m * val b)) ≤ val a) then [true] else []

def divStep (s : List Bool) : List Bool :=
  let lo := (unpairB s).1
  let hi := (unpairB (unpairB s).2).1
  let x := (unpairB (unpairB s).2).2
  let m := midB lo hi
  let cf := cflag m (unpairB x).2 (unpairB x).1
  pairB (sel cf lo (fit lo m)) (pairB (sel cf (fit hi m) hi) x)

def initS (x : List Bool) : List Bool :=
  pairB (fit (true :: (unpairB x).1) [])
    (pairB (fit (true :: (unpairB x).1) (Nat.bits (val (unpairB x).1 + 1))) x)

def zflag (x : List Bool) : List Bool :=
  if decide (val (unpairB x).2 ≤ val []) then [true] else []

def G (x : List Bool) : List Bool :=
  sel (zflag x)
    (Nat.bits (val (unpairB (divStep^[(true :: (unpairB x).1).length] (initS x))).1 + val [])) []

/-! Poly-time pieces. -/

theorem un1 {F u : List Bool → List Bool} (hF : PT F) (hu : PT u) : PT (fun s => F (u s)) :=
  PvsNP.Units.m2_polytime_comp _ _ _ _ _ hu hF

theorem bin2 {F : List Bool × List Bool → List Bool}
    (hF : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString F)
    {u v : List Bool → List Bool} (hu : PT u) (hv : PT v) : PT (fun s => F (u s, v s)) :=
  PvsNP.Units.m2_polytime_comp _ _ _ _ _ (PvsNP.Units.m2_pair_build_polytime u v hu hv) hF

theorem bin2B {F : List Bool × List Bool → Bool}
    (hF : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer F)
    {u v : List Bool → List Bool} (hu : PT u) (hv : PT v) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => F (u s, v s)) :=
  PvsNP.Units.m2_polytime_comp _ _ _ _ _ (PvsNP.Units.m2_pair_build_polytime u v hu hv) hF

theorem mapFalse_poly : PT (fun u : List Bool => u.map (fun _ => false)) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some false))
    (fun _ => none)
    (fun _ u => u.map (fun _ => false))
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

theorem cpt_fit {w v : List Bool → List Bool} (hw : PT w) (hv : PT v) :
    PT (fun s => fit (w s) (v s)) := by
  have hz := un1 mapFalse_poly hw
  have happ := cpt_app2 hv hz
  have h := bin2 PvsNP.Units.m2_take_drop_length_polytime.1 hw happ
  exact h

theorem cpt_midB {u v : List Bool → List Bool} (hu : PT u) (hv : PT v) :
    PT (fun s => midB (u s) (v s)) := by
  have hadd := bin2 PvsNP.Units.tf_fun_pair_add hu hv
  have h := un1 PvsNP.Units.m2_tm_binary_half_double.1 hadd
  exact h

theorem cpt_cflag {u v w : List Bool → List Bool} (hu : PT u) (hv : PT v) (hw : PT w) :
    PT (fun s => cflag (u s) (v s) (w s)) := by
  have hp := bin2 PvsNP.Units.tf_fun_pair_mul hu hv
  have hle := bin2B PvsNP.Units.m2_binary_le_polytime hp hw
  have h := cpt_bitFlag hle
  exact h

theorem cpt_divStep : PT divStep := by
  have hlo : PT (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : PT (fun s => (unpairB s).2) := cpt_unpairB2
  have hhi : PT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hx : PT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hA : PT (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 hx
  have hB : PT (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 hx
  have hm := cpt_midB hlo hhi
  have hcf := cpt_cflag hm hB hA
  have hfl := cpt_fit hlo hm
  have hfh := cpt_fit hhi hm
  have h := cpt_pairB2 (cpt_sel hcf hlo hfl) (cpt_pairB2 (cpt_sel hcf hfh hhi) hx)
  exact h

theorem cpt_initS : PT initS := by
  have hW : PT (fun x : List Bool => true :: (unpairB x).1) := cpt_cons1 true cpt_unpairB1
  have hS := un1 PvsNP.Units.tf_fun_succ cpt_unpairB1
  have h0 := cpt_fit hW (cpt_const [])
  have h1 := cpt_fit hW hS
  have h := cpt_pairB2 h0 (cpt_pairB2 h1 cpt_id)
  exact h

theorem sel_length (f a b : List Bool) (n : ℕ) (ha : a.length = n) (hb : b.length = n) :
    (sel f a b).length = n := by
  unfold sel; split_ifs <;> assumption

theorem divStep_length (s : List Bool) : (divStep s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have e1 : ∀ f m : List Bool, (sel f (unpairB s).1 (fit (unpairB s).1 m)).length =
      (unpairB s).1.length := fun f m => sel_length _ _ _ _ rfl (fit_length _ _)
  have e2 : ∀ f m : List Bool, (sel f (fit (unpairB (unpairB s).2).1 m) (unpairB (unpairB s).2).1).length =
      (unpairB (unpairB s).2).1.length := fun f m => sel_length _ _ _ _ (fit_length _ _) rfl
  simp only [divStep, pairB_length, e1, e2]
  omega

theorem cpt_G : PT G := by
  have hIter := cpt_iterGrow cpt_divStep 2 divStep_length (cpt_cons1 true cpt_unpairB1) cpt_initS
  have hL := un1 cpt_unpairB1 hIter
  have hN := bin2 PvsNP.Units.tf_fun_pair_add hL (cpt_const [])
  have hZ := cpt_bitFlag (bin2B PvsNP.Units.m2_binary_le_polytime cpt_unpairB2 (cpt_const []))
  have h := cpt_sel hZ hN (cpt_const [])
  exact h

/-! The arithmetic of the search. -/

def stepD (A B : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if (p.1 + p.2) / 2 * B ≤ A then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

theorem stepD_inv (A B a b : ℕ) (h1 : a * B ≤ A) (h2 : A < b * B) (h3 : a < b) :
    (stepD A B (a, b)).1 * B ≤ A ∧ A < (stepD A B (a, b)).2 * B ∧
      (stepD A B (a, b)).1 < (stepD A B (a, b)).2 ∧
      (stepD A B (a, b)).2 - (stepD A B (a, b)).1 - 1 ≤ (b - a - 1) / 2 := by
  unfold stepD
  split_ifs with h
  · show (a + b) / 2 * B ≤ A ∧ A < b * B ∧ (a + b) / 2 < b ∧
      b - (a + b) / 2 - 1 ≤ (b - a - 1) / 2
    exact ⟨h, h2, by omega, by omega⟩
  · have hlt : A < (a + b) / 2 * B := Nat.lt_of_not_le h
    have hne : (a + b) / 2 ≠ a := by
      intro he
      rw [he] at hlt
      exact Nat.lt_irrefl _ (lt_of_le_of_lt h1 hlt)
    show a * B ≤ A ∧ A < (a + b) / 2 * B ∧ a < (a + b) / 2 ∧
      (a + b) / 2 - a - 1 ≤ (b - a - 1) / 2
    exact ⟨h1, hlt, by omega, by omega⟩

theorem stepD_iter (A B t : ℕ) (hB : 0 < B) :
    ((stepD A B)^[t] (0, A + 1)).1 * B ≤ A ∧
      A < ((stepD A B)^[t] (0, A + 1)).2 * B ∧
      ((stepD A B)^[t] (0, A + 1)).1 < ((stepD A B)^[t] (0, A + 1)).2 ∧
      ((stepD A B)^[t] (0, A + 1)).2 - ((stepD A B)^[t] (0, A + 1)).1 - 1 ≤ A / 2 ^ t := by
  induction t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, Nat.div_one]
    refine ⟨by simp, by nlinarith, by omega, by omega⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    generalize (stepD A B)^[t] (0, A + 1) = q at ih ⊢
    obtain ⟨a, b⟩ := q
    simp only at ih
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨g1, g2, g3, g4⟩ := stepD_inv A B a b h1 h2 h3
    refine ⟨g1, g2, g3, ?_⟩
    calc (stepD A B (a, b)).2 - (stepD A B (a, b)).1 - 1 ≤ (b - a - 1) / 2 := g4
      _ ≤ A / 2 ^ t / 2 := Nat.div_le_div_right h4
      _ = A / 2 ^ (t + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

theorem stepD_final (A B n : ℕ) (hA : A < 2 ^ n) (hB : 0 < B) :
    ((stepD A B)^[n + 1] (0, A + 1)).1 = A / B := by
  obtain ⟨h1, h2, h3, h4⟩ := stepD_iter A B (n + 1) hB
  generalize (stepD A B)^[n + 1] (0, A + 1) = q at h1 h2 h3 h4 ⊢
  obtain ⟨a, b⟩ := q
  simp only at h1 h2 h3 h4 ⊢
  have hz : A / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt (by rw [pow_succ]; omega)
  rw [hz] at h4
  have hb : b = a + 1 := by omega
  subst hb
  have e1 : a ≤ A / B := (Nat.le_div_iff_mul_le hB).mpr h1
  have e2 : A / B < a + 1 := (Nat.div_lt_iff_lt_mul hB).mpr h2
  omega

/-! The list machine follows the arithmetic. -/

theorem divStep_pair (lo hi a b : List Bool) (hw : lo.length = hi.length) :
    ∃ lo' hi', divStep (pairB lo (pairB hi (pairB a b))) = pairB lo' (pairB hi' (pairB a b)) ∧
      lo'.length = lo.length ∧ hi'.length = hi.length ∧
      (val lo', val hi') = stepD (val a) (val b) (val lo, val hi) := by
  have hlo := val_lt lo
  have hhi := val_lt hi
  rw [← hw] at hhi
  have hM : (val lo + val hi) / 2 < 2 ^ lo.length := by omega
  have hM' : (val lo + val hi) / 2 < 2 ^ hi.length := by rw [← hw]; exact hM
  have hs : divStep (pairB lo (pairB hi (pairB a b))) =
      pairB (sel (cflag (midB lo hi) b a) lo (fit lo (midB lo hi)))
        (pairB (sel (cflag (midB lo hi) b a) (fit hi (midB lo hi)) hi) (pairB a b)) := by
    simp only [divStep, unpairB_pairB]
  have hmid : midB lo hi = Nat.bits ((val lo + val hi) / 2) := by
    unfold midB
    have := val_bits (val lo + val hi)
    unfold val at this ⊢
    rw [this]
  by_cases hc : (val lo + val hi) / 2 * val b ≤ val a
  · have hcf : cflag (midB lo hi) b a = [true] := by
      unfold cflag
      rw [hmid, val_bits, val_bits]
      simp [hc]
    refine ⟨fit lo (midB lo hi), hi, ?_, fit_length _ _, rfl, ?_⟩
    · rw [hs, hcf]; simp [sel]
    · rw [hmid, val_fit _ _ hM]; simp [stepD, hc]
  · have hcf : cflag (midB lo hi) b a = [] := by
      unfold cflag
      rw [hmid, val_bits, val_bits]
      simp [hc]
    refine ⟨lo, fit hi (midB lo hi), ?_, rfl, fit_length _ _, ?_⟩
    · rw [hs, hcf]; simp [sel]
    · rw [hmid, val_fit _ _ hM']; simp [stepD, hc]

theorem iter_spec (a b : List Bool) (t : ℕ) : ∀ lo hi : List Bool, lo.length = hi.length →
    ∃ lo' hi', divStep^[t] (pairB lo (pairB hi (pairB a b))) = pairB lo' (pairB hi' (pairB a b)) ∧
      lo'.length = lo.length ∧ hi'.length = hi.length ∧
      (val lo', val hi') = (stepD (val a) (val b))^[t] (val lo, val hi) := by
  induction t with
  | zero => intro lo hi _; exact ⟨lo, hi, rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    intro lo hi hw
    obtain ⟨lo1, hi1, e1, hl1, hh1, hv1⟩ := divStep_pair lo hi a b hw
    obtain ⟨lo2, hi2, e2, hl2, hh2, hv2⟩ := ih lo1 hi1 (by rw [hl1, hh1, hw])
    refine ⟨lo2, hi2, ?_, by rw [hl2, hl1], by rw [hh2, hh1], ?_⟩
    · rw [Function.iterate_succ_apply, e1, e2]
    · rw [Function.iterate_succ_apply, ← hv1, hv2]

theorem G_spec (a b : List Bool) : G (pairB a b) = Nat.bits (val a / val b) := by
  have hG : G (pairB a b) = sel (if decide (val b ≤ val []) then [true] else [])
      (Nat.bits (val (unpairB (divStep^[(true :: a).length] (pairB (fit (true :: a) [])
        (pairB (fit (true :: a) (Nat.bits (val a + 1))) (pairB a b))))).1 + val [])) [] := by
    simp only [G, zflag, initS, unpairB_pairB]
  rw [hG]
  by_cases hb : val b = 0
  · rw [hb, Nat.div_zero]
    simp [sel, val_nil]
  · have hB : 0 < val b := Nat.pos_of_ne_zero hb
    have hA := val_lt a
    have hw : (fit (true :: a) []).length = (fit (true :: a) (Nat.bits (val a + 1))).length := by
      rw [fit_length, fit_length]
    obtain ⟨lo', hi', e, _, _, hv⟩ := iter_spec a b (true :: a).length _ _ hw
    have h0 : val (fit (true :: a) []) = 0 := by
      have := val_fit (true :: a) 0 (by positivity)
      simpa using this
    have h1 : val (fit (true :: a) (Nat.bits (val a + 1))) = val a + 1 :=
      val_fit _ _ (by rw [List.length_cons, pow_succ]; omega)
    rw [h0, h1, List.length_cons] at hv
    have hlo : val lo' = val a / val b := by
      have := congrArg Prod.fst hv
      simp only at this
      rw [this]
      exact stepD_final (val a) (val b) a.length hA hB
    have hsel : ¬ (decide (val b ≤ val []) = true) := by
      rw [val_nil, decide_eq_true_eq]; omega
    rw [if_neg hsel, e, unpairB_pairB]
    unfold sel
    rw [if_pos rfl, val_nil, Nat.add_zero]
    rw [hlo]

theorem cpt_ext {f f' : List Bool × List Bool → List Bool}
    (h : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) f)
    (e : ∀ a, f a = f' a) :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem main : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    (fun x : List Bool => x)
    (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) /
      Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  cpt_ext (cpt_comp cpt_pairB cpt_G) (fun p => G_spec p.1 p.2)

end PvsNP.Units.tf_fun_pair_div

theorem PvsNP.Units.tf_fun_pair_div :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) / Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_pair_div.main
