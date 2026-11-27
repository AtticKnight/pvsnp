import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_pair_mul

namespace PvsNP.Units.m2_tm_binary_shift_right_low

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem unpairB_len_le (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  unfold unpairB
  dsimp only
  cases hd0 : s.dropWhile id with
  | nil =>
    simp
  | cons b t =>
    rw [hd0] at hsplit
    have htake : (t.take (s.takeWhile id).length).length ≤ (s.takeWhile id).length :=
      List.length_take_le _ _
    have htd : (t.take (s.takeWhile id).length).length +
        (t.drop (s.takeWhile id).length).length = t.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.tail_cons, List.length_cons] at hsplit ⊢
    omega

def take1D : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

def take1 (l : List Bool) : List Bool :=
  fstRun take1D (fun _ => none) false l

private theorem take1_true : ∀ l : List Bool, fstRun take1D (fun _ => none) true l = []
  | [] => rfl
  | _ :: t => by simp [fstRun, take1D, take1_true t]

private theorem take1_eq (l : List Bool) : take1 l = l.take 1 := by
  cases l with
  | nil => rfl
  | cons b t => simp [take1, fstRun, take1D, take1_true]

private theorem cpt_take1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) take1 :=
  fst_polyTime _ _ _ take1D (fun _ => none) false (fun _ => rfl)

def splitStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1.tail ((unpairB s).2 ++ take1 (unpairB s).1)

private theorem splitStep_len_le (s : List Bool) : (splitStep s).length ≤ s.length + 2 := by
  have h1 := unpairB_len_le s
  have ht : (unpairB s).1.tail.length ≤ (unpairB s).1.length := by simp
  have ht1 : (take1 (unpairB s).1).length ≤ 1 := by
    rw [take1_eq]
    cases (unpairB s).1 <;> simp
  unfold splitStep
  simp only [pairB_length, List.length_append]
  omega

private theorem cpt_splitStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) splitStep :=
  cpt_pairB2 (cpt_tail1 cpt_unpairB1) (cpt_app2 cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_take1))

private theorem splitStep_iter : ∀ (k : ℕ) (a acc : List Bool),
    splitStep^[k] (pairB a acc) = pairB (a.drop k) (acc ++ a.take k)
  | 0, a, acc => by simp
  | k + 1, a, acc => by
    have hstep : splitStep (pairB a acc) = pairB a.tail (acc ++ a.take 1) := by
      simp [splitStep, unpairB_pairB, take1_eq]
    rw [Function.iterate_succ_apply, hstep, splitStep_iter k a.tail (acc ++ a.take 1)]
    cases a with
    | nil => simp
    | cons b t => simp [List.append_assoc]

def bval (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

private theorem bval_take_drop : ∀ (k : ℕ) (l : List Bool),
    bval l = bval (l.take k) + 2 ^ k * bval (l.drop k) ∧ bval (l.take k) < 2 ^ k
  | 0, l => by
    refine ⟨?_, ?_⟩
    · simp [bval]
    · simp [bval]
  | k + 1, [] => by
    have hpos : 0 < 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
    refine ⟨by simp [bval], by simpa [bval] using hpos⟩
  | k + 1, b :: t => by
    obtain ⟨ih_eq, ih_lt⟩ := bval_take_drop k t
    have hb_le : b.toNat ≤ 1 := by cases b <;> decide
    simp only [List.take_succ_cons, List.drop_succ_cons, bval, List.map_cons, Nat.ofDigits_cons,
      Nat.pow_succ'] at ih_eq ih_lt ⊢
    refine ⟨?_, ?_⟩
    · rw [ih_eq]
      ring
    · omega

private theorem bval_drop_eq_div (l : List Bool) (k : ℕ) :
    bval (l.drop k) = bval l / 2 ^ k := by
  obtain ⟨heq, hlt⟩ := bval_take_drop k l
  have hpos : 0 < 2 ^ k := Nat.one_le_pow k 2 (by decide)
  rw [heq, mul_comm (2 ^ k), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]

private theorem bval_take_eq_mod (l : List Bool) (k : ℕ) :
    bval (l.take k) = bval l % 2 ^ k := by
  obtain ⟨heq, hlt⟩ := bval_take_drop k l
  rw [heq, mul_comm (2 ^ k), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

def shiftFun (p : List Bool × List Bool) : List Bool :=
  PvsNP.Units.tf_fun_pair_mul.stripLSB
    (unpairB (splitStep^[p.2.length] (pairB p.1 []))).1

def lowFun (p : List Bool × List Bool) : List Bool :=
  PvsNP.Units.tf_fun_pair_mul.stripLSB
    (unpairB (splitStep^[p.2.length] (pairB p.1 []))).2

theorem cpt_shiftFun :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString shiftFun := by
  have henc : PvsNP.encodePair = encodePair := by
    funext ⟨_, _⟩
    rfl
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => pairB (unpairB z).1 []) :=
    cpt_pairB2 cpt_unpairB1 (cpt_const [])
  have hIter : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => splitStep^[(unpairB z).2.length] (pairB (unpairB z).1 [])) :=
    cpt_iterGrow cpt_splitStep 2 splitStep_len_le cpt_unpairB2 hInit
  have hDrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun z => (unpairB (splitStep^[(unpairB z).2.length] (pairB (unpairB z).1 []))).1) :=
    cpt_unpairB1_1 hIter
  have hBody0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ hDrop PvsNP.Units.tf_fun_pair_mul.cpt_stripLSB
  have hBody : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => shiftFun ((unpairB z).1, (unpairB z).2)) := hBody0
  unfold PvsNP.PolyTimeComputable PvsNP.encodeString
  rw [henc]
  exact cptp (cpt_comp cpt_pairB hBody) (fun q => by
    obtain ⟨a, b⟩ := q
    simp only [unpairB_pairB])

theorem cpt_lowFun :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString lowFun := by
  have henc : PvsNP.encodePair = encodePair := by
    funext ⟨_, _⟩
    rfl
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => pairB (unpairB z).1 []) :=
    cpt_pairB2 cpt_unpairB1 (cpt_const [])
  have hIter : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => splitStep^[(unpairB z).2.length] (pairB (unpairB z).1 [])) :=
    cpt_iterGrow cpt_splitStep 2 splitStep_len_le cpt_unpairB2 hInit
  have hTake : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun z => (unpairB (splitStep^[(unpairB z).2.length] (pairB (unpairB z).1 []))).2) :=
    cpt_unpairB2_1 hIter
  have hBody0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ hTake PvsNP.Units.tf_fun_pair_mul.cpt_stripLSB
  have hBody : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun z => lowFun ((unpairB z).1, (unpairB z).2)) := hBody0
  unfold PvsNP.PolyTimeComputable PvsNP.encodeString
  rw [henc]
  exact cptp (cpt_comp cpt_pairB hBody) (fun q => by
    obtain ⟨a, b⟩ := q
    simp only [unpairB_pairB])

theorem shiftFun_eq (p : List Bool × List Bool) :
    shiftFun p = Nat.bits (bval p.1 / 2 ^ p.2.length) := by
  rcases p with ⟨a, b⟩
  unfold shiftFun
  rw [splitStep_iter, unpairB_pairB, PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits]
  change Nat.bits (bval (a.drop b.length)) = Nat.bits (bval a / 2 ^ b.length)
  rw [bval_drop_eq_div]

theorem lowFun_eq (p : List Bool × List Bool) :
    lowFun p = Nat.bits (bval p.1 % 2 ^ p.2.length) := by
  rcases p with ⟨a, b⟩
  unfold lowFun
  rw [splitStep_iter, unpairB_pairB, List.nil_append,
    PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits]
  change Nat.bits (bval (a.take b.length)) = Nat.bits (bval a % 2 ^ b.length)
  rw [bval_take_eq_mod]

end PvsNP.Units.m2_tm_binary_shift_right_low

theorem PvsNP.Units.m2_tm_binary_shift_right_low :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) / 2 ^ p.2.length)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) % 2 ^ p.2.length)) := by
  refine ⟨?_, ?_⟩
  · have h := PvsNP.Units.m2_tm_binary_shift_right_low.cpt_shiftFun
    have heq : PvsNP.Units.m2_tm_binary_shift_right_low.shiftFun =
        (fun p : List Bool × List Bool =>
          Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) / 2 ^ p.2.length)) :=
      funext PvsNP.Units.m2_tm_binary_shift_right_low.shiftFun_eq
    rwa [heq] at h
  · have h := PvsNP.Units.m2_tm_binary_shift_right_low.cpt_lowFun
    have heq : PvsNP.Units.m2_tm_binary_shift_right_low.lowFun =
        (fun p : List Bool × List Bool =>
          Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) % 2 ^ p.2.length)) :=
      funext PvsNP.Units.m2_tm_binary_shift_right_low.lowFun_eq
    rwa [heq] at h
