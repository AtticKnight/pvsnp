import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.tf_fun_pair_add

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_binary_sub_unary

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def val (x : List Bool) : ℕ := Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · rcases h with ⟨rfl, rfl⟩; simp [val]
    · have hcond : n = 0 → b = true := by intro hn; cases b <;> simp_all
      rw [Nat.bits_append_bit n b hcond, val_cons, ih, Nat.bit_val]
      omega

def binAdd (a b : List Bool) : List Bool := Nat.bits (val a + val b)

theorem cpt_binAdd_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binAdd (f s) (g s)) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_add

def normBin (x : List Bool) : List Bool := binAdd x []

theorem normBin_eq (x : List Bool) : normBin x = Nat.bits (val x) := by
  unfold normBin binAdd
  have h0 : val [] = 0 := rfl
  rw [h0, Nat.add_zero]

theorem cpt_normBin : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString normBin :=
  cpt_binAdd_fun _ _ cpt_id (cpt_const [])

def decRawD : Bool → Bool → Bool × Option Bool
  | true, false => (true, some true)
  | true, true => (false, some false)
  | false, b => (false, some b)

def decRaw (x : List Bool) : List Bool := fstRun decRawD (fun _ => none) true x

theorem cpt_decRaw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString decRaw :=
  fst_polyTime _ _ _ decRawD (fun _ => none) true (fun _ => rfl)

theorem decRawD_false (x : List Bool) : fstRun decRawD (fun _ => none) false x = x := by
  induction x with
  | nil => rfl
  | cons b tl ih => simp [fstRun, decRawD, ih]

theorem decRaw_length (x : List Bool) : (decRaw x).length = x.length := by
  unfold decRaw
  induction x with
  | nil => rfl
  | cons b tl ih =>
    cases b with
    | true => simp [fstRun, decRawD, decRawD_false]
    | false => simp [fstRun, decRawD, ih]

theorem val_decRaw {x : List Bool} (hpos : 0 < val x) : val (decRaw x) = val x - 1 := by
  induction x with
  | nil => simp [val] at hpos
  | cons b tl ih =>
    cases b with
    | true =>
      have hd : decRaw (true :: tl) = false :: tl := by
        simp [decRaw, fstRun, decRawD, decRawD_false]
      rw [hd, val_cons, val_cons]
      simp
    | false =>
      have hd : decRaw (false :: tl) = true :: decRaw tl := by
        simp [decRaw, fstRun, decRawD]
      rw [val_cons] at hpos
      have htl : 0 < val tl := by simp at hpos; omega
      rw [hd, val_cons, val_cons, ih htl]
      simp
      omega

def decStep (x : List Bool) : List Bool := sel (normBin x) [] (decRaw x)

theorem cpt_decStep : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString decStep :=
  cpt_sel cpt_normBin (cpt_const []) cpt_decRaw

theorem decStep_length (x : List Bool) : (decStep x).length ≤ x.length + 0 := by
  unfold decStep sel
  split_ifs
  · simp
  · rw [decRaw_length]; omega

theorem val_decStep (x : List Bool) : val (decStep x) = val x - 1 := by
  unfold decStep sel
  rw [normBin_eq]
  split_ifs with h
  · have hv0 : val x = 0 := by
      have := congrArg val h
      rw [val_bits] at this
      exact this
    rw [hv0]
    rfl
  · have hpos : 0 < val x := by
      by_contra hle
      have hv0 : val x = 0 := by omega
      rw [hv0] at h
      exact h rfl
    exact val_decRaw hpos

theorem val_decStep_iter (k : ℕ) (x : List Bool) : val (decStep^[k] x) = val x - k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, val_decStep]
    omega

def subFun (p : List Bool × List Bool) : List Bool :=
  normBin (decStep^[(unpairB (pairB p.1 p.2)).2.length] (unpairB (pairB p.1 p.2)).1)

theorem cpt_subFun : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString subFun := by
  have hiter : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => decStep^[(unpairB s).2.length] (unpairB s).1) :=
    cpt_iterGrow cpt_decStep 0 decStep_length cpt_unpairB2 cpt_unpairB1
  have hstr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => normBin (decStep^[(unpairB s).2.length] (unpairB s).1)) :=
    cpt_comp (g := normBin) hiter cpt_normBin
  unfold subFun
  exact cpt_comp (g := fun s => normBin (decStep^[(unpairB s).2.length] (unpairB s).1)) cpt_pairB hstr

theorem subFun_eq (p : List Bool × List Bool) :
    subFun p = Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - p.2.length) := by
  unfold subFun
  rw [unpairB_pairB, normBin_eq, val_decStep_iter]
  rfl

end PvsNP.Units.m2_tm_binary_sub_unary

theorem PvsNP.Units.m2_tm_binary_sub_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - p.2.length)) := by
  have heq : PvsNP.Units.m2_tm_binary_sub_unary.subFun =
      (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - p.2.length)) :=
    funext PvsNP.Units.m2_tm_binary_sub_unary.subFun_eq
  rw [← heq]
  exact PvsNP.Units.m2_tm_binary_sub_unary.cpt_subFun
