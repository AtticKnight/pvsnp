import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_pair_add

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_div_const

def div3Step (r : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  let v := 2 * r.val + b.toNat
  (⟨v % 3, Nat.mod_lt _ (by decide)⟩, some (decide (3 ≤ v)))

def div3MSB : Fin 3 → List Bool → List Bool
  | _, [] => []
  | r, b :: xs =>
    let v := 2 * r.val + b.toNat
    decide (3 ≤ v) :: div3MSB ⟨v % 3, Nat.mod_lt _ (by decide)⟩ xs

theorem cpt_div3MSB :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (div3MSB ⟨0, by decide⟩) :=
  PvsNP.Units.m2_transducer_polytime (Fin 3) div3Step (fun _ => none) div3MSB
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ⟨0, by decide⟩

theorem cpt_stripZeros :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.tf_fun_pair_add.stripZeros :=
  PvsNP.Units.m2_transducer_polytime Bool
    (fun st b => if st then (true, some b) else if b then (true, some true) else (false, none))
    (fun _ => none)
    (fun st x => if st then x else PvsNP.Units.tf_fun_pair_add.stripZeros x)
    (fun st => by cases st <;> rfl)
    (fun st b x => by cases st <;> cases b <;> rfl)
    false

theorem div3MSB_len (r : Fin 3) (l : List Bool) : (div3MSB r l).length = l.length := by
  induction l generalizing r with
  | nil => rfl
  | cons b xs ih =>
    simp only [div3MSB, List.length_cons]
    exact congrArg Nat.succ (ih _)

def msbVal (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.reverse.map Bool.toNat)

theorem msbVal_cons (b : Bool) (xs : List Bool) :
    msbVal (b :: xs) = msbVal xs + 2 ^ xs.length * b.toNat := by
  simp only [msbVal, List.reverse_cons, List.map_append, List.map_singleton]
  have h := PvsNP.Units.tf_fun_pair_add.ofDigits_append_singleton (xs.reverse.map Bool.toNat) b.toNat
  simp only [List.length_map, List.length_reverse] at h
  exact h

theorem div3_bit_eq (r : Fin 3) (b : Bool) :
    3 * (decide (3 ≤ 2 * r.val + b.toNat)).toNat + (2 * r.val + b.toNat) % 3 =
      2 * r.val + b.toNat := by
  rcases r with ⟨n, hn⟩
  dsimp only
  match n with
  | 0 => cases b <;> simp
  | 1 => cases b <;> simp
  | 2 => cases b <;> simp
  | _ + 3 => omega

theorem div3MSB_val (r : Fin 3) (l : List Bool) :
    msbVal (div3MSB r l) = (r.val * 2 ^ l.length + msbVal l) / 3 := by
  induction l generalizing r with
  | nil =>
    have hr := r.isLt
    simp only [div3MSB, msbVal, List.reverse_nil, List.map_nil, Nat.ofDigits_nil,
      List.length_nil, pow_zero, mul_one, Nat.add_zero]
    omega
  | cons b xs ih =>
    simp only [div3MSB]
    rw [msbVal_cons, div3MSB_len, ih]
    rw [msbVal_cons, List.length_cons, Nat.pow_succ]
    have hbit := div3_bit_eq r b
    have hnum : ((2 * r.val + b.toNat) % 3) * 2 ^ xs.length + msbVal xs +
        3 * (2 ^ xs.length * (decide (3 ≤ 2 * r.val + b.toNat)).toNat) =
        r.val * (2 ^ xs.length * 2) + (msbVal xs + 2 ^ xs.length * b.toNat) := by
      calc
        ((2 * r.val + b.toNat) % 3) * 2 ^ xs.length + msbVal xs +
            3 * (2 ^ xs.length * (decide (3 ≤ 2 * r.val + b.toNat)).toNat)
            = (3 * (decide (3 ≤ 2 * r.val + b.toNat)).toNat + (2 * r.val + b.toNat) % 3) *
                2 ^ xs.length + msbVal xs := by ring
        _ = (2 * r.val + b.toNat) * 2 ^ xs.length + msbVal xs := by rw [hbit]
        _ = r.val * (2 ^ xs.length * 2) + (msbVal xs + 2 ^ xs.length * b.toNat) := by ring
    have hdiv : (((2 * r.val + b.toNat) % 3) * 2 ^ xs.length + msbVal xs) / 3 +
        2 ^ xs.length * (decide (3 ≤ 2 * r.val + b.toNat)).toNat =
        (((2 * r.val + b.toNat) % 3) * 2 ^ xs.length + msbVal xs +
          3 * (2 ^ xs.length * (decide (3 ≤ 2 * r.val + b.toNat)).toNat)) / 3 :=
      (Nat.add_mul_div_left _ _ (by decide : 0 < 3)).symm
    rw [hdiv, hnum]

theorem div3_eq (x : List Bool) :
    (PvsNP.Units.tf_fun_pair_add.stripZeros (div3MSB ⟨0, by decide⟩ x.reverse)).reverse =
      Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) / 3) := by
  rw [PvsNP.Units.tf_fun_pair_add.stripZeros_reverse_eq_bits]
  have h := div3MSB_val ⟨0, by decide⟩ x.reverse
  dsimp only at h
  simp only [msbVal, List.reverse_reverse, zero_mul, Nat.zero_add] at h
  exact congrArg Nat.bits h

end PvsNP.Units.tf_fun_div_const

theorem PvsNP.Units.tf_fun_div_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) / 3)) := by
  have h1 := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    PvsNP.Units.m2_reverse_polytime PvsNP.Units.tf_fun_div_const.cpt_div3MSB
  have h2 := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    h1 PvsNP.Units.tf_fun_div_const.cpt_stripZeros
  have h3 := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    h2 PvsNP.Units.m2_reverse_polytime
  convert h3 using 1
  funext x
  exact (PvsNP.Units.tf_fun_div_const.div3_eq x).symm
