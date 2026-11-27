import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_const_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_mod_const

private def step3 : (Fin 3 × Bool) → Bool → (Fin 3 × Bool)
  | (r, p), false => (r, !p)
  | (r, false), true => (⟨(r.val + 1) % 3, Nat.mod_lt _ (by decide)⟩, true)
  | (r, true), true => (⟨(r.val + 2) % 3, Nat.mod_lt _ (by decide)⟩, false)

private lemma foldl_step3 (x : List Bool) :
    ∀ (r : Fin 3) (p : Bool),
      (x.foldl step3 (r, p)).1.val =
        (r.val + (if p then 2 else 1) * Nat.ofDigits 2 (x.map Bool.toNat)) % 3 := by
  induction x with
  | nil =>
    intro r p
    simp [Nat.ofDigits, Nat.mod_eq_of_lt r.isLt]
  | cons b rest ih =>
    intro r p
    simp only [List.foldl_cons, List.map_cons, Nat.ofDigits_cons]
    cases b <;> cases p
    · rw [step3, ih]
      simp only [Bool.toNat_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
    · rw [step3, ih]
      simp only [Bool.toNat_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
    · rw [step3, ih]
      simp only [Bool.toNat_true, Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [step3, ih]
      simp only [Bool.toNat_true, Bool.false_eq_true, ↓reduceIte]
      omega

private lemma val_mod3_eq (x : List Bool) :
    (x.foldl step3 (⟨0, by decide⟩, false)).1.val =
      Nat.ofDigits 2 (x.map Bool.toNat) % 3 := by
  rw [foldl_step3]
  simp

lemma mod3_eq_in_p (k : ℕ) :
    ({x : List Bool | Nat.ofDigits 2 (x.map Bool.toNat) % 3 = k} : Language Bool) ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_dfa_in_p (Fin 3 × Bool) step3 (⟨0, by decide⟩, false)
    (fun s => decide (s.1.val = k))
  have hEq :
      ({x : List Bool | decide ((x.foldl step3 (⟨0, by decide⟩, false)).1.val = k) = true} : Language Bool) =
      ({x : List Bool | Nat.ofDigits 2 (x.map Bool.toNat) % 3 = k} : Language Bool) := by
    ext x
    show decide ((x.foldl step3 (⟨0, by decide⟩, false)).1.val = k) = true ↔
      Nat.ofDigits 2 (x.map Bool.toNat) % 3 = k
    rw [decide_eq_true_eq, val_mod3_eq]
  rwa [hEq] at h

end PvsNP.Units.tf_fun_mod_const

theorem PvsNP.Units.tf_fun_mod_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3)) := by
  obtain ⟨f1, hf1, h1⟩ := PvsNP.Units.tf_fun_mod_const.mod3_eq_in_p 1
  obtain ⟨f2, hf2, h2⟩ := PvsNP.Units.tf_fun_mod_const.mod3_eq_in_p 2
  have hinner := PvsNP.Units.m2_ite_polytime f2
    (fun _ : List Bool => [false, true]) (fun _ : List Bool => [])
    hf2 (PvsNP.Units.m2_const_polytime [false, true]) (PvsNP.Units.m2_const_polytime [])
  have houter := PvsNP.Units.m2_ite_polytime f1
    (fun _ : List Bool => [true])
    (fun x : List Bool => if f2 x = true then [false, true] else [])
    hf1 (PvsNP.Units.m2_const_polytime [true]) hinner
  have heq :
      (fun x : List Bool => if f1 x = true then [true] else if f2 x = true then [false, true] else []) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3)) := by
    funext x
    have hlt : Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 < 3 := Nat.mod_lt _ (by decide)
    have h1x : (Nat.ofDigits 2 (x.map Bool.toNat) % 3 = 1) ↔ f1 x = true := h1 x
    have h2x : (Nat.ofDigits 2 (x.map Bool.toNat) % 3 = 2) ↔ f2 x = true := h2 x
    set r := Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3
    interval_cases r
    · have hf1f : f1 x ≠ true := fun ht => by have := h1x.mpr ht; omega
      have hf2f : f2 x ≠ true := fun ht => by have := h2x.mpr ht; omega
      simp only [hf1f, hf2f, ↓reduceIte]
      decide
    · have hf1t : f1 x = true := h1x.mp rfl
      simp only [hf1t, ↓reduceIte]
      decide
    · have hf1f : f1 x ≠ true := fun ht => by have := h1x.mpr ht; omega
      have hf2t : f2 x = true := h2x.mp rfl
      simp only [hf1f, hf2t, ↓reduceIte]
      decide
  rwa [heq] at houter
