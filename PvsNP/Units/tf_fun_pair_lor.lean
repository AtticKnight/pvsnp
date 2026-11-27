import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_zip_with_all
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.tf_fun_pred

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.tf_fun_pair_xor,
PvsNP.Units.tf_fun_zip_with_all, PvsNP.Units.tf_fun_succ, and PvsNP.Units.tf_fun_pred
of github.com/makedotfun/pvsnp (Apache License 2.0), whose machine combinators come from
github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_lor

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private def nv (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

private theorem nv_cons (b : Bool) (l : List Bool) : nv (b :: l) = b.toNat + 2 * nv l := by
  simp [nv, Nat.ofDigits_cons]

private theorem nv_append (l₁ l₂ : List Bool) : nv (l₁ ++ l₂) = nv l₁ + 2 ^ l₁.length * nv l₂ := by
  simp [nv, Nat.ofDigits_append]

private theorem nv_falses (R : List Bool) : nv (R.map fun _ => false) = 0 := by
  induction R with
  | nil => rfl
  | cons c R ih => simp only [List.map_cons, nv_cons, ih]; rfl

private theorem nv_pad (A R : List Bool) : nv (A ++ R.map fun _ => false) = nv A := by
  rw [nv_append, nv_falses]; simp

private theorem nv_bits (n : ℕ) : nv (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      set b : Bool := decide ((m + 1) % 2 = 1)
      set q : ℕ := (m + 1) / 2
      have hbit : m + 1 = Nat.bit b q := by
        cases hb : b
        · have hmod : (m + 1) % 2 = 0 := by
            have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
            omega
          change m + 1 = 2 * q
          omega
        · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
          change m + 1 = 2 * q + 1
          omega
      have hcond : q = 0 → b = true := by
        intro hq
        have hmod : (m + 1) % 2 = 1 := by omega
        exact decide_eq_true hmod
      have hlt : q < m + 1 := by omega
      rw [hbit, Nat.bits_append_bit q b hcond, nv_cons, ih q hlt]
      rw [← hbit]
      cases hb : b
      · have hmod : (m + 1) % 2 = 0 := by
          have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
          omega
        simp only [Bool.toNat_false]
        omega
      · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
        simp only [Bool.toNat_true]
        omega

private theorem lor_step (a b : Bool) (m n : ℕ) :
    (a.toNat + 2 * m) ||| (b.toNat + 2 * n) = (a || b).toNat + 2 * (m ||| n) := by
  have h1 : a.toNat + 2 * m = Nat.bit a m := by rw [Nat.bit_val]; ring
  have h2 : b.toNat + 2 * n = Nat.bit b n := by rw [Nat.bit_val]; ring
  have h3 : (a || b).toNat + 2 * (m ||| n) = Nat.bit (a || b) (m ||| n) := by
    rw [Nat.bit_val]; ring
  rw [h1, h2, h3]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_lor, Nat.testBit_bit_zero]
  | succ k => simp [Nat.testBit_lor, Nat.testBit_bit_succ]

private theorem nv_zip : ∀ (A B : List Bool), A.length = B.length →
    nv (List.zipWith (fun a b : Bool => a || b) A B) = nv A ||| nv B := by
  intro A
  induction A with
  | nil => intro B h; cases B with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a A ih => intro B h; cases B with
    | nil => simp at h
    | cons b B =>
      simp only [List.zipWith_cons_cons, nv_cons]
      rw [ih B (by simpa using h), lor_step]

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem cpt_norm :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => Nat.bits (nv x)) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun x : List Bool => Nat.bits (nv x - 1)) ∘
       (fun x : List Bool => Nat.bits (nv x + 1))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (nv x + 1))
      (fun x : List Bool => Nat.bits (nv x - 1))
      PvsNP.Units.tf_fun_succ PvsNP.Units.tf_fun_pred
  exact cptE' h (fun x => by simp only [Function.comp_apply, nv_bits]; simp)

def lorF (p : List Bool × List Bool) : List Bool :=
  Nat.bits (nv
    (List.zipWith (fun a b : Bool => a || b)
      ((unpairB (pairB p.1 p.2)).1 ++ (unpairB (pairB p.1 p.2)).2.map fun _ => false)
      ((unpairB (pairB p.1 p.2)).2 ++ (unpairB (pairB p.1 p.2)).1.map fun _ => false)))

theorem lorF_eq (p : List Bool × List Bool) : lorF p = Nat.bits (nv p.1 ||| nv p.2) := by
  obtain ⟨A, B⟩ := p
  simp only [lorF, unpairB_pairB]
  have e := nv_zip (A ++ B.map fun _ => false) (B ++ A.map fun _ => false)
    (by simp [Nat.add_comm])
  rw [nv_pad, nv_pad] at e
  exact congrArg Nat.bits e

theorem cpt_lorF : ComputableInPolyTime encodePair (fun x : List Bool => x) lorF := by
  have hP : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := cpt_pairB
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) := cpt_unpairB1
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) := cpt_unpairB2
  have hFalse : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun l : List Bool => l.map fun _ => false) := by
    refine filterMap_polyTime _ _ _ (fun _ : Bool => some false) ?_
    intro x; show x.map _ = x.filterMap _
    induction x with
    | nil => rfl
    | cons b t ih => simp only [List.map_cons, List.filterMap_cons, ih]
  have hL := cpt_app2 h1 (cpt_comp h2 hFalse)
  have hR := cpt_app2 h2 (cpt_comp h1 hFalse)
  have hZ : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a || b) p.1 p.2) :=
    PvsNP.Units.tf_fun_zip_with_all (fun a b => a || b)
  have hAll := cpt_comp (cpt_comp (cpt_comp hP (cpt_pairG hL hR)) hZ) cpt_norm
  exact cptE' hAll (fun _ => rfl)

end PvsNP.Units.tf_fun_pair_lor

theorem PvsNP.Units.tf_fun_pair_lor :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ||| Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have h := PvsNP.Units.tf_fun_pair_lor.cpt_lorF
  have e : PvsNP.Units.tf_fun_pair_lor.lorF = fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ||| Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) :=
    funext PvsNP.Units.tf_fun_pair_lor.lorF_eq
  rw [e] at h
  exact h
