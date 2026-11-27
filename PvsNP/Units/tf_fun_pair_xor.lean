import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.m2_zip_bne_polytime

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_xor

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def nv (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem nv_cons (b : Bool) (l : List Bool) : nv (b :: l) = b.toNat + 2 * nv l := by
  simp [nv, Nat.ofDigits_cons]

theorem nv_append (l₁ l₂ : List Bool) : nv (l₁ ++ l₂) = nv l₁ + 2 ^ l₁.length * nv l₂ := by
  simp [nv, Nat.ofDigits_append]

theorem nv_falses (R : List Bool) : nv (R.map fun _ => false) = 0 := by
  induction R with
  | nil => rfl
  | cons c R ih => simp only [List.map_cons, nv_cons, ih]; rfl

theorem nv_pad (A R : List Bool) : nv (A ++ R.map fun _ => false) = nv A := by
  rw [nv_append, nv_falses]; simp

theorem xor_step (a b : Bool) (m n : ℕ) :
    (a.toNat + 2 * m) ^^^ (b.toNat + 2 * n) = (a != b).toNat + 2 * (m ^^^ n) := by
  have h1 : a.toNat + 2 * m = Nat.bit a m := by rw [Nat.bit_val]; ring
  have h2 : b.toNat + 2 * n = Nat.bit b n := by rw [Nat.bit_val]; ring
  rw [h1, h2, Nat.xor_bit, Nat.bit_val]
  ring

theorem nv_zip : ∀ (A B : List Bool), A.length = B.length →
    nv (List.zipWith (fun a b : Bool => a != b) A B) = nv A ^^^ nv B := by
  intro A
  induction A with
  | nil => intro B h; cases B with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a A ih => intro B h; cases B with
    | nil => simp at h
    | cons b B =>
      simp only [List.zipWith_cons_cons, nv_cons]
      rw [ih B (by simpa using h), xor_step]

theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def xF (p : List Bool × List Bool) : List Bool :=
  PvsNP.Units.tf_fun_pair_mul.stripLSB
    (List.zipWith (fun a b : Bool => a != b)
      ((unpairB (pairB p.1 p.2)).1 ++ (unpairB (pairB p.1 p.2)).2.map fun _ => false)
      ((unpairB (pairB p.1 p.2)).2 ++ (unpairB (pairB p.1 p.2)).1.map fun _ => false))

theorem xF_eq (p : List Bool × List Bool) : xF p = Nat.bits (nv p.1 ^^^ nv p.2) := by
  obtain ⟨A, B⟩ := p
  simp only [xF, unpairB_pairB]
  rw [PvsNP.Units.tf_fun_pair_mul.stripLSB_eq_bits]
  have e := nv_zip (A ++ B.map fun _ => false) (B ++ A.map fun _ => false)
    (by simp [Nat.add_comm])
  rw [nv_pad, nv_pad] at e
  exact congrArg Nat.bits e

theorem cpt_xF : ComputableInPolyTime encodePair (fun x : List Bool => x) xF := by
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
      (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a != b) p.1 p.2) :=
    PvsNP.Units.m2_zip_bne_polytime
  have hAll := cpt_comp (cpt_comp (cpt_comp hP (cpt_pairG hL hR)) hZ)
    PvsNP.Units.tf_fun_pair_mul.cpt_stripLSB
  exact cptE' hAll (fun _ => rfl)

end PvsNP.Units.tf_fun_pair_xor

theorem PvsNP.Units.tf_fun_pair_xor :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ^^^ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have h := PvsNP.Units.tf_fun_pair_xor.cpt_xF
  have e : PvsNP.Units.tf_fun_pair_xor.xF = fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ^^^ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) :=
    funext PvsNP.Units.tf_fun_pair_xor.xF_eq
  rw [e] at h
  exact h
