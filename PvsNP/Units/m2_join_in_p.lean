import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_union

set_option autoImplicit false

namespace PvsNP.Units.m2_join_in_p

inductive HState : Type
  | init | yes | no
  deriving DecidableEq

instance : Fintype HState where
  elems := { HState.init, HState.yes, HState.no }
  complete x := by cases x <;> simp

def hDelta (target : Bool) : HState → Bool → HState
  | .init, b => if b == target then .yes else .no
  | .yes, _ => .yes
  | .no, _ => .no

def hAcc : HState → Bool
  | .yes => true
  | _ => false

lemma foldl_yes (target : Bool) (xs : List Bool) :
    xs.foldl (hDelta target) .yes = .yes := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simpa [List.foldl, hDelta] using ih

lemma foldl_no (target : Bool) (xs : List Bool) :
    xs.foldl (hDelta target) .no = .no := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simpa [List.foldl, hDelta] using ih

lemma head_in_p (target : Bool) :
    ({x : List Bool | ∃ y : List Bool, x = target :: y} : Language Bool) ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_dfa_in_p HState (hDelta target) .init hAcc
  have hEq : ({x : List Bool | hAcc (x.foldl (hDelta target) .init) = true} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, x = target :: y} : Language Bool) := by
    ext x
    cases x with
    | nil => simp [hAcc]
    | cons b ys =>
      simp only [Set.mem_ofPred_eq, List.foldl_cons, hDelta]
      by_cases hb : b = target
      · subst hb
        simp [foldl_yes, hAcc]
      · have hbeq : (b == target) = false := beq_false_of_ne hb
        simp [hbeq, foldl_no, hAcc, hb]
  rw [← hEq]
  exact h

lemma tail_in_p {L : Language Bool} (hL : L ∈ PvsNP.P) :
    ({x : List Bool | x.tail ∈ L} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨f, hf, hdec⟩ := hL
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString List.tail :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => f x.tail) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp htail hf
  exact ⟨fun x => f x.tail, hcomp, fun x => hdec x.tail⟩

lemma cons_in_p (b : Bool) {L : Language Bool} (hL : L ∈ PvsNP.P) :
    ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) ∈ PvsNP.P := by
  have hEq : ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, x = b :: y} : Language Bool) ⊓
      ({x : List Bool | x.tail ∈ L} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, hy⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hy, rfl⟩
  rw [hEq]
  exact PvsNP.Units.m2_p_inter _ _ (head_in_p b) (tail_in_p hL)

end PvsNP.Units.m2_join_in_p

/-- P is closed under the join (disjoint union) of two languages (TM2). -/
theorem PvsNP.Units.m2_join_in_p :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈ PvsNP.P := by
  intro L₁ L₂ h1 h2
  have hEq : ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) =
      ({x : List Bool | ∃ y ∈ L₁, x = false :: y} : Language Bool) ⊔
      ({x : List Bool | ∃ y ∈ L₂, x = true :: y} : Language Bool) := by
    ext x
    rfl
  rw [hEq]
  exact PvsNP.Units.m2_p_union _ _
    (PvsNP.Units.m2_join_in_p.cons_in_p false h1)
    (PvsNP.Units.m2_join_in_p.cons_in_p true h2)
