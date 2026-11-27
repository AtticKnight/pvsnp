import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its transducer machine (fst_polyTime) is that of
github.com/brilliant-hq/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0).
-/

namespace PvsNP.Units.m2_z_length_finset_p

/-- Count the length, capped at `M + 1`. -/
def lenD (M : ℕ) : Fin (M + 2) × Bool → Bool → (Fin (M + 2) × Bool) × Option Bool
  | (c, s), b => ((⟨min (c.val + 1) (M + 1), by omega⟩, s && b), none)

def lenFin (A : Finset ℕ) (M : ℕ) (tally : Bool) : Fin (M + 2) × Bool → Option Bool
  | (c, s) => some ((tally → s) && decide (c.val ∈ A))

theorem lenRun (A : Finset ℕ) (M : ℕ) (tally : Bool) (l : List Bool) : ∀ (c : Fin (M + 2)) (s : Bool),
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun (lenD M) (lenFin A M tally) (c, s) l =
      [(tally → (s && decide (∀ b ∈ l, b = true))) && decide (min (c.val + l.length) (M + 1) ∈ A)] := by
  induction l with
  | nil =>
    intro c s
    have hc := c.isLt
    have e : min c.val (M + 1) = c.val := by omega
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, lenFin, e]
  | cons b l ih =>
    intro c s
    simp only [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, lenD, Option.toList_none, List.nil_append]
    rw [ih]
    have e : min (min (c.val + 1) (M + 1) + l.length) (M + 1) = min (c.val + (l.length + 1)) (M + 1) := by
      omega
    simp only [List.length_cons, e]
    cases s <;> cases b <;> simp

theorem min_mem (A : Finset ℕ) (n : ℕ) :
    min n (A.sup id + 1) ∈ A ↔ n ∈ A := by
  have hb : ∀ m ∈ A, m ≤ A.sup id := fun m hm => Finset.le_sup (f := id) hm
  by_cases h : n ≤ A.sup id
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega)]
    constructor
    · intro hm; have := hb _ hm; omega
    · intro hm; have := hb _ hm; omega

end PvsNP.Units.m2_z_length_finset_p

/-- The strings whose length lies in a finite set are in P (TM2): an automaton counting the length
up to just past the set's largest element decides them. -/
theorem PvsNP.Units.m2_z_length_finset_p :
    ∀ A : Finset ℕ, ({x : List Bool | x.length ∈ A} : Language Bool) ∈ PvsNP.P := by
  intro A
  refine ⟨fun x => decide (x.length ∈ A),
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime (fun x : List Bool => x) Computability.encodeBool _
      (PvsNP.Units.m2_z_length_finset_p.lenD (A.sup id)) (PvsNP.Units.m2_z_length_finset_p.lenFin A (A.sup id) false) (0, true)
      (fun x => ?_), fun x => ?_⟩
  · rw [PvsNP.Units.m2_z_length_finset_p.lenRun]
    simp only [Computability.encodeBool, Fin.val_zero, Nat.zero_add]
    have := PvsNP.Units.m2_z_length_finset_p.min_mem A x.length
    simp [this]
  · show _ ↔ decide _ = true
    simp only [decide_eq_true_eq]
    exact Iff.rfl
