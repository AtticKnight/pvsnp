import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tl_lang_len_prime_p

namespace PvsNP.Units.tl_lang_count_coprime_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-! ### Euclid by subtraction on unary pairs -/

def stepN (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 ≤ p.2 then (p.1, p.2 - p.1) else (p.1 - p.2, p.2)

def stepF (s : List Bool) : List Bool :=
  sel (if decide ((unpairB s).1.length ≤ (unpairB s).2.length) then [true] else [])
    (pairB (dropU (unpairB s).2 (unpairB s).1) (unpairB s).2)
    (pairB (unpairB s).1 (dropU (unpairB s).1 (unpairB s).2))

theorem cpt_stepF :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) stepF :=
  cpt_sel (cpt_le cpt_unpairB1 cpt_unpairB2)
    (cpt_pairB2 (cpt_dropU cpt_unpairB2 cpt_unpairB1) cpt_unpairB2)
    (cpt_pairB2 cpt_unpairB1 (cpt_dropU cpt_unpairB1 cpt_unpairB2))

theorem stepF_pair (A B : List Bool) :
    ∃ A' B', stepF (pairB A B) = pairB A' B' ∧
      (A'.length, B'.length) = stepN (A.length, B.length) := by
  by_cases h : A.length ≤ B.length
  · refine ⟨A, dropU A B, ?_, ?_⟩
    · simp [stepF, unpairB_pairB, h, sel]
    · simp [stepN, h, dropU_length]
  · refine ⟨dropU B A, B, ?_, ?_⟩
    · simp [stepF, unpairB_pairB, h, sel]
    · simp [stepN, h, dropU_length]

theorem stepF_length (s : List Bool) : (stepF s).length ≤ s.length + 1 := by
  have h := unpairB_length s
  unfold stepF
  apply sel_length <;> simp only [pairB_length, dropU_length] <;> omega

theorem iter_pair (m : ℕ) : ∀ A B : List Bool, ∃ A' B',
    stepF^[m] (pairB A B) = pairB A' B' ∧
      (A'.length, B'.length) = stepN^[m] (A.length, B.length) := by
  induction m with
  | zero => intro A B; exact ⟨A, B, rfl, rfl⟩
  | succ m ih =>
      intro A B
      obtain ⟨A1, B1, h1, h2⟩ := stepF_pair A B
      obtain ⟨A', B', h3, h4⟩ := ih A1 B1
      refine ⟨A', B', ?_, ?_⟩
      · rw [Function.iterate_succ_apply, h1, h3]
      · rw [Function.iterate_succ_apply, h4]
        have : (A1.length, B1.length) = stepN (A.length, B.length) := h2
        rw [this]

theorem gcd_stepN (p : ℕ × ℕ) : Nat.gcd (stepN p).1 (stepN p).2 = Nat.gcd p.1 p.2 := by
  unfold stepN
  split_ifs with h
  · exact Nat.gcd_sub_self_right h
  · have h' : p.2 ≤ p.1 := by omega
    exact Nat.gcd_sub_self_left h'

theorem gcd_iter (m : ℕ) (p : ℕ × ℕ) :
    Nat.gcd (stepN^[m] p).1 (stepN^[m] p).2 = Nat.gcd p.1 p.2 := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, gcd_stepN]

theorem zero_iter (m : ℕ) : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ m →
    (stepN^[m] p).1 = 0 ∨ (stepN^[m] p).2 = 0 := by
  induction m with
  | zero =>
      intro p hp
      left
      simp only [Function.iterate_zero, id_eq]
      omega
  | succ m ih =>
      intro p hp
      rw [Function.iterate_succ_apply]
      by_cases hz : p.1 = 0 ∨ p.2 = 0
      · have hfix : stepN p = p := by
          rcases hz with hz | hz <;> (ext <;> simp [stepN, hz])
        rw [hfix, Function.iterate_fixed hfix]
        exact hz
      · simp only [not_or] at hz
        apply ih
        unfold stepN
        split_ifs <;> simp only <;> omega

theorem gcd_eq_sum (m : ℕ) (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ m) :
    Nat.gcd p.1 p.2 = (stepN^[m] p).1 + (stepN^[m] p).2 := by
  rw [← gcd_iter m p]
  rcases zero_iter m p hp with h | h <;> simp [h]

/-! ### The decider -/

def zeroOne (b : Bool) : Option Bool := if b = false then some true else none

theorem cpt_ones : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x => x.filterMap (fun b => if b = true then some true else none)) :=
  filterMap_polyTime _ _ _ _ (fun _ => rfl)

theorem cpt_zeros : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x => x.filterMap (fun b => if b = false then some true else none)) :=
  filterMap_polyTime _ _ _ _ (fun _ => rfl)

theorem len_ones (x : List Bool) :
    (x.filterMap (fun b => if b = true then some true else none)).length = x.count true := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

theorem len_zeros (x : List Bool) :
    (x.filterMap (fun b => if b = false then some true else none)).length = x.count false := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

theorem count_add (x : List Bool) : x.count true + x.count false = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp <;> omega

def runF (x : List Bool) : List Bool :=
  stepF^[x.length] (pairB (x.filterMap (fun b => if b = true then some true else none))
    (x.filterMap (fun b => if b = false then some true else none)))

def finalU (x : List Bool) : List Bool :=
  sel ((unpairB (runF x)).1 ++ (unpairB (runF x)).2) [true, true]
    ((unpairB (runF x)).1 ++ (unpairB (runF x)).2).tail

def deciderF (x : List Bool) : Bool := decide (finalU x = [])

theorem cpt_deciderF :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer deciderF := by
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) runF :=
    cpt_iterGrow cpt_stepF 1 stepF_length cpt_id (cpt_pairB2 cpt_ones cpt_zeros)
  have hw := cpt_app2 (cpt_unpairB1_1 hrun) (cpt_unpairB2_1 hrun)
  have hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) finalU :=
    cpt_sel hw (cpt_const [true, true]) (cpt_tail1 hw)
  have hdec : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x => decide (finalU x = [])) :=
    cpt_comp hu PvsNP.Units.tl_lang_len_prime_p.cpt_isEmpty
  exact hdec

theorem deciderF_spec (x : List Bool) :
    Nat.gcd (x.count true) (x.count false) = 1 ↔ deciderF x = true := by
  obtain ⟨A', B', hr, hl⟩ := iter_pair x.length
    (x.filterMap (fun b => if b = true then some true else none))
    (x.filterMap (fun b => if b = false then some true else none))
  rw [len_ones, len_zeros] at hl
  have hcount := count_add x
  have hg := gcd_eq_sum x.length (x.count true, x.count false) (by simp only; omega)
  rw [← hl] at hg
  have hrun : runF x = pairB A' B' := hr
  have hfin : (deciderF x = true) ↔ (A' ++ B' = [] → False) ∧ (A' ++ B').tail = [] := by
    simp only [deciderF, finalU, hrun, unpairB_pairB, decide_eq_true_eq, sel]
    by_cases h : A' ++ B' = []
    · simp [h]
    · simp [h]
  rw [hfin]
  simp only at hg
  rw [hg]
  have hlen : (A' ++ B').length = A'.length + B'.length := List.length_append ..
  constructor
  · intro h
    refine ⟨fun he => ?_, ?_⟩
    · rw [he] at hlen; simp at hlen; omega
    · apply List.eq_nil_of_length_eq_zero
      simp only [List.length_tail]; omega
  · rintro ⟨hne, hnil⟩
    have h1 : (A' ++ B').length - 1 = 0 := by
      have := congrArg List.length hnil
      simpa only [List.length_tail, List.length_nil] using this
    have h2 : (A' ++ B').length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    omega

theorem main :
    ({x : List Bool | Nat.gcd (x.count true) (x.count false) = 1} : Language Bool) ∈ PvsNP.P :=
  ⟨deciderF, cpt_deciderF, deciderF_spec⟩

end PvsNP.Units.tl_lang_count_coprime_p

theorem PvsNP.Units.tl_lang_count_coprime_p :
    ({x : List Bool | Nat.gcd (x.count true) (x.count false) = 1} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_count_coprime_p.main
