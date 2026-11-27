import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_canonical_cnf

lemma pairwise_lt_range : ∀ n : ℕ, (List.range n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨pairwise_lt_range n, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_range] at ha
    rw [List.mem_singleton] at hb
    omega

lemma sublist_eq_of_mem_iff :
    ∀ {l s t : List ℕ}, l.Pairwise (· < ·) →
      List.Sublist s l → List.Sublist t l → (∀ x, x ∈ s ↔ x ∈ t) → s = t
  | [], _, _, _, hs, ht, _ => by
    cases hs
    cases ht
    rfl
  | x :: r, s, t, hpw, hs, ht, hiff => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨hxl, hr⟩ := hpw
    cases hs with
    | cons _ hs' =>
      cases ht with
      | cons _ ht' =>
        exact sublist_eq_of_mem_iff hr hs' ht' hiff
      | cons_cons _ ht' =>
        have hxs : x ∈ s := (hiff x).mpr (List.mem_cons_self ..)
        have hxr : x ∈ r := hs'.subset hxs
        exact absurd (hxl x hxr) (Nat.lt_irrefl x)
    | cons_cons _ hs' =>
      cases ht with
      | cons _ ht' =>
        have hxt : x ∈ t := (hiff x).mp (List.mem_cons_self ..)
        have hxr : x ∈ r := ht'.subset hxt
        exact absurd (hxl x hxr) (Nat.lt_irrefl x)
      | cons_cons _ ht' =>
        refine congrArg (x :: ·) (sublist_eq_of_mem_iff hr hs' ht' fun y => ?_)
        constructor
        · intro hys
          have hne : y ≠ x := by
            have hyr : y ∈ r := hs'.subset hys
            have := hxl y hyr
            omega
          rcases List.mem_cons.mp ((hiff y).mp (List.mem_cons_of_mem x hys)) with rfl | hyt
          · exact absurd rfl hne
          · exact hyt
        · intro hyt
          have hne : y ≠ x := by
            have hyr : y ∈ r := ht'.subset hyt
            have := hxl y hyr
            omega
          rcases List.mem_cons.mp ((hiff y).mpr (List.mem_cons_of_mem x hyt)) with rfl | hys
          · exact absurd rfl hne
          · exact hys

lemma evalClause_canonical_iff (n : ℕ) (a : assgn) (T : List var)
    (hT : List.Sublist T (List.range n)) :
    evalClause a ((List.range n).map (fun v => (!decide (v ∈ T), v))) = true ↔
      T ≠ (List.range n).filter (fun v => decide (v ∈ a)) := by
  rw [evalClause_literal_iff]
  constructor
  · rintro ⟨l, hlmem, hleval⟩ hEq
    obtain ⟨v, hvrange, rfl⟩ := List.mem_map.mp hlmem
    simp only [evalLiteral, evalVar] at hleval
    rw [hEq] at hleval
    have hvmem : v ∈ (List.range n).filter (fun u => decide (u ∈ a)) ↔ v ∈ a := by
      simp [hvrange]
    by_cases hva : v ∈ a
    · have hvT : v ∈ (List.range n).filter (fun u => decide (u ∈ a)) := hvmem.mpr hva
      simp [hva, hvT] at hleval
    · have hvT : v ∉ (List.range n).filter (fun u => decide (u ∈ a)) := fun h => hva (hvmem.mp h)
      simp [hva, hvT] at hleval
  · intro hne
    have hnot : ¬ ∀ v : var, v ∈ T ↔ v ∈ (List.range n).filter (fun u => decide (u ∈ a)) :=
      fun hall => hne (sublist_eq_of_mem_iff (pairwise_lt_range n) hT List.filter_sublist hall)
    push Not at hnot
    obtain ⟨v, hv⟩ := hnot
    have hvrange : v ∈ List.range n := by
      rcases hv with ⟨hvT, _⟩ | ⟨_, hvS⟩
      · exact hT.subset hvT
      · exact (List.mem_filter.mp hvS).1
    refine ⟨(!decide (v ∈ T), v), List.mem_map.mpr ⟨v, hvrange, rfl⟩, ?_⟩
    simp only [evalLiteral, evalVar]
    rcases hv with ⟨hvT, hvS⟩ | ⟨hvT, hvS⟩
    · have hva : v ∉ a := fun h => hvS (List.mem_filter.mpr ⟨hvrange, decide_eq_true h⟩)
      simp [hvT, hva]
    · have hva : v ∈ a := decide_eq_true_eq.mp (List.mem_filter.mp hvS).2
      simp [hvT, hva]

end PvsNP.Units.m3_canonical_cnf

theorem PvsNP.Units.m3_canonical_cnf :
    ∀ (n : ℕ) (f : List var → Bool) (a : assgn),
      evalCnf a (((List.range n).sublists.filter (fun T => !f T)).map
        (fun T => (List.range n).map (fun v => (!decide (v ∈ T), v)))) =
        f ((List.range n).filter (fun v => decide (v ∈ a))) := by
  intro n f a
  let S : List var := (List.range n).filter (fun v => decide (v ∈ a))
  have hSsub : S ∈ (List.range n).sublists := List.mem_sublists.mpr List.filter_sublist
  apply Bool.eq_iff_iff.mpr
  rw [evalCnf_clause_iff]
  constructor
  · intro hall
    by_contra hne
    have hfS : f S = false := Bool.eq_false_iff.mpr hne
    have hSin : S ∈ (List.range n).sublists.filter (fun T => !f T) :=
      List.mem_filter.mpr ⟨hSsub, by simp [hfS]⟩
    have hsat := hall _ (List.mem_map.mpr ⟨S, hSin, rfl⟩)
    have hneq := (PvsNP.Units.m3_canonical_cnf.evalClause_canonical_iff n a S
      List.filter_sublist).mp hsat
    exact hneq rfl
  · intro hfS C hC
    obtain ⟨T, hTfilt, rfl⟩ := List.mem_map.mp hC
    obtain ⟨hTsub, hTf⟩ := List.mem_filter.mp hTfilt
    have hTS : T ≠ S := by
      intro hEq
      subst hEq
      have hfS' : f S = true := hfS
      simp [hfS'] at hTf
    exact (PvsNP.Units.m3_canonical_cnf.evalClause_canonical_iff n a T
      (List.mem_sublists.mp hTsub)).mpr hTS
