import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_parity_direct_cnf

lemma sublist_eq_of_mem_iff :
    ∀ {l s t : List ℕ}, l.Nodup →
      List.Sublist s l → List.Sublist t l → (∀ x, x ∈ s ↔ x ∈ t) → s = t
  | [], _, _, _, hs, ht, _ => by
    cases hs
    cases ht
    rfl
  | x :: r, s, t, hpw, hs, ht, hiff => by
    rw [List.nodup_cons] at hpw
    obtain ⟨hxl, hr⟩ := hpw
    cases hs with
    | cons _ hs' =>
      cases ht with
      | cons _ ht' =>
        exact sublist_eq_of_mem_iff hr hs' ht' hiff
      | cons_cons _ ht' =>
        have hxs : x ∈ s := (hiff x).mpr (List.mem_cons_self ..)
        have hxr : x ∈ r := hs'.subset hxs
        exact absurd hxr hxl
    | cons_cons _ hs' =>
      cases ht with
      | cons _ ht' =>
        have hxt : x ∈ t := (hiff x).mp (List.mem_cons_self ..)
        have hxr : x ∈ r := ht'.subset hxt
        exact absurd hxr hxl
      | cons_cons _ ht' =>
        refine congrArg (x :: ·) (sublist_eq_of_mem_iff hr hs' ht' fun y => ?_)
        constructor
        · intro hys
          have hne : y ≠ x := by
            intro hyx
            have hyr : y ∈ r := hs'.subset hys
            rw [hyx] at hyr
            exact hxl hyr
          rcases List.mem_cons.mp ((hiff y).mp (List.mem_cons_of_mem x hys)) with h | hyt
          · exact absurd h hne
          · exact hyt
        · intro hyt
          have hne : y ≠ x := by
            intro hyx
            have hyr : y ∈ r := ht'.subset hyt
            rw [hyx] at hyr
            exact hxl hyr
          rcases List.mem_cons.mp ((hiff y).mpr (List.mem_cons_of_mem x hyt)) with h | hys
          · exact absurd h hne
          · exact hys

lemma evalClause_direct_iff (vs : List var) (hvs : vs.Nodup) (a : assgn) (T : List var)
    (hT : List.Sublist T vs) :
    evalClause a (vs.map (fun v => (decide (v ∉ T), v))) = true ↔
      T ≠ vs.filter (fun v => decide (v ∈ a)) := by
  rw [evalClause_literal_iff]
  constructor
  · rintro ⟨l, hlmem, hleval⟩ hEq
    obtain ⟨v, hvrange, rfl⟩ := List.mem_map.mp hlmem
    simp only [evalLiteral, evalVar] at hleval
    rw [hEq] at hleval
    have hvmem : v ∈ vs.filter (fun u => decide (u ∈ a)) ↔ v ∈ a := by
      simp [hvrange]
    by_cases hva : v ∈ a
    · have hvT : v ∈ vs.filter (fun u => decide (u ∈ a)) := hvmem.mpr hva
      simp [hva, hvT] at hleval
    · have hvT : v ∉ vs.filter (fun u => decide (u ∈ a)) := fun h => hva (hvmem.mp h)
      simp [hva, hvT] at hleval
  · intro hne
    have hnot : ¬ ∀ v : var, v ∈ T ↔ v ∈ vs.filter (fun u => decide (u ∈ a)) :=
      fun hall => hne (sublist_eq_of_mem_iff hvs hT List.filter_sublist hall)
    push Not at hnot
    obtain ⟨v, hv⟩ := hnot
    have hvrange : v ∈ vs := by
      rcases hv with ⟨hvT, _⟩ | ⟨_, hvS⟩
      · exact hT.subset hvT
      · exact (List.mem_filter.mp hvS).1
    refine ⟨(decide (v ∉ T), v), List.mem_map.mpr ⟨v, hvrange, rfl⟩, ?_⟩
    simp only [evalLiteral, evalVar]
    rcases hv with ⟨hvT, hvS⟩ | ⟨hvT, hvS⟩
    · have hva : v ∉ a := fun h => hvS (List.mem_filter.mpr ⟨hvrange, decide_eq_true h⟩)
      simp [hvT, hva]
    · have hva : v ∈ a := decide_eq_true_eq.mp (List.mem_filter.mp hvS).2
      simp [hvT, hva]

theorem main : ∀ (vs : List var) (p : Bool) (a : assgn), vs.Nodup →
      (evalCnf a ((vs.sublists.filter (fun T => decide (T.length % 2 = 1) != p)).map
          (fun T => vs.map (fun v => (decide (v ∉ T), v)))) = true ↔
        decide ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1) = p) := by
  intro vs p a hvs
  let S : List var := vs.filter (fun v => decide (v ∈ a))
  have hSsub : S ∈ vs.sublists := List.mem_sublists.mpr List.filter_sublist
  rw [evalCnf_clause_iff]
  constructor
  · intro hall
    by_contra hne
    have hSin : S ∈ vs.sublists.filter (fun T => decide (T.length % 2 = 1) != p) := by
      refine List.mem_filter.mpr ⟨hSsub, ?_⟩
      revert hne
      cases decide (S.length % 2 = 1) <;> cases p <;> simp
    have hsat := hall _ (List.mem_map.mpr ⟨S, hSin, rfl⟩)
    have hneq := (evalClause_direct_iff vs hvs a S List.filter_sublist).mp hsat
    exact hneq rfl
  · intro hfS C hC
    obtain ⟨T, hTfilt, rfl⟩ := List.mem_map.mp hC
    obtain ⟨hTsub, hTf⟩ := List.mem_filter.mp hTfilt
    have hTS : T ≠ S := by
      intro hEq
      rw [hEq] at hTf
      have hfS' : decide (S.length % 2 = 1) = p := hfS
      rw [hfS'] at hTf
      cases p <;> simp at hTf
    exact (evalClause_direct_iff vs hvs a T (List.mem_sublists.mp hTsub)).mpr hTS

end PvsNP.Units.m3_parity_direct_cnf

/-- The direct CNF of a parity constraint excludes exactly the points of the wrong parity. -/
theorem PvsNP.Units.m3_parity_direct_cnf :
    ∀ (vs : List var) (p : Bool) (a : assgn), vs.Nodup →
      (evalCnf a ((vs.sublists.filter (fun T => decide (T.length % 2 = 1) != p)).map
          (fun T => vs.map (fun v => (decide (v ∉ T), v)))) = true ↔
        decide ((vs.filter (fun v => decide (v ∈ a))).length % 2 = 1) = p) :=
  PvsNP.Units.m3_parity_direct_cnf.main
