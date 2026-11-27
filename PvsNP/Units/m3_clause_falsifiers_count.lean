import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_clause_falsifiers_count

private lemma sublist_eq_of_mem_iff :
    ∀ {l a b : List ℕ}, l.Nodup → List.Sublist a l → List.Sublist b l → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], a, b, _, ha, hb, _ => by
    rw [List.sublist_nil.mp ha, List.sublist_nil.mp hb]
  | y :: l, a, b, hnd, ha, hb, hmem => by
    rw [List.nodup_cons] at hnd
    cases ha with
    | cons _ ha' =>
      have hya : y ∉ a := fun h => hnd.1 (ha'.subset h)
      cases hb with
      | cons _ hb' => exact sublist_eq_of_mem_iff hnd.2 ha' hb' hmem
      | cons_cons _ hb' => exact absurd ((hmem y).mpr List.mem_cons_self) hya
    | cons_cons _ ha' =>
      rename_i a'
      cases hb with
      | cons _ hb' =>
        have hyb : y ∉ b := fun h => hnd.1 (hb'.subset h)
        exact absurd ((hmem y).mp List.mem_cons_self) hyb
      | cons_cons _ hb' =>
        rename_i b'
        congr 1
        apply sublist_eq_of_mem_iff hnd.2 ha' hb'
        intro x
        by_cases h : x = y
        · subst h
          exact ⟨fun hx => absurd (ha'.subset hx) hnd.1, fun hx => absurd (hb'.subset hx) hnd.1⟩
        · have := hmem x
          simpa [List.mem_cons, h] using this

private lemma eq_of_mem_of_snd_eq :
    ∀ {C : clause}, (C.map Prod.snd).Nodup → ∀ {l₁ l₂ : literal},
      l₁ ∈ C → l₂ ∈ C → l₁.2 = l₂.2 → l₁ = l₂
  | [], _, _, _, h1, _, _ => by cases h1
  | l :: C, hnd, l₁, l₂, h1, h2, hsnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1'
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · rfl
      · exact absurd ⟨l₂, h2', hsnd.symm⟩ hnd.1
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · exact absurd ⟨l₁, h1', hsnd⟩ hnd.1
      · exact eq_of_mem_of_snd_eq hnd.2 h1' h2' hsnd

private lemma evalLiteral_false_of_evalClause_false (a : assgn) (C : clause)
    (hC : evalClause a C = false) {l : literal} (hl : l ∈ C) :
    evalLiteral a l = false := by
  cases h : evalLiteral a l with
  | false => rfl
  | true =>
    have htrue : evalClause a C = true := (evalClause_literal_iff a C).mpr ⟨l, hl, h⟩
    rw [hC] at htrue
    cases htrue

private lemma evalClause_false_of_all_false (a : assgn) (C : clause)
    (h : ∀ l ∈ C, evalLiteral a l = false) :
    evalClause a C = false := by
  cases hcl : evalClause a C with
  | false => rfl
  | true =>
    obtain ⟨l, hl, hlt⟩ := (evalClause_literal_iff a C).mp hcl
    rw [h l hl] at hlt
    cases hlt

end PvsNP.Units.m3_clause_falsifiers_count

theorem PvsNP.Units.m3_clause_falsifiers_count :
    ∀ (n : ℕ) (C : clause), (C.map Prod.snd).Nodup → (∀ l ∈ C, l.2 < n) →
      ((List.range n).sublists.filter (fun a => !evalClause a C)).length = 2 ^ (n - C.length) := by
  intro n C hnodup hlt
  classical
  let S : List (List ℕ) := (List.range n).sublists.filter (fun a => !evalClause a C)
  have hS_nd : S.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  let VC : Finset ℕ := (C.map Prod.snd).toFinset
  let negVars : Finset ℕ := ((C.filter (fun l => !l.1)).map Prod.snd).toFinset
  have hVC_sub : VC ⊆ Finset.range n := by
    intro v hv
    simp only [VC, List.mem_toFinset, List.mem_map] at hv
    obtain ⟨l, hl, rfl⟩ := hv
    exact Finset.mem_range.mpr (hlt l hl)
  have hneg_sub : negVars ⊆ VC := by
    intro v hv
    simp only [negVars, VC, List.mem_toFinset, List.mem_map, List.mem_filter] at hv ⊢
    obtain ⟨l, ⟨hl, _⟩, rfl⟩ := hv
    exact ⟨l, hl, rfl⟩
  have hVC_card : VC.card = C.length := by
    simp only [VC, List.toFinset_card_of_nodup hnodup, List.length_map]
  have hbij : S.toFinset.card = (Finset.range n \ VC).powerset.card := by
    refine Finset.card_bij (fun a _ => a.toFinset \ VC) ?_ ?_ ?_
    · intro a ha
      simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists] at ha
      rw [Finset.mem_powerset]
      intro v hv
      simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_range] at hv ⊢
      exact ⟨List.mem_range.mp (ha.1.subset hv.1), hv.2⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists,
        Bool.not_eq_true'] at ha₁ ha₂
      apply PvsNP.Units.m3_clause_falsifiers_count.sublist_eq_of_mem_iff
        List.nodup_range ha₁.1 ha₂.1
      intro v
      by_cases hv : v ∈ VC
      · simp only [VC, List.mem_toFinset, List.mem_map] at hv
        obtain ⟨⟨s, v'⟩, hl, rfl⟩ := hv
        have hf1 := PvsNP.Units.m3_clause_falsifiers_count.evalLiteral_false_of_evalClause_false
          a₁ C ha₁.2 hl
        have hf2 := PvsNP.Units.m3_clause_falsifiers_count.evalLiteral_false_of_evalClause_false
          a₂ C ha₂.2 hl
        simp only [evalLiteral, evalVar] at hf1 hf2
        cases s with
        | false =>
          have h1 : v' ∈ a₁ := by by_contra h; simp [h] at hf1
          have h2 : v' ∈ a₂ := by by_contra h; simp [h] at hf2
          exact ⟨fun _ => h2, fun _ => h1⟩
        | true =>
          have h1 : v' ∉ a₁ := fun h => by simp [h] at hf1
          have h2 : v' ∉ a₂ := fun h => by simp [h] at hf2
          exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      · have hmem : v ∈ a₁.toFinset \ VC ↔ v ∈ a₂.toFinset \ VC := by rw [heq]
        simpa [Finset.mem_sdiff, List.mem_toFinset, hv] using hmem
    · intro B hB
      rw [Finset.mem_powerset] at hB
      let A : Finset ℕ := B ∪ negVars
      let a : List ℕ := (List.range n).filter (fun x => decide (x ∈ A))
      have ha_sub : List.Sublist a (List.range n) := List.filter_sublist
      have hA_sub : A ⊆ Finset.range n :=
        Finset.union_subset (hB.trans Finset.sdiff_subset) (hneg_sub.trans hVC_sub)
      have hmem_a : ∀ x, x ∈ a ↔ x ∈ A := by
        intro x
        simp only [a, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (hA_sub h), h⟩⟩
      have heval : evalClause a C = false := by
        apply PvsNP.Units.m3_clause_falsifiers_count.evalClause_false_of_all_false
        intro ⟨s, v⟩ hl
        simp only [evalLiteral, evalVar]
        cases s with
        | false =>
          have hvneg : v ∈ negVars := by
            simp only [negVars, List.mem_toFinset, List.mem_map, List.mem_filter]
            exact ⟨(false, v), ⟨hl, by simp⟩, rfl⟩
          have hva : v ∈ a := (hmem_a v).mpr (Finset.mem_union_right B hvneg)
          simp [hva]
        | true =>
          have hvVC : v ∈ VC := by
            simp only [VC, List.mem_toFinset, List.mem_map]
            exact ⟨(true, v), hl, rfl⟩
          have hvB : v ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 hvVC
          have hvneg : v ∉ negVars := by
            intro h
            simp only [negVars, List.mem_toFinset, List.mem_map, List.mem_filter] at h
            obtain ⟨l', ⟨hl', hfl'⟩, hveq⟩ := h
            have hle := PvsNP.Units.m3_clause_falsifiers_count.eq_of_mem_of_snd_eq
              hnodup hl' hl hveq
            subst hle
            simp at hfl'
          have hva : v ∉ a := by
            intro h
            rcases Finset.mem_union.mp ((hmem_a v).mp h) with h1 | h2
            · exact hvB h1
            · exact hvneg h2
          simp [hva]
      refine ⟨a, ?_, ?_⟩
      · simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists, heval,
          Bool.not_false, and_true]
        exact ha_sub
      · ext x
        simp only [Finset.mem_sdiff, List.mem_toFinset, hmem_a, A, Finset.mem_union]
        constructor
        · rintro ⟨hxB | hxneg, hxVC⟩
          · exact hxB
          · exact absurd (hneg_sub hxneg) hxVC
        · intro hxB
          exact ⟨Or.inl hxB, (Finset.mem_sdiff.mp (hB hxB)).2⟩
  calc S.length
      = S.toFinset.card := (List.toFinset_card_of_nodup hS_nd).symm
    _ = (Finset.range n \ VC).powerset.card := hbij
    _ = 2 ^ (Finset.range n \ VC).card := Finset.card_powerset _
    _ = 2 ^ ((Finset.range n).card - VC.card) := by rw [Finset.card_sdiff_of_subset hVC_sub]
    _ = 2 ^ (n - C.length) := by rw [Finset.card_range, hVC_card]
