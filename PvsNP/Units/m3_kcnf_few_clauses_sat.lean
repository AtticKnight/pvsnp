import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_kcnf_few_clauses_sat

private noncomputable def bad (V : Finset ℕ) (C : clause) : Finset (Finset ℕ) :=
  V.powerset.filter (fun A => evalClause A.toList C = false)

private lemma evalLiteral_false_of_evalClause_false (a : assgn) (C : clause)
    (hC : evalClause a C = false) {l : literal} (hl : l ∈ C) :
    evalLiteral a l = false := by
  cases h : evalLiteral a l with
  | false => rfl
  | true =>
    have htrue : evalClause a C = true := (evalClause_literal_iff a C).mpr ⟨l, hl, h⟩
    rw [hC] at htrue
    cases htrue

private lemma bad_card_le (V : Finset ℕ) (k : ℕ) (C : clause)
    (hlen : C.length = k) (hnodup : (C.map Prod.snd).Nodup)
    (hsub : ∀ l ∈ C, l.2 ∈ V) :
    (bad V C).card ≤ 2 ^ (V.card - k) := by
  classical
  let VC : Finset ℕ := (C.map Prod.snd).toFinset
  have hVC_sub : VC ⊆ V := by
    intro v hv
    simp only [VC, List.mem_toFinset, List.mem_map] at hv
    obtain ⟨l, hl, rfl⟩ := hv
    exact hsub l hl
  have hVC_card : VC.card = k := by
    simp only [VC, List.toFinset_card_of_nodup hnodup, List.length_map, hlen]
  have hcard_le : (bad V C).card ≤ (V \ VC).powerset.card := by
    apply Finset.card_le_card_of_injOn (fun A => A \ VC)
    · intro A hA
      simp only [Finset.mem_coe, bad, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
      intro v hv
      simp only [Finset.mem_sdiff] at hv ⊢
      exact ⟨hA.1 hv.1, hv.2⟩
    · intro A₁ hA₁ A₂ hA₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe, bad, Finset.mem_filter, Finset.mem_powerset] at hA₁ hA₂
      ext v
      by_cases hv : v ∈ VC
      · simp only [VC, List.mem_toFinset, List.mem_map] at hv
        obtain ⟨⟨s, v'⟩, hl, rfl⟩ := hv
        have hf1 := evalLiteral_false_of_evalClause_false A₁.toList C hA₁.2 hl
        have hf2 := evalLiteral_false_of_evalClause_false A₂.toList C hA₂.2 hl
        simp only [evalLiteral, evalVar, decide_eq_false_iff_not, Finset.mem_toList] at hf1 hf2
        cases s with
        | false =>
          have h1 : v' ∈ A₁ := by
            by_contra h
            exact hf1 (by simp [h])
          have h2 : v' ∈ A₂ := by
            by_contra h
            exact hf2 (by simp [h])
          exact ⟨fun _ => h2, fun _ => h1⟩
        | true =>
          have h1 : v' ∉ A₁ := by
            intro h
            exact hf1 (by simp [h])
          have h2 : v' ∉ A₂ := by
            intro h
            exact hf2 (by simp [h])
          exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      · have hmem : v ∈ A₁ \ VC ↔ v ∈ A₂ \ VC := by rw [heq]
        simp only [Finset.mem_sdiff, hv, not_false_eq_true, and_true] at hmem
        exact hmem
  calc
    (bad V C).card ≤ (V \ VC).powerset.card := hcard_le
    _ = 2 ^ (V \ VC).card := Finset.card_powerset (V \ VC)
    _ = 2 ^ (V.card - k) := by rw [Finset.card_sdiff_of_subset hVC_sub, hVC_card]

private noncomputable def badUnion (V : Finset ℕ) : List clause → Finset (Finset ℕ)
  | [] => ∅
  | C :: Cs => bad V C ∪ badUnion V Cs

private lemma badUnion_sub (V : Finset ℕ) : ∀ Cs : List clause, badUnion V Cs ⊆ V.powerset
  | [] => Finset.empty_subset _
  | _C :: Cs =>
    Finset.union_subset (Finset.filter_subset _ _) (badUnion_sub V Cs)

private lemma mem_badUnion_of_mem (V : Finset ℕ) (A : Finset ℕ) :
    ∀ {Cs : List clause} {C : clause}, C ∈ Cs → A ∈ bad V C → A ∈ badUnion V Cs
  | [], _, hC, _ => by cases hC
  | C' :: Cs, C, hC, hA => by
    simp only [badUnion, Finset.mem_union]
    rcases List.mem_cons.mp hC with rfl | hC
    · exact Or.inl hA
    · exact Or.inr (mem_badUnion_of_mem V A hC hA)

private lemma badUnion_card_le (V : Finset ℕ) (B : ℕ) :
    ∀ Cs : List clause, (∀ C ∈ Cs, (bad V C).card ≤ B) → (badUnion V Cs).card ≤ Cs.length * B
  | [], _ => by simp [badUnion]
  | C :: Cs, hB => by
    have h1 : (bad V C).card ≤ B := hB C List.mem_cons_self
    have h2 : (badUnion V Cs).card ≤ Cs.length * B :=
      badUnion_card_le V B Cs (fun C' hC' => hB C' (List.mem_cons_of_mem C hC'))
    have hu : (bad V C ∪ badUnion V Cs).card ≤ (bad V C).card + (badUnion V Cs).card :=
      Finset.card_union_le _ _
    simp only [badUnion, List.length_cons, Nat.succ_mul]
    omega

end PvsNP.Units.m3_kcnf_few_clauses_sat

theorem PvsNP.Units.m3_kcnf_few_clauses_sat :
    ∀ (k : ℕ) (N : cnf), (∀ C ∈ N, C.length = k ∧ (C.map Prod.snd).Nodup) →
      N.length < 2 ^ k → SAT N := by
  intro k N hN hlt
  cases N with
  | nil => exact ⟨[], rfl⟩
  | cons C₀ Ns =>
    classical
    let N' : cnf := C₀ :: Ns
    let V : Finset ℕ := (SAT_inNP.varsOfCnf N').toFinset
    have hsub : ∀ C ∈ N', ∀ l ∈ C, l.2 ∈ V := fun C hC l hl => by
      simp only [V, List.mem_toFinset]
      exact SAT_inNP.varsOfCnf_mem N' C l hC hl
    have hk_le : k ≤ V.card := by
      have h0 := hN C₀ List.mem_cons_self
      let VC₀ : Finset ℕ := (C₀.map Prod.snd).toFinset
      have hVC₀_sub : VC₀ ⊆ V := by
        intro v hv
        simp only [VC₀, List.mem_toFinset, List.mem_map] at hv
        obtain ⟨l, hl, rfl⟩ := hv
        exact hsub C₀ List.mem_cons_self l hl
      have hVC₀_card : VC₀.card = k := by
        simp only [VC₀, List.toFinset_card_of_nodup h0.2, List.length_map, h0.1]
      rw [← hVC₀_card]
      exact Finset.card_le_card hVC₀_sub
    have hU_card :
        (PvsNP.Units.m3_kcnf_few_clauses_sat.badUnion V N').card ≤ N'.length * 2 ^ (V.card - k) := by
      apply PvsNP.Units.m3_kcnf_few_clauses_sat.badUnion_card_le
      intro C hC
      have hCi := hN C hC
      exact PvsNP.Units.m3_kcnf_few_clauses_sat.bad_card_le V k C hCi.1 hCi.2 (hsub C hC)
    have hpow : 2 ^ k * 2 ^ (V.card - k) = 2 ^ V.card := by
      rw [← pow_add, Nat.add_sub_of_le hk_le]
    have hpos : 0 < 2 ^ (V.card - k) := Nat.pos_of_ne_zero (by positivity)
    have hlt_card :
        (PvsNP.Units.m3_kcnf_few_clauses_sat.badUnion V N').card < V.powerset.card := by
      rw [Finset.card_powerset, ← hpow]
      exact lt_of_le_of_lt hU_card (Nat.mul_lt_mul_of_pos_right hlt hpos)
    have hex : ∃ A ∈ V.powerset, A ∉ PvsNP.Units.m3_kcnf_few_clauses_sat.badUnion V N' := by
      by_contra hall
      push Not at hall
      have hle := Finset.card_le_card (show V.powerset ⊆ PvsNP.Units.m3_kcnf_few_clauses_sat.badUnion V N' from hall)
      omega
    obtain ⟨A, hA_mem, hA_not⟩ := hex
    refine ⟨A.toList, ?_⟩
    show evalCnf A.toList N' = true
    rw [evalCnf_clause_iff]
    intro C hC
    cases hcl : evalClause A.toList C with
    | true => rfl
    | false =>
      have hbad : A ∈ PvsNP.Units.m3_kcnf_few_clauses_sat.bad V C := by
        simp only [PvsNP.Units.m3_kcnf_few_clauses_sat.bad, Finset.mem_filter]
        exact ⟨hA_mem, hcl⟩
      exact absurd (PvsNP.Units.m3_kcnf_few_clauses_sat.mem_badUnion_of_mem V A hC hbad) hA_not
