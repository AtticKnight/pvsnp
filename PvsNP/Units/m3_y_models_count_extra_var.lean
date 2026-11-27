import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_models_count_extra_var

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
      cases hb with
      | cons _ hb' =>
        have hyb : y ∉ b := fun h => hnd.1 (hb'.subset h)
        exact absurd ((hmem y).mp List.mem_cons_self) hyb
      | cons_cons _ hb' =>
        congr 1
        apply sublist_eq_of_mem_iff hnd.2 ha' hb'
        intro x
        by_cases h : x = y
        · subst h
          exact ⟨fun hx => absurd (ha'.subset hx) hnd.1, fun hx => absurd (hb'.subset hx) hnd.1⟩
        · have := hmem x
          simpa [List.mem_cons, h] using this

private lemma evalCnf_congr {a₁ a₂ : assgn} {N : cnf}
    (h : ∀ C ∈ N, ∀ l ∈ C, evalVar a₁ l.2 = evalVar a₂ l.2) :
    evalCnf a₁ N = evalCnf a₂ N := by
  apply Bool.eq_iff_iff.mpr
  rw [evalCnf_clause_iff, evalCnf_clause_iff]
  refine forall₂_congr fun C hC => ?_
  rw [evalClause_literal_iff, evalClause_literal_iff]
  refine exists_congr fun l => and_congr_right fun hl => ?_
  cases l with
  | mk s v =>
    simp only [evalLiteral, h C hC (s, v) hl]

private lemma filter_range_succ_ne (n : ℕ) :
    (List.range (n + 1)).filter (fun x => decide (x ≠ n)) = List.range n := by
  rw [List.range_succ, List.filter_append]
  have h1 : (List.range n).filter (fun x => decide (x ≠ n)) = List.range n := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact Nat.ne_of_lt (List.mem_range.mp hx)
  rw [h1]
  simp

end PvsNP.Units.m3_y_models_count_extra_var

theorem PvsNP.Units.m3_y_models_count_extra_var :
  ∀ (n : ℕ) (N : cnf), (∀ C ∈ N, ∀ l ∈ C, l.2 < n) →
    ((List.range (n + 1)).sublists.filter (fun a => evalCnf a N)).length =
      2 * ((List.range n).sublists.filter (fun a => evalCnf a N)).length := by
  intro n N hlt
  classical
  let S₁ : List (List ℕ) := (List.range (n + 1)).sublists.filter (fun a => evalCnf a N)
  let S₀ : List (List ℕ) := (List.range n).sublists.filter (fun a => evalCnf a N)
  have hS₁_nd : S₁.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have hS₀_nd : S₀.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have hbij : S₁.toFinset.card = (S₀.toFinset ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij (fun a _ => (a.filter (fun x => decide (x ≠ n)), decide (n ∈ a))) ?_ ?_ ?_
    · intro a ha
      simp only [S₁, List.mem_toFinset, List.mem_filter, List.mem_sublists] at ha
      simp only [Finset.mem_product, Finset.mem_univ, and_true, S₀, List.mem_toFinset,
        List.mem_filter, List.mem_sublists]
      refine ⟨?_, ?_⟩
      · have hsub := ha.1.filter (fun x => decide (x ≠ n))
        rwa [m3_y_models_count_extra_var.filter_range_succ_ne] at hsub
      · rw [← ha.2]
        apply m3_y_models_count_extra_var.evalCnf_congr
        intro C hC l hl
        have hne : l.2 ≠ n := Nat.ne_of_lt (hlt C hC l hl)
        simp [evalVar, List.mem_filter, hne]
    · intro a₁ ha₁ a₂ ha₂ heq
      simp only [S₁, List.mem_toFinset, List.mem_filter, List.mem_sublists] at ha₁ ha₂
      have hf : a₁.filter (fun x => decide (x ≠ n)) = a₂.filter (fun x => decide (x ≠ n)) :=
        congrArg Prod.fst heq
      have hm : decide (n ∈ a₁) = decide (n ∈ a₂) := congrArg Prod.snd heq
      apply m3_y_models_count_extra_var.sublist_eq_of_mem_iff List.nodup_range ha₁.1 ha₂.1
      intro x
      by_cases hx : x = n
      · subst hx
        simpa using congrArg (· = true) hm
      · have := congrArg (fun l => x ∈ l) hf
        simpa [List.mem_filter, hx] using this
    · rintro ⟨b, flag⟩ hb
      simp only [Finset.mem_product, Finset.mem_univ, and_true, S₀, List.mem_toFinset,
        List.mem_filter, List.mem_sublists] at hb
      have hnb : n ∉ b := fun h => Nat.lt_irrefl n (List.mem_range.mp (hb.1.subset h))
      have hbf : b.filter (fun x => decide (x ≠ n)) = b := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        exact Nat.ne_of_lt (List.mem_range.mp (hb.1.subset hx))
      cases flag with
      | false =>
        refine ⟨b, ?_, ?_⟩
        · simp only [S₁, List.mem_toFinset, List.mem_filter, List.mem_sublists]
          refine ⟨hb.1.trans ?_, hb.2⟩
          rw [List.range_succ]
          exact List.sublist_append_left (List.range n) [n]
        · rw [hbf]
          simp [hnb]
      | true =>
        refine ⟨b ++ [n], ?_, ?_⟩
        · simp only [S₁, List.mem_toFinset, List.mem_filter, List.mem_sublists]
          refine ⟨?_, ?_⟩
          · rw [List.range_succ]
            exact hb.1.append (List.Sublist.refl [n])
          · rw [← hb.2]
            apply m3_y_models_count_extra_var.evalCnf_congr
            intro C hC l hl
            have hne : l.2 ≠ n := Nat.ne_of_lt (hlt C hC l hl)
            simp [evalVar, hne]
        · rw [List.filter_append, hbf]
          simp
  calc S₁.length
      = S₁.toFinset.card := (List.toFinset_card_of_nodup hS₁_nd).symm
    _ = (S₀.toFinset ×ˢ (Finset.univ : Finset Bool)).card := hbij
    _ = S₀.toFinset.card * (Finset.univ : Finset Bool).card := Finset.card_product _ _
    _ = 2 * S₀.length := by
        rw [List.toFinset_card_of_nodup hS₀_nd, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]
