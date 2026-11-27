import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_resolution_complete

private def ResClosed (S : Set clause) : Prop :=
  ∀ C ∈ S, ∀ D ∈ S, ∀ v : var, (true, v) ∈ C → (false, v) ∈ D →
    C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v))) ∈ S

private theorem evalClause_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLiteral a l = true := by
  simp only [evalClause, List.any_eq_true]

private theorem satisfiesCnf_iff (a : assgn) (N : cnf) :
    satisfiesCnf a N ↔ ∀ C ∈ N, evalClause a C = true := by
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]

private theorem evalLiteral_cons_ne (a : assgn) (v : var) (l : literal) (h : l.2 ≠ v) :
    evalLiteral (v :: a) l = evalLiteral a l := by
  simp only [evalLiteral, evalVar, List.mem_cons, h, false_or]
  rfl

private theorem evalLiteral_filter_ne (a : assgn) (v : var) (l : literal) (h : l.2 ≠ v) :
    evalLiteral (a.filter (· != v)) l = evalLiteral a l := by
  simp only [evalLiteral, evalVar, List.mem_filter, bne_iff_ne, ne_eq, h, not_false_eq_true,
    and_true]
  rfl

private theorem filter_comm {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).filter q = (l.filter q).filter p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hp : p a <;> cases hq : q a
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ite_false, ih]
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ite_false, ite_true, ih]
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ite_false, ite_true, ih]
    · simp only [List.filter_cons, hp, hq, ite_true, ih]

private theorem eq_nil_or_mem_of_filter_eq_nil {α : Type} [DecidableEq α] (x : α) (l : List α)
    (h : l.filter (fun y => decide (y ≠ x)) = []) : l = [] ∨ x ∈ l := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a t =>
    by_cases hax : a = x
    · subst hax
      exact Or.inr List.mem_cons_self
    · have hne : decide (a ≠ x) = true := decide_eq_true hax
      simp only [List.filter_cons, hne, ite_true] at h
      cases h

private theorem complete_aux (U : Finset var) :
    ∀ (N : cnf), (∀ C ∈ N, ∀ l ∈ C, l.2 ∈ U) → ¬ SAT N →
      ∀ (S : Set clause), (∀ C ∈ N, C ∈ S) → ResClosed S → [] ∈ S := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    intro N hvars hunsat S hNS _
    have hne : N ≠ [] := by
      intro hnil
      apply hunsat
      refine ⟨[], ?_⟩
      rw [hnil]
      rfl
    cases N with
    | nil => exact False.elim (hne rfl)
    | cons C Cs =>
      have hCnil : C = [] := by
        cases C with
        | nil => rfl
        | cons l ls =>
          exact False.elim (Finset.notMem_empty l.2 (hvars (l :: ls) List.mem_cons_self l List.mem_cons_self))
      rw [← hCnil]
      exact hNS C List.mem_cons_self
  | @insert v U' hvU ih =>
    intro N hvars hunsat S hNS hclosed
    -- Branch 0: set v = false
    let N₀ : cnf :=
      (N.filter (fun C => decide ((false, v) ∉ C))).map
        (fun C => C.filter (fun l => decide (l ≠ (true, v))))
    let S₀ : Set clause :=
      {E : clause | ∃ C ∈ S, (false, v) ∉ C ∧ E = C.filter (fun l => decide (l ≠ (true, v)))}
    have hvars₀ : ∀ E ∈ N₀, ∀ l ∈ E, l.2 ∈ U' := by
      intro E hE l hlE
      obtain ⟨C, hCf, rfl⟩ := List.mem_map.1 hE
      obtain ⟨hCN, hnotf⟩ := List.mem_filter.1 hCf
      have hnotf' : (false, v) ∉ C := of_decide_eq_true hnotf
      obtain ⟨hlC, hnet⟩ := List.mem_filter.1 hlE
      have hnet' : l ≠ (true, v) := of_decide_eq_true hnet
      have hlU : l.2 ∈ insert v U' := hvars C hCN l hlC
      rcases Finset.mem_insert.1 hlU with hlv | hlU'
      · rcases l with ⟨s, w⟩
        dsimp only at hlv
        subst hlv
        cases s with
        | true => exact False.elim (hnet' rfl)
        | false => exact False.elim (hnotf' hlC)
      · exact hlU'
    have hunsat₀ : ¬ SAT N₀ := by
      rintro ⟨a, ha⟩
      have ha' := (satisfiesCnf_iff a N₀).1 ha
      apply hunsat
      refine ⟨a.filter (· != v), (satisfiesCnf_iff _ N).2 ?_⟩
      intro C hCN
      rw [evalClause_iff]
      by_cases hf : (false, v) ∈ C
      · refine ⟨(false, v), hf, ?_⟩
        simp only [evalLiteral, evalVar, List.mem_filter, bne_self_eq_false, Bool.false_eq_true,
          and_false, decide_false]
        rfl
      · have hE : C.filter (fun l => decide (l ≠ (true, v))) ∈ N₀ :=
          List.mem_map.2 ⟨C, List.mem_filter.2 ⟨hCN, decide_eq_true hf⟩, rfl⟩
        obtain ⟨l, hlE, hla⟩ := (evalClause_iff a _).1 (ha' _ hE)
        obtain ⟨hlC, hnet⟩ := List.mem_filter.1 hlE
        have hnet' : l ≠ (true, v) := of_decide_eq_true hnet
        have hne : l.2 ≠ v := by
          intro hlv
          rcases l with ⟨s, w⟩
          dsimp only at hlv
          subst hlv
          cases s with
          | true => exact hnet' rfl
          | false => exact hf hlC
        exact ⟨l, hlC, by rwa [evalLiteral_filter_ne a v l hne]⟩
    have hNS₀ : ∀ E ∈ N₀, E ∈ S₀ := by
      intro E hE
      obtain ⟨C, hCf, rfl⟩ := List.mem_map.1 hE
      obtain ⟨hCN, hnotf⟩ := List.mem_filter.1 hCf
      exact ⟨C, hNS C hCN, of_decide_eq_true hnotf, rfl⟩
    have hclosed₀ : ResClosed S₀ := by
      intro E₁ hE₁ E₂ hE₂ w hw₁ hw₂
      obtain ⟨C₁, hC₁S, hC₁nf, rfl⟩ := hE₁
      obtain ⟨C₂, hC₂S, hC₂nf, rfl⟩ := hE₂
      obtain ⟨hw₁C, hw₁ne⟩ := List.mem_filter.1 hw₁
      obtain ⟨hw₂C, _⟩ := List.mem_filter.1 hw₂
      let R := C₁.filter (fun l => decide (l ≠ (true, w))) ++
        C₂.filter (fun l => decide (l ≠ (false, w)))
      have hRS : R ∈ S := hclosed C₁ hC₁S C₂ hC₂S w hw₁C hw₂C
      have hRnf : (false, v) ∉ R := by
        intro hmem
        rcases List.mem_append.1 hmem with h1 | h2
        · exact hC₁nf (List.mem_filter.1 h1).1
        · exact hC₂nf (List.mem_filter.1 h2).1
      refine ⟨R, hRS, hRnf, ?_⟩
      simp only [R, List.filter_append]
      exact congrArg₂ List.append (filter_comm _ _ _) (filter_comm _ _ _)
    have hnil₀ : [] ∈ S₀ := ih N₀ hvars₀ hunsat₀ S₀ hNS₀ hclosed₀
    obtain ⟨Cpos, hCposS, _, hCposf⟩ := hnil₀
    -- Branch 1: set v = true
    let N₁ : cnf :=
      (N.filter (fun C => decide ((true, v) ∉ C))).map
        (fun C => C.filter (fun l => decide (l ≠ (false, v))))
    let S₁ : Set clause :=
      {E : clause | ∃ D ∈ S, (true, v) ∉ D ∧ E = D.filter (fun l => decide (l ≠ (false, v)))}
    have hvars₁ : ∀ E ∈ N₁, ∀ l ∈ E, l.2 ∈ U' := by
      intro E hE l hlE
      obtain ⟨D, hDf, rfl⟩ := List.mem_map.1 hE
      obtain ⟨hDN, hnott⟩ := List.mem_filter.1 hDf
      have hnott' : (true, v) ∉ D := of_decide_eq_true hnott
      obtain ⟨hlD, hnef⟩ := List.mem_filter.1 hlE
      have hnef' : l ≠ (false, v) := of_decide_eq_true hnef
      have hlU : l.2 ∈ insert v U' := hvars D hDN l hlD
      rcases Finset.mem_insert.1 hlU with hlv | hlU'
      · rcases l with ⟨s, w⟩
        dsimp only at hlv
        subst hlv
        cases s with
        | true => exact False.elim (hnott' hlD)
        | false => exact False.elim (hnef' rfl)
      · exact hlU'
    have hunsat₁ : ¬ SAT N₁ := by
      rintro ⟨a, ha⟩
      have ha' := (satisfiesCnf_iff a N₁).1 ha
      apply hunsat
      refine ⟨v :: a, (satisfiesCnf_iff _ N).2 ?_⟩
      intro D hDN
      rw [evalClause_iff]
      by_cases ht : (true, v) ∈ D
      · refine ⟨(true, v), ht, ?_⟩
        simp only [evalLiteral, evalVar, List.mem_cons, true_or, decide_true]
      · have hE : D.filter (fun l => decide (l ≠ (false, v))) ∈ N₁ :=
          List.mem_map.2 ⟨D, List.mem_filter.2 ⟨hDN, decide_eq_true ht⟩, rfl⟩
        obtain ⟨l, hlE, hla⟩ := (evalClause_iff a _).1 (ha' _ hE)
        obtain ⟨hlD, hnef⟩ := List.mem_filter.1 hlE
        have hnef' : l ≠ (false, v) := of_decide_eq_true hnef
        have hne : l.2 ≠ v := by
          intro hlv
          rcases l with ⟨s, w⟩
          dsimp only at hlv
          subst hlv
          cases s with
          | true => exact ht hlD
          | false => exact hnef' rfl
        exact ⟨l, hlD, by rwa [evalLiteral_cons_ne a v l hne]⟩
    have hNS₁ : ∀ E ∈ N₁, E ∈ S₁ := by
      intro E hE
      obtain ⟨D, hDf, rfl⟩ := List.mem_map.1 hE
      obtain ⟨hDN, hnott⟩ := List.mem_filter.1 hDf
      exact ⟨D, hNS D hDN, of_decide_eq_true hnott, rfl⟩
    have hclosed₁ : ResClosed S₁ := by
      intro E₁ hE₁ E₂ hE₂ w hw₁ hw₂
      obtain ⟨C₁, hC₁S, hC₁nt, rfl⟩ := hE₁
      obtain ⟨C₂, hC₂S, hC₂nt, rfl⟩ := hE₂
      obtain ⟨hw₁C, _⟩ := List.mem_filter.1 hw₁
      obtain ⟨hw₂C, _⟩ := List.mem_filter.1 hw₂
      let R := C₁.filter (fun l => decide (l ≠ (true, w))) ++
        C₂.filter (fun l => decide (l ≠ (false, w)))
      have hRS : R ∈ S := hclosed C₁ hC₁S C₂ hC₂S w hw₁C hw₂C
      have hRnt : (true, v) ∉ R := by
        intro hmem
        rcases List.mem_append.1 hmem with h1 | h2
        · exact hC₁nt (List.mem_filter.1 h1).1
        · exact hC₂nt (List.mem_filter.1 h2).1
      refine ⟨R, hRS, hRnt, ?_⟩
      simp only [R, List.filter_append]
      exact congrArg₂ List.append (filter_comm _ _ _) (filter_comm _ _ _)
    have hnil₁ : [] ∈ S₁ := ih N₁ hvars₁ hunsat₁ S₁ hNS₁ hclosed₁
    obtain ⟨Cneg, hCnegS, _, hCnegf⟩ := hnil₁
    rcases eq_nil_or_mem_of_filter_eq_nil (true, v) Cpos hCposf.symm with hposNil | hposMem
    · rw [← hposNil]; exact hCposS
    · rcases eq_nil_or_mem_of_filter_eq_nil (false, v) Cneg hCnegf.symm with hnegNil | hnegMem
      · rw [← hnegNil]; exact hCnegS
      · have hres := hclosed Cpos hCposS Cneg hCnegS v hposMem hnegMem
        rw [← hCposf, ← hCnegf] at hres
        exact hres

private def listToFinset {α : Type} [DecidableEq α] : List α → Finset α
  | [] => ∅
  | a :: t => insert a (listToFinset t)

private theorem mem_listToFinset {α : Type} [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
    x ∈ listToFinset l := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons a t ih =>
    rcases List.mem_cons.1 h with rfl | ht
    · exact Finset.mem_insert_self x _
    · exact Finset.mem_insert_of_mem (ih ht)

end PvsNP.Units.m3_resolution_complete

theorem PvsNP.Units.m3_resolution_complete :
    ∀ N : cnf, ¬ SAT N →
      ∀ S : Set clause, (∀ C ∈ N, C ∈ S) →
        (∀ C ∈ S, ∀ D ∈ S, ∀ v : var, (true, v) ∈ C → (false, v) ∈ D →
          C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v))) ∈ S) →
        [] ∈ S := by
  intro N hunsat S hNS hclosed
  let U : Finset var := PvsNP.Units.m3_resolution_complete.listToFinset (N.flatten.map Prod.snd)
  refine PvsNP.Units.m3_resolution_complete.complete_aux U N ?_ hunsat S hNS hclosed
  intro C hCN l hlC
  exact PvsNP.Units.m3_resolution_complete.mem_listToFinset
    (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨C, hCN, hlC⟩, rfl⟩)
