import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_unit_propagation :
    ∀ (N : cnf) (l : literal),
      SAT ([l] :: N) ↔
        SAT ((N.filter (fun C => decide (l ∉ C))).map
          (fun C => C.filter (fun m => decide (m ≠ (!l.1, l.2))))) := by
  intro N l
  rcases l with ⟨s, v⟩
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true, List.all_eq_true] at ha ⊢
    have hlv : evalVar a v = s := by
      have h1 := ha.1
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral,
        decide_eq_true_eq] at h1
      exact h1
    intro C' hC'
    obtain ⟨C, hCfilt, rfl⟩ := List.mem_map.mp hC'
    have hCN : C ∈ N := (List.mem_filter.mp hCfilt).1
    have hCa := ha.2 C hCN
    simp only [evalClause, List.any_eq_true] at hCa ⊢
    obtain ⟨m, hmC, hma⟩ := hCa
    refine ⟨m, List.mem_filter.mpr ⟨hmC, decide_eq_true_eq.mpr ?_⟩, hma⟩
    intro heq
    subst heq
    simp only [evalLiteral, hlv, decide_eq_true_eq] at hma
    cases s <;> simp at hma
  · rintro ⟨a, ha⟩
    let a' : assgn := if s then v :: a else a.filter (fun u => decide (u ≠ v))
    have hmem_v : v ∈ a' ↔ s = true := by
      cases s
      · simp [a']
      · simp [a']
    have hmem_ne : ∀ u, u ≠ v → (u ∈ a' ↔ u ∈ a) := by
      intro u hu
      cases s <;> simp [a', hu]
    refine ⟨a', ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true, List.all_eq_true] at ha ⊢
    refine ⟨?_, ?_⟩
    · simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral, evalVar,
        hmem_v]
      cases s <;> decide
    · intro C hC
      by_cases hlv : (s, v) ∈ C
      · simp only [evalClause, List.any_eq_true]
        refine ⟨(s, v), hlv, ?_⟩
        simp only [evalLiteral, evalVar, hmem_v]
        cases s <;> decide
      · have hC' : C.filter (fun m => decide (m ≠ (!s, v))) ∈
            (N.filter (fun C => decide ((s, v) ∉ C))).map
              (fun C => C.filter (fun m => decide (m ≠ (!s, v)))) :=
          List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, decide_eq_true_eq.mpr hlv⟩, rfl⟩
        have hsat := ha _ hC'
        simp only [evalClause, List.any_eq_true] at hsat ⊢
        obtain ⟨⟨sm, vm⟩, hmfilt, hma⟩ := hsat
        obtain ⟨hmC, hne⟩ := List.mem_filter.mp hmfilt
        have hne' : (sm, vm) ≠ (!s, v) := decide_eq_true_eq.mp hne
        have hvm : vm ≠ v := by
          intro hv
          subst hv
          cases s <;> cases sm
          · exact hlv hmC
          · exact hne' rfl
          · exact hne' rfl
          · exact hlv hmC
        refine ⟨(sm, vm), hmC, ?_⟩
        simp only [evalLiteral, evalVar] at hma ⊢
        by_cases h : vm ∈ a
        · have h' : vm ∈ a' := (hmem_ne vm hvm).mpr h
          simpa [h, h'] using hma
        · have h' : vm ∉ a' := fun hc => h ((hmem_ne vm hvm).mp hc)
          simpa [h, h'] using hma
