import Mathlib
import PvsNP.Defs
import CookLevin

/-- The coordinatewise majority of three satisfying assignments of a 2-CNF satisfies it. -/
theorem PvsNP.Units.m3_twocnf_majority :
    ∀ (N : cnf) (a b c : assgn), (∀ C ∈ N, C.length ≤ 2) →
      satisfiesCnf a N → satisfiesCnf b N → satisfiesCnf c N →
        satisfiesCnf
          (a.filter (fun v => decide (v ∈ b ∨ v ∈ c)) ++ b.filter (fun v => decide (v ∈ c))) N := by
  intro N a b c hlen ha hb hc
  let m : assgn :=
    a.filter (fun v => decide (v ∈ b ∨ v ∈ c)) ++ b.filter (fun v => decide (v ∈ c))
  have hmem : ∀ v : var, v ∈ m ↔ (v ∈ a ∧ v ∈ b) ∨ (v ∈ a ∧ v ∈ c) ∨ (v ∈ b ∧ v ∈ c) := by
    intro v
    simp only [m, List.mem_append, List.mem_filter, decide_eq_true_eq]
    tauto
  have hmaj_ab : ∀ l : literal, evalLiteral a l = true → evalLiteral b l = true →
      evalLiteral m l = true := by
    rintro ⟨s, v⟩ hla hlb
    by_cases hva : v ∈ a <;> by_cases hvb : v ∈ b
    · have hvm : v ∈ m := (hmem v).2 (Or.inl ⟨hva, hvb⟩)
      cases s <;> simp [evalLiteral, evalVar, hva, hvm] at hla ⊢
    · cases s <;> simp [evalLiteral, evalVar, hva, hvb] at hla hlb
    · cases s <;> simp [evalLiteral, evalVar, hva, hvb] at hla hlb
    · have hvm : v ∉ m := fun h => by
        rcases (hmem v).1 h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
        · exact hva h1
        · exact hva h1
        · exact hvb h2
      cases s <;> simp [evalLiteral, evalVar, hva, hvm] at hla ⊢
  have hmaj_ac : ∀ l : literal, evalLiteral a l = true → evalLiteral c l = true →
      evalLiteral m l = true := by
    rintro ⟨s, v⟩ hla hlc
    by_cases hva : v ∈ a <;> by_cases hvc : v ∈ c
    · have hvm : v ∈ m := (hmem v).2 (Or.inr (Or.inl ⟨hva, hvc⟩))
      cases s <;> simp [evalLiteral, evalVar, hva, hvm] at hla ⊢
    · cases s <;> simp [evalLiteral, evalVar, hva, hvc] at hla hlc
    · cases s <;> simp [evalLiteral, evalVar, hva, hvc] at hla hlc
    · have hvm : v ∉ m := fun h => by
        rcases (hmem v).1 h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hva h1
        · exact hva h1
        · exact hvc h2
      cases s <;> simp [evalLiteral, evalVar, hva, hvm] at hla ⊢
  have hmaj_bc : ∀ l : literal, evalLiteral b l = true → evalLiteral c l = true →
      evalLiteral m l = true := by
    rintro ⟨s, v⟩ hlb hlc
    by_cases hvb : v ∈ b <;> by_cases hvc : v ∈ c
    · have hvm : v ∈ m := (hmem v).2 (Or.inr (Or.inr ⟨hvb, hvc⟩))
      cases s <;> simp [evalLiteral, evalVar, hvb, hvm] at hlb ⊢
    · cases s <;> simp [evalLiteral, evalVar, hvb, hvc] at hlb hlc
    · cases s <;> simp [evalLiteral, evalVar, hvb, hvc] at hlb hlc
    · have hvm : v ∉ m := fun h => by
        rcases (hmem v).1 h with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvb h1
        · exact hvc h2
        · exact hvb h1
      cases s <;> simp [evalLiteral, evalVar, hvb, hvm] at hlb ⊢
  simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha hb hc ⊢
  intro C hCN
  have hCa := ha C hCN
  have hCb := hb C hCN
  have hCc := hc C hCN
  have hClen := hlen C hCN
  match C with
  | [] => simp [evalClause] at hCa
  | [l₁] =>
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false] at hCa hCb ⊢
    exact hmaj_ab l₁ hCa hCb
  | [l₁, l₂] =>
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hCa hCb hCc ⊢
    rcases hCa with h1a | h2a
    · rcases hCb with h1b | h2b
      · exact Or.inl (hmaj_ab l₁ h1a h1b)
      · rcases hCc with h1c | h2c
        · exact Or.inl (hmaj_ac l₁ h1a h1c)
        · exact Or.inr (hmaj_bc l₂ h2b h2c)
    · rcases hCb with h1b | h2b
      · rcases hCc with h1c | h2c
        · exact Or.inl (hmaj_bc l₁ h1b h1c)
        · exact Or.inr (hmaj_ac l₂ h2a h2c)
      · exact Or.inr (hmaj_ab l₂ h2a h2b)
  | _ :: _ :: _ :: _ => simp at hClen
