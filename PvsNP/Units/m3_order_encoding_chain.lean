import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_order_encoding_chain

private lemma forward (a : assgn) :
    ∀ d : ℕ,
      (∀ i < d, i + 1 ∈ a → i ∈ a) →
      ∃ k : ℕ, k ≤ d + 1 ∧ ∀ i ≤ d, (i ∈ a ↔ i < k)
  | 0, _ => by
    by_cases h0 : (0 : ℕ) ∈ a
    · refine ⟨1, by omega, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using h0
    · refine ⟨0, by omega, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using h0
  | d + 1, hchain => by
    have ih := forward a d (fun i hi => hchain i (by omega))
    obtain ⟨k, hkd, hk⟩ := ih
    by_cases hd1 : d + 1 ∈ a
    · have hd : d ∈ a := hchain d (by omega) hd1
      have hdk : d < k := (hk d (by omega)).mp hd
      have hkeq : k = d + 1 := by omega
      refine ⟨d + 2, by omega, ?_⟩
      intro i hi
      by_cases hid : i = d + 1
      · subst hid
        exact ⟨fun _ => by omega, fun _ => hd1⟩
      · have hle : i ≤ d := by omega
        rw [hk i hle]
        omega
    · refine ⟨k, by omega, ?_⟩
      intro i hi
      by_cases hid : i = d + 1
      · subst hid
        exact ⟨fun h => absurd h hd1, fun h => by omega⟩
      · exact hk i (by omega)

end PvsNP.Units.m3_order_encoding_chain

theorem PvsNP.Units.m3_order_encoding_chain :
    ∀ (d : ℕ) (a : assgn),
      satisfiesCnf a ((List.range d).map (fun i => [(false, i + 1), (true, i)])) ↔
        ∃ k : ℕ, ∀ i ≤ d, (i ∈ a ↔ i < k) := by
  intro d a
  constructor
  · intro hsat
    have hcl : ∀ C ∈ (List.range d).map (fun i => [(false, i + 1), (true, i)]),
        evalClause a C = true := (evalCnf_clause_iff a _).mp hsat
    have hchain : ∀ i < d, i + 1 ∈ a → i ∈ a := by
      intro i hi hi1
      have hC := hcl [(false, i + 1), (true, i)]
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a _).mp hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [evalLiteral, evalVar, hi1] at hlit
      · simpa [evalLiteral, evalVar] using hlit
    obtain ⟨k, _, hk⟩ := PvsNP.Units.m3_order_encoding_chain.forward a d hchain
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
    rw [List.mem_range] at hi
    by_cases hlt : i + 1 < k
    · have hia : i ∈ a := (hk i (by omega)).mpr (Nat.lt_of_succ_lt hlt)
      exact (evalClause_literal_iff a _).mpr ⟨(true, i), by simp, by simp [evalLiteral, evalVar, hia]⟩
    · have hi1a : i + 1 ∉ a := fun h => hlt ((hk (i + 1) (by omega)).mp h)
      exact (evalClause_literal_iff a _).mpr ⟨(false, i + 1), by simp, by simp [evalLiteral, evalVar, hi1a]⟩
