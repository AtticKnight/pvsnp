import Mathlib
import PvsNP.Defs
import CookLevin

/-
Predicted statements for the next desk units, in the campaign's phrasing: the complement form of a
Karp reduction (upstream lean/PEqualNP/Library/L040.lean), the polynomial form of P (L003), and CNF
facts in the vendored Cook-Levin model next to L022-L026 (vendor/CookLevin/CookLevin/SAT/SAT.lean:
`cnf`, `clause`, `literal`, `assgn`, `evalVar`, `evalLiteral`, `evalClause`, `evalCnf`,
`satisfiesCnf`, `SAT`; `SATStr.cnfOf` and `SATToSATStr.satToStr` of the same vendored library, used
as they stand). Upstream: github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs)
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0,
http://www.apache.org/licenses/LICENSE-2.0). MODIFIED: the statements are rewritten over the
campaign's and the vendored definitions and the proofs are new. No upstream or campaign file is copied.
-/

set_option autoImplicit false

namespace PvsNP.Units.m3_negative_clause_sat

/-! ## Karp reductions and P -/

/-- A Karp reduction from `L₁` to `L₂` is also one from the complement of `L₁` to the complement of
`L₂` (upstream L040). -/
theorem karp_compl : ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ →
    PvsNP.KarpReducible L₁ᶜ L₂ᶜ := by
  rintro L₁ L₂ ⟨f, hf, h⟩
  exact ⟨f, hf, fun x => not_congr (h x)⟩

/-- P is decided within a polynomial number of steps, the polynomial named (upstream L003). -/
theorem p_poly_form : ∀ L : Language Bool, L ∈ PvsNP.P ↔
    ∃ (p : Polynomial ℕ) (f : List Bool → Bool)
      (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time.eval n ≤ p.eval n := by
  intro L
  constructor
  · intro hL
    obtain ⟨f, ⟨M⟩, hf⟩ := hL
    exact ⟨M.time, f, M, hf, fun n => le_rfl⟩
  · rintro ⟨p, f, M, hf, -⟩
    exact ⟨f, ⟨M⟩, hf⟩

/-! ## CNF facts (vendored model) -/

/-- A formula in which every clause has a negative literal is satisfiable: the all-false
assignment satisfies it (the dual of upstream L023). -/
theorem neg_lit_sat : ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (false, v) ∈ C) → SAT N := by
  intro N h
  refine ⟨[], ?_⟩
  show evalCnf _ N = true
  rw [evalCnf_clause_iff]
  intro C hC
  obtain ⟨v, hv⟩ := h C hC
  rw [evalClause_literal_iff]
  exact ⟨(false, v), hv, by simp [evalLiteral, evalVar]⟩

/-- The empty formula is satisfiable. -/
theorem sat_nil : SAT ([] : cnf) := ⟨[], by simp [satisfiesCnf, evalCnf]⟩

/-- Fewer clauses: a formula whose clauses all occur in a satisfiable formula is satisfiable. -/
theorem sat_mono : ∀ N M : cnf, (∀ C ∈ M, C ∈ N) → SAT N → SAT M := by
  rintro N M hsub ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have ha' : evalCnf a N = true := ha
  show evalCnf a M = true
  rw [evalCnf_clause_iff] at ha' ⊢
  exact fun C hC => ha' C (hsub C hC)

theorem sat_subset : ∀ N M : cnf, M ⊆ N → SAT N → SAT M :=
  fun N M h => sat_mono N M (fun C hC => h hC)

theorem sat_append_left : ∀ N M : cnf, SAT (N ++ M) → SAT N :=
  fun N M => sat_mono (N ++ M) N (fun C hC => List.mem_append_left M hC)

theorem sat_append_right : ∀ N M : cnf, SAT (N ++ M) → SAT M :=
  fun N M => sat_mono (N ++ M) M (fun C hC => List.mem_append_right N hC)

theorem sat_cons : ∀ (C : clause) (N : cnf), SAT (C :: N) → SAT N :=
  fun C N => sat_mono (C :: N) N (fun D hD => List.mem_cons_of_mem C hD)

/-- Reordering the clauses keeps satisfiability. -/
theorem sat_perm : ∀ N M : cnf, N.Perm M → (SAT N ↔ SAT M) := fun N M h =>
  ⟨sat_mono N M (fun C hC => h.symm.subset hC), sat_mono M N (fun C hC => h.subset hC)⟩

/-- A tautological clause (one holding a variable and its negation) can be dropped. -/
theorem taut_clause : ∀ (N : cnf) (C : clause) (v : var), (true, v) ∈ C → (false, v) ∈ C →
    (SAT (C :: N) ↔ SAT N) := by
  intro N C v ht hf
  refine ⟨sat_cons C N, ?_⟩
  rintro ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have ha' : evalCnf a N = true := ha
  show evalCnf a (C :: N) = true
  rw [evalCnf_clause_iff] at ha' ⊢
  intro D hD
  rcases List.mem_cons.mp hD with rfl | hD
  · rw [evalClause_literal_iff]
    by_cases hv : evalVar a v = true
    · exact ⟨(true, v), ht, by simp [evalLiteral, hv]⟩
    · exact ⟨(false, v), hf, by simp [evalLiteral, hv]⟩
  · exact ha' D hD

/-- A clause evaluates to true on a concatenation exactly when it does on one of the parts. -/
theorem evalClause_append : ∀ (a : assgn) (C D : clause),
    evalClause a (C ++ D) = true ↔ evalClause a C = true ∨ evalClause a D = true := by
  intro a C D
  simp [evalClause, List.any_append, Bool.or_eq_true]

/-- A formula evaluates to true on a concatenation exactly when it does on both parts. -/
theorem evalCnf_append : ∀ (a : assgn) (N M : cnf),
    evalCnf a (N ++ M) = true ↔ evalCnf a N = true ∧ evalCnf a M = true := by
  intro a N M
  simp [evalCnf, List.all_append, Bool.and_eq_true]



theorem h_karp_compl :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ → PvsNP.KarpReducible L₁ᶜ L₂ᶜ :=
  PvsNP.Units.m3_negative_clause_sat.karp_compl


theorem h_p_poly_form :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔ ∃ (p : Polynomial ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time.eval n ≤ p.eval n :=
  PvsNP.Units.m3_negative_clause_sat.p_poly_form


theorem h_neg_lit_sat :
    ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (false, v) ∈ C) → SAT N :=
  PvsNP.Units.m3_negative_clause_sat.neg_lit_sat


theorem h_sat_nil : SAT ([] : cnf) :=
  PvsNP.Units.m3_negative_clause_sat.sat_nil


theorem h_sat_mono :
    ∀ N M : cnf, (∀ C ∈ M, C ∈ N) → SAT N → SAT M :=
  PvsNP.Units.m3_negative_clause_sat.sat_mono


theorem h_sat_subset : ∀ N M : cnf, M ⊆ N → SAT N → SAT M :=
  PvsNP.Units.m3_negative_clause_sat.sat_subset


theorem h_sat_append_left : ∀ N M : cnf, SAT (N ++ M) → SAT N :=
  PvsNP.Units.m3_negative_clause_sat.sat_append_left


theorem h_sat_cons : ∀ (C : clause) (N : cnf), SAT (C :: N) → SAT N :=
  PvsNP.Units.m3_negative_clause_sat.sat_cons


theorem h_sat_perm : ∀ N M : cnf, N.Perm M → (SAT N ↔ SAT M) :=
  PvsNP.Units.m3_negative_clause_sat.sat_perm


theorem h_taut_clause :
    ∀ (N : cnf) (C : clause) (v : var), (true, v) ∈ C → (false, v) ∈ C → (SAT (C :: N) ↔ SAT N) :=
  PvsNP.Units.m3_negative_clause_sat.taut_clause


theorem h_evalClause_append :
    ∀ (a : assgn) (C D : clause), evalClause a (C ++ D) = true ↔ evalClause a C = true ∨ evalClause a D = true :=
  PvsNP.Units.m3_negative_clause_sat.evalClause_append


end PvsNP.Units.m3_negative_clause_sat

theorem PvsNP.Units.m3_negative_clause_sat :
    ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (false, v) ∈ C) → SAT N :=
  PvsNP.Units.m3_negative_clause_sat.h_neg_lit_sat
