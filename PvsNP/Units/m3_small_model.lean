import Mathlib
import PvsNP.Defs
import CookLevin

/-
A satisfiable CNF has a model with at most one true variable per clause.

Fix a model `b`. Going through the clauses, each clause has a literal true under `b`; if that
literal is positive, its variable is put in `a`. Then `a` holds at most one variable per clause and
only variables of `b`, so a negative literal true under `b` is true under `a`, and the chosen
positive literals are true under `a`.
-/

namespace PvsNP.Units.m3_small_model

/-- The literal `l` is true under every assignment that contains `a` and is contained in `b`
for the reason recorded here: positive with its variable in `a`, or negative with its variable
outside `b`. -/
def Good (a b : assgn) (l : literal) : Prop :=
  (l.1 = true ∧ l.2 ∈ a) ∨ (l.1 = false ∧ l.2 ∉ b)

theorem lit_cases (b : assgn) (l : literal) (h : evalLiteral b l = true) :
    (l.1 = true ∧ l.2 ∈ b) ∨ (l.1 = false ∧ l.2 ∉ b) := by
  obtain ⟨s, v⟩ := l
  change decide (decide (v ∈ b) = s) = true at h
  cases s <;> simp_all

theorem good_eval (a b : assgn) (hab : ∀ v ∈ a, v ∈ b) (l : literal) (h : Good a b l) :
    evalLiteral a l = true := by
  obtain ⟨s, v⟩ := l
  change decide (decide (v ∈ a) = s) = true
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    subst h1
    simp [h2]
  · simp only at h1 h2
    subst h1
    have : v ∉ a := fun hv => h2 (hab v hv)
    simp [this]

theorem build (b : assgn) : ∀ N : cnf, (∀ C ∈ N, evalClause b C = true) →
    ∃ a : assgn, (∀ v ∈ a, v ∈ b) ∧ (∀ C ∈ N, ∃ l ∈ C, Good a b l) ∧ a.length ≤ N.length := by
  intro N
  induction N with
  | nil =>
    intro _
    exact ⟨[], by simp, by simp, by simp⟩
  | cons C N ih =>
    intro h
    obtain ⟨a, hab, hgood, hlen⟩ := ih (fun D hD => h D (List.mem_cons_of_mem _ hD))
    have hC := h C List.mem_cons_self
    unfold evalClause at hC
    rw [List.any_eq_true] at hC
    obtain ⟨l, hl, hlb⟩ := hC
    rcases lit_cases b l hlb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨l.2 :: a, ?_, ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact h2
        · exact hab v hv
      · intro D hD
        rcases List.mem_cons.1 hD with rfl | hD
        · exact ⟨l, hl, Or.inl ⟨h1, List.mem_cons_self⟩⟩
        · obtain ⟨m, hm, hg⟩ := hgood D hD
          refine ⟨m, hm, ?_⟩
          rcases hg with ⟨g1, g2⟩ | hg
          · exact Or.inl ⟨g1, List.mem_cons_of_mem _ g2⟩
          · exact Or.inr hg
      · simp only [List.length_cons]
        omega
    · refine ⟨a, hab, ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.1 hD with rfl | hD
        · exact ⟨l, hl, Or.inr ⟨h1, h2⟩⟩
        · exact hgood D hD
      · simp only [List.length_cons]
        omega

end PvsNP.Units.m3_small_model

theorem PvsNP.Units.m3_small_model :
    ∀ N : cnf, SAT N → ∃ a : assgn, satisfiesCnf a N ∧ a.length ≤ N.length := by
  intro N hN
  obtain ⟨b, hb⟩ := hN
  unfold satisfiesCnf evalCnf at hb
  rw [List.all_eq_true] at hb
  obtain ⟨a, hab, hgood, hlen⟩ := PvsNP.Units.m3_small_model.build b N hb
  refine ⟨a, ?_, hlen⟩
  unfold satisfiesCnf evalCnf
  rw [List.all_eq_true]
  intro C hC
  obtain ⟨l, hl, hg⟩ := hgood C hC
  unfold evalClause
  rw [List.any_eq_true]
  exact ⟨l, hl, PvsNP.Units.m3_small_model.good_eval a b hab l hg⟩
