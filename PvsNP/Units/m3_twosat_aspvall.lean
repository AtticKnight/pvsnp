import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_twosat_aspvall

def ng (l : literal) : literal := (!l.1, l.2)

abbrev Rel (N : cnf) : literal → literal → Prop :=
  fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N

theorem ng_ng (l : literal) : ng (ng l) = l := by
  rcases l with ⟨s, v⟩
  simp [ng]

theorem lit (a : assgn) (l : literal) : evalLiteral a (ng l) = !evalLiteral a l := by
  rcases l with ⟨s, v⟩
  by_cases m : v ∈ a <;> cases s <;> simp [evalLiteral, evalVar, ng, m]

theorem R_contra {N : cnf} {l m : literal} (h : Rel N l m) : Rel N (ng m) (ng l) := by
  have e : ((!(ng m).1, (ng m).2) : literal) = m := ng_ng m
  rcases h with h | h
  · right
    show [ng l, (!(ng m).1, (ng m).2)] ∈ N
    rw [e]
    exact h
  · left
    show [(!(ng m).1, (ng m).2), ng l] ∈ N
    rw [e]
    exact h

theorem star_contra {N : cnf} {l m : literal} (h : Relation.ReflTransGen (Rel N) l m) :
    Relation.ReflTransGen (Rel N) (ng m) (ng l) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (R_contra hbc) ih

theorem sound {N : cnf} (a : assgn) (ha : ∀ C ∈ N, evalClause a C = true) {l m : literal}
    (h : Relation.ReflTransGen (Rel N) l m) : evalLiteral a l = true → evalLiteral a m = true := by
  induction h with
  | refl => exact id
  | @tail b c _ hbc ih =>
    intro hl
    have hb := ih hl
    have hnb : evalLiteral a (ng b) = false := by rw [lit, hb]; rfl
    rcases hbc with h | h
    · obtain ⟨x, hx, ht⟩ := (evalClause_literal_iff a _).mp (ha _ h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have ht' : evalLiteral a (ng b) = true := ht
        rw [hnb] at ht'
        cases ht'
      · exact ht
    · obtain ⟨x, hx, ht⟩ := (evalClause_literal_iff a _).mp (ha _ h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ht
      · have ht' : evalLiteral a (ng b) = true := ht
        rw [hnb] at ht'
        cases ht'

theorem closed_star {N : cnf} {T : Set literal} (hcl : ∀ l ∈ T, ∀ m, Rel N l m → m ∈ T)
    {l m : literal} (hl : l ∈ T) (h : Relation.ReflTransGen (Rel N) l m) : m ∈ T := by
  induction h with
  | refl => exact hl
  | tail _ hbc ih => exact hcl _ ih _ hbc

theorem ext (N : cnf)
    (H : ∀ v : var, ¬ (Relation.ReflTransGen (Rel N) (true, v) (false, v) ∧
      Relation.ReflTransGen (Rel N) (false, v) (true, v))) :
    ∀ vs : List var, ∃ T : Set literal, (∀ l ∈ T, ng l ∉ T) ∧
      (∀ l ∈ T, ∀ m, Rel N l m → m ∈ T) ∧ ∀ v ∈ vs, (true, v) ∈ T ∨ (false, v) ∈ T
  | [] => ⟨∅, fun _ hl => hl.elim, fun _ hl => hl.elim, fun v hv => by simp at hv⟩
  | v :: vs => by
    obtain ⟨T, hc, hcl, htot⟩ := ext N H vs
    by_cases hv : (true, v) ∈ T ∨ (false, v) ∈ T
    · refine ⟨T, hc, hcl, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hv
      · exact htot u hu'
    · have hv1 : (true, v) ∉ T := fun h => hv (Or.inl h)
      have hv2 : (false, v) ∉ T := fun h => hv (Or.inr h)
      obtain ⟨x, hxv, hxn⟩ : ∃ x : literal, (x = (true, v) ∨ x = (false, v)) ∧
          ¬ Relation.ReflTransGen (Rel N) x (ng x) := by
        by_cases h1 : Relation.ReflTransGen (Rel N) (true, v) (false, v)
        · exact ⟨(false, v), Or.inr rfl, fun h2 => H v ⟨h1, h2⟩⟩
        · exact ⟨(true, v), Or.inl rfl, h1⟩
      have hngx : ng x ∉ T := by
        rcases hxv with rfl | rfl
        · exact hv2
        · exact hv1
      refine ⟨{m | m ∈ T ∨ Relation.ReflTransGen (Rel N) x m}, ?_, ?_, ?_⟩
      · rintro l (hl | hl) (hn | hn)
        · exact hc l hl hn
        · have h := star_contra hn
          rw [ng_ng] at h
          exact hngx (closed_star hcl hl h)
        · have h := star_contra hl
          exact hngx (closed_star hcl hn h)
        · have h := star_contra hn
          rw [ng_ng] at h
          exact hxn (hl.trans h)
      · rintro l (hl | hl) m hm
        · exact Or.inl (hcl l hl m hm)
        · exact Or.inr (Relation.ReflTransGen.tail hl hm)
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · rcases hxv with rfl | rfl
          · exact Or.inl (Or.inr Relation.ReflTransGen.refl)
          · exact Or.inr (Or.inr Relation.ReflTransGen.refl)
        · rcases htot u hu' with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)

end PvsNP.Units.m3_twosat_aspvall

open PvsNP.Units.m3_twosat_aspvall in
theorem PvsNP.Units.m3_twosat_aspvall : ∀ N : cnf, (∀ C ∈ N, C.length = 2) →
  (SAT N ↔ ∀ v : var,
    ¬ (Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (true, v) (false, v) ∧
      Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (false, v) (true, v))) := by
  intro N h2
  constructor
  · rintro ⟨a, ha⟩ v ⟨h1, h3⟩
    have ha' := (evalCnf_clause_iff a N).mp ha
    have s1 := sound (N := N) a ha' h1
    have s2 := sound (N := N) a ha' h3
    by_cases m : v ∈ a
    · have t : evalLiteral a (true, v) = true := by simp [evalLiteral, evalVar, m]
      have f := s1 t
      simp [evalLiteral, evalVar, m] at f
    · have t : evalLiteral a (false, v) = true := by simp [evalLiteral, evalVar, m]
      have f := s2 t
      simp [evalLiteral, evalVar, m] at f
  · intro H
    classical
    obtain ⟨T, hc, hcl, htot⟩ := ext N H (N.flatMap (fun C => C.map (fun l => l.2)))
    have hvar : ∀ C ∈ N, ∀ l ∈ C, l.2 ∈ N.flatMap (fun C => C.map (fun l => l.2)) :=
      fun C hC l hl => List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
    refine ⟨(N.flatMap (fun C => C.map (fun l => l.2))).filter (fun v => decide ((true, v) ∈ T)), ?_⟩
    have key : ∀ l : literal, l.2 ∈ N.flatMap (fun C => C.map (fun l => l.2)) → l ∈ T →
        evalLiteral ((N.flatMap (fun C => C.map (fun l => l.2))).filter
          (fun v => decide ((true, v) ∈ T))) l = true := by
      rintro ⟨s, v⟩ hv hl
      cases s
      · have hn : (true, v) ∉ T := hc (false, v) hl
        have hm : v ∉ (N.flatMap (fun C => C.map (fun l => l.2))).filter
            (fun v => decide ((true, v) ∈ T)) := by
          intro c
          exact hn (of_decide_eq_true (List.mem_filter.mp c).2)
        simp [evalLiteral, evalVar, hm]
      · have hm : v ∈ (N.flatMap (fun C => C.map (fun l => l.2))).filter
            (fun v => decide ((true, v) ∈ T)) :=
          List.mem_filter.mpr ⟨hv, decide_eq_true hl⟩
        simp [evalLiteral, evalVar, hm]
    have total : ∀ l : literal, l.2 ∈ N.flatMap (fun C => C.map (fun l => l.2)) → l ∈ T ∨ ng l ∈ T := by
      rintro ⟨s, v⟩ hv
      rcases htot v hv with h | h
      · cases s
        · exact Or.inr h
        · exact Or.inl h
      · cases s
        · exact Or.inl h
        · exact Or.inr h
    apply (evalCnf_clause_iff _ N).mpr
    intro C hC
    have hlen := h2 C hC
    match C, hC, hlen with
    | [l1, l2], hC', _ =>
      have hv1 := hvar _ hC' l1 (by simp)
      have hv2 := hvar _ hC' l2 (by simp)
      rcases total l1 hv1 with h | h
      · exact (evalClause_literal_iff _ _).mpr ⟨l1, by simp, key l1 hv1 h⟩
      · have hr : Rel N (ng l1) l2 := by
          left
          show [(!(ng l1).1, (ng l1).2), l2] ∈ N
          have e : ((!(ng l1).1, (ng l1).2) : literal) = l1 := ng_ng l1
          rw [e]
          exact hC'
        have h2T := hcl _ h _ hr
        exact (evalClause_literal_iff _ _).mpr ⟨l2, by simp, key l2 hv2 h2T⟩
