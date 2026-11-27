import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_models_count_disjoint_product

theorem evalLiteral_congr (a b : assgn) (l : literal) (h : l.2 ∈ a ↔ l.2 ∈ b) :
    evalLiteral a l = evalLiteral b l := by
  rcases l with ⟨s, v⟩
  dsimp only at h
  cases s <;> simp [evalLiteral, evalVar, h]

theorem evalClause_congr (a b : assgn) (C : clause) (h : ∀ l ∈ C, l.2 ∈ a ↔ l.2 ∈ b) :
    evalClause a C = evalClause b C := by
  induction C with
  | nil => rfl
  | cons l ls ih =>
    simp only [evalClause, List.any_cons]
    congr 1
    · exact evalLiteral_congr a b l (h l List.mem_cons_self)
    · exact ih (fun m hm => h m (List.mem_cons_of_mem l hm))

theorem evalCnf_congr (a b : assgn) (N : cnf) (h : ∀ C ∈ N, ∀ l ∈ C, l.2 ∈ a ↔ l.2 ∈ b) :
    evalCnf a N = evalCnf b N := by
  induction N with
  | nil => rfl
  | cons C Cs ih =>
    simp only [evalCnf, List.all_cons]
    congr 1
    · exact evalClause_congr a b C (h C List.mem_cons_self)
    · exact ih (fun D hD => h D (List.mem_cons_of_mem C hD))

theorem evalClause_shift (a : assgn) (C : clause) (m : ℕ) (b : assgn)
    (h : ∀ l ∈ C, l.2 + m ∈ a ↔ l.2 ∈ b) :
    evalClause a (C.map (fun l => (l.1, l.2 + m))) = evalClause b C := by
  induction C with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons, evalClause, List.any_cons]
    congr 1
    · rcases l with ⟨s, v⟩
      have hv := h (s, v) List.mem_cons_self
      dsimp only at hv
      cases s <;> simp [evalLiteral, evalVar, hv]
    · exact ih (fun u hu => h u (List.mem_cons_of_mem l hu))

theorem evalCnf_shift (a : assgn) (N : cnf) (m : ℕ) (b : assgn)
    (h : ∀ C ∈ N, ∀ l ∈ C, l.2 + m ∈ a ↔ l.2 ∈ b) :
    evalCnf a (N.map (fun C => C.map (fun l => (l.1, l.2 + m)))) = evalCnf b N := by
  induction N with
  | nil => rfl
  | cons C Cs ih =>
    simp only [List.map_cons, evalCnf, List.all_cons]
    congr 1
    · exact evalClause_shift a C m b (h C List.mem_cons_self)
    · exact ih (fun D hD => h D (List.mem_cons_of_mem C hD))

theorem sublist_append_split {α : Type} :
    ∀ {a l₁ l₂ : List α}, List.Sublist a (l₁ ++ l₂) →
      ∃ a₁ a₂, a = a₁ ++ a₂ ∧ List.Sublist a₁ l₁ ∧ List.Sublist a₂ l₂
  | a, [], l₂, h => ⟨[], a, rfl, List.Sublist.slnil, h⟩
  | a, x :: xs, l₂, h => by
    cases h with
    | cons _ h' =>
      obtain ⟨a₁, a₂, rfl, h1, h2⟩ := sublist_append_split h'
      exact ⟨a₁, a₂, rfl, List.Sublist.cons x h1, h2⟩
    | cons_cons _ h' =>
      obtain ⟨a₁, a₂, rfl, h1, h2⟩ := sublist_append_split h'
      exact ⟨x :: a₁, a₂, rfl, List.Sublist.cons_cons x h1, h2⟩

theorem sublist_map_split {α β : Type} (f : α → β) :
    ∀ {b : List β} {l : List α}, List.Sublist b (l.map f) →
      ∃ a, b = a.map f ∧ List.Sublist a l
  | _, [], h => by
    simp only [List.map_nil, List.sublist_nil] at h
    exact ⟨[], by rw [h]; rfl, List.Sublist.slnil⟩
  | b, x :: xs, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons _ h' =>
      obtain ⟨a, rfl, ha⟩ := sublist_map_split f h'
      exact ⟨a, rfl, List.Sublist.cons x ha⟩
    | cons_cons _ h' =>
      obtain ⟨a, rfl, ha⟩ := sublist_map_split f h'
      exact ⟨x :: a, rfl, List.Sublist.cons_cons x ha⟩

theorem range_add_eq (m k : ℕ) :
    List.range (m + k) = List.range m ++ (List.range k).map (· + m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append,
      List.map_singleton, List.append_assoc]
    simp only [Nat.add_comm k m]

theorem main :
    ∀ (m k : ℕ) (N₁ N₂ : cnf), (∀ C ∈ N₁, ∀ l ∈ C, l.2 < m) → (∀ C ∈ N₂, ∀ l ∈ C, l.2 < k) →
      ((List.range (m + k)).sublists.filter
          (fun a => evalCnf a (N₁ ++ N₂.map (fun C => C.map (fun l => (l.1, l.2 + m)))))).length =
        ((List.range m).sublists.filter (fun a => evalCnf a N₁)).length *
          ((List.range k).sublists.filter (fun a => evalCnf a N₂)).length := by
  intro m k N₁ N₂ hN₁ _
  set N₂' : cnf := N₂.map (fun C => C.map (fun l => (l.1, l.2 + m)))
  set S := (List.range (m + k)).sublists.filter (fun a => evalCnf a (N₁ ++ N₂'))
  set S₁ := (List.range m).sublists.filter (fun a => evalCnf a N₁)
  set S₂ := (List.range k).sublists.filter (fun a => evalCnf a N₂)
  have hS_nd : S.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have hS₁_nd : S₁.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have hS₂_nd : S₂.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have heval_app : ∀ (a₁ a₂ : assgn), List.Sublist a₁ (List.range m) →
      evalCnf (a₁ ++ a₂.map (· + m)) (N₁ ++ N₂') = (evalCnf a₁ N₁ && evalCnf a₂ N₂) := by
    intro a₁ a₂ ha₁
    have h1 : evalCnf (a₁ ++ a₂.map (· + m)) N₁ = evalCnf a₁ N₁ := by
      refine evalCnf_congr _ _ N₁ (fun C hC l hl => ?_)
      have hlm : l.2 < m := hN₁ C hC l hl
      simp only [List.mem_append, List.mem_map, or_iff_left_iff_imp]
      rintro ⟨v, _, hv⟩
      have hle : m ≤ v + m := Nat.le_add_left m v
      rw [hv] at hle
      exact absurd hlm (Nat.not_lt.2 hle)
    have h2 : evalCnf (a₁ ++ a₂.map (· + m)) N₂' = evalCnf a₂ N₂ := by
      refine evalCnf_shift _ N₂ m _ (fun C _ l _ => ?_)
      simp only [List.mem_append, List.mem_map]
      constructor
      · rintro (hmem | ⟨v, hv, heq⟩)
        · exfalso
          have hlt : l.2 + m < m := List.mem_range.1 (ha₁.subset hmem)
          exact Nat.not_lt.2 (Nat.le_add_left m l.2) hlt
        · have : v = l.2 := Nat.add_right_cancel heq
          rwa [← this]
      · intro hv
        exact Or.inr ⟨l.2, hv, rfl⟩
    change (N₁ ++ N₂').all (evalClause (a₁ ++ a₂.map (· + m))) = (evalCnf a₁ N₁ && evalCnf a₂ N₂)
    rw [List.all_append]
    exact congrArg₂ (· && ·) h1 h2
  have hbij : (S₁.toFinset ×ˢ S₂.toFinset).card = S.toFinset.card := by
    refine Finset.card_bij (fun p _ => p.1 ++ p.2.map (· + m)) ?_ ?_ ?_
    · rintro ⟨a₁, a₂⟩ hp
      simp only [Finset.mem_product, List.mem_toFinset, S₁, S₂, List.mem_filter,
        List.mem_sublists] at hp
      obtain ⟨⟨ha₁, he₁⟩, ⟨ha₂, he₂⟩⟩ := hp
      simp only [List.mem_toFinset, S, List.mem_filter, List.mem_sublists]
      refine ⟨?_, ?_⟩
      · rw [range_add_eq]
        exact ha₁.append (ha₂.map (· + m))
      · rw [heval_app a₁ a₂ ha₁, he₁, he₂]; rfl
    · rintro ⟨a₁, a₂⟩ hp ⟨b₁, b₂⟩ hq heq
      simp only [Finset.mem_product, List.mem_toFinset, S₁, S₂, List.mem_filter,
        List.mem_sublists] at hp hq
      have hlt_a₁ : ∀ x ∈ a₁, x < m := fun x hx => List.mem_range.1 (hp.1.1.subset hx)
      have hlt_b₁ : ∀ x ∈ b₁, x < m := fun x hx => List.mem_range.1 (hq.1.1.subset hx)
      have hfilt1 := congrArg (List.filter (fun x => decide (x < m))) heq
      simp only [List.filter_append] at hfilt1
      have ha1f : a₁.filter (fun x => decide (x < m)) = a₁ :=
        List.filter_eq_self.2 (fun x hx => decide_eq_true (hlt_a₁ x hx))
      have hb1f : b₁.filter (fun x => decide (x < m)) = b₁ :=
        List.filter_eq_self.2 (fun x hx => decide_eq_true (hlt_b₁ x hx))
      have ha2f : (a₂.map (· + m)).filter (fun x => decide (x < m)) = [] :=
        List.filter_eq_nil_iff.2 (fun x hx => by
          obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx; simp)
      have hb2f : (b₂.map (· + m)).filter (fun x => decide (x < m)) = [] :=
        List.filter_eq_nil_iff.2 (fun x hx => by
          obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx; simp)
      rw [ha1f, ha2f, hb1f, hb2f, List.append_nil, List.append_nil] at hfilt1
      subst hfilt1
      have hmap : a₂.map (· + m) = b₂.map (· + m) := List.append_cancel_left heq
      have h2eq : a₂ = b₂ := List.map_injective_iff.2 (fun _ _ h => Nat.add_right_cancel h) hmap
      subst h2eq
      rfl
    · intro a ha
      simp only [List.mem_toFinset, S, List.mem_filter, List.mem_sublists] at ha
      obtain ⟨hasub, haev⟩ := ha
      rw [range_add_eq] at hasub
      obtain ⟨a₁, a₂', rfl, ha₁, ha₂'⟩ := sublist_append_split hasub
      obtain ⟨a₂, rfl, ha₂⟩ := sublist_map_split (· + m) ha₂'
      rw [heval_app a₁ a₂ ha₁, Bool.and_eq_true] at haev
      refine ⟨(a₁, a₂), ?_, rfl⟩
      simp only [Finset.mem_product, List.mem_toFinset, S₁, S₂, List.mem_filter,
        List.mem_sublists]
      exact ⟨⟨ha₁, haev.1⟩, ⟨ha₂, haev.2⟩⟩
  calc S.length
      = S.toFinset.card := (List.toFinset_card_of_nodup hS_nd).symm
    _ = (S₁.toFinset ×ˢ S₂.toFinset).card := hbij.symm
    _ = S₁.toFinset.card * S₂.toFinset.card := Finset.card_product _ _
    _ = S₁.length * S₂.length := by
        rw [List.toFinset_card_of_nodup hS₁_nd, List.toFinset_card_of_nodup hS₂_nd]

end PvsNP.Units.m3_models_count_disjoint_product

theorem PvsNP.Units.m3_models_count_disjoint_product :
    ∀ (m k : ℕ) (N₁ N₂ : cnf), (∀ C ∈ N₁, ∀ l ∈ C, l.2 < m) → (∀ C ∈ N₂, ∀ l ∈ C, l.2 < k) →
      ((List.range (m + k)).sublists.filter
          (fun a => evalCnf a (N₁ ++ N₂.map (fun C => C.map (fun l => (l.1, l.2 + m)))))).length =
        ((List.range m).sublists.filter (fun a => evalCnf a N₁)).length *
          ((List.range k).sublists.filter (fun a => evalCnf a N₂)).length :=
  PvsNP.Units.m3_models_count_disjoint_product.main
