import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter

/-!
Exponential time is closed under self-delimiting pairing (TM2).

The pair language is the intersection of three languages: the strings that re-encode to
themselves after decoding (in P), the strings whose decoded first part is in `L₁`, and the
strings whose decoded second part is in `L₂` (both Karp-reduce to `L₁`, `L₂` by the
decoder of the settled unit `m2_tm_self_delimiting_pair`).
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_pair_lang

/-- The self-delimiting encoding of a pair. -/
def enc (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: (p.1 ++ p.2)

/-- The decoder of the self-delimiting encoding. -/
def dec (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dropWhile_rep (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dec_enc (p : List Bool × List Bool) : dec (enc p) = p := by
  obtain ⟨u, v⟩ := p
  simp [dec, enc]

theorem dec_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair dec :=
  PvsNP.Units.m2_tm_self_delimiting_pair.2

theorem enc_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString enc :=
  PvsNP.Units.m2_tm_self_delimiting_pair.1

theorem id_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x) :=
  ⟨Turing.idComputableInPolyTime _⟩

/-- Strings that are encodings of pairs. -/
def Shape : Language Bool := (Set.ofPred fun x => enc (dec x) = x : Set (List Bool))

/-- Strings whose decoded first part is in `L`. -/
def First (L : Language Bool) : Language Bool := (Set.ofPred fun x => (dec x).1 ∈ L : Set (List Bool))

/-- Strings whose decoded second part is in `L`. -/
def Second (L : Language Bool) : Language Bool := (Set.ofPred fun x => (dec x).2 ∈ L : Set (List Bool))

theorem shape_in_P : Shape ∈ PvsNP.P := by
  refine ⟨fun x => decide (enc (dec x) = x), ?_, ?_⟩
  · have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (enc ∘ dec) :=
      PvsNP.Units.m2_polytime_comp _ _ _ dec enc dec_poly enc_poly
    have h2 := PvsNP.Units.m2_pair_build_polytime (enc ∘ dec) (fun x => x) h1 id_poly
    have h3 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ h2 PvsNP.Units.m2_eq_polytime
    exact h3
  · intro x
    show enc (dec x) = x ↔ _
    simp

theorem first_karp (L : Language Bool) : PvsNP.KarpReducible (First L) L :=
  ⟨fun x => (dec x).1,
    PvsNP.Units.m2_polytime_comp _ _ _ dec (fun p : List Bool × List Bool => p.1) dec_poly
      PvsNP.Units.m2_pair_split_polytime.1,
    fun _ => Iff.rfl⟩

theorem second_karp (L : Language Bool) : PvsNP.KarpReducible (Second L) L :=
  ⟨fun x => (dec x).2,
    PvsNP.Units.m2_polytime_comp _ _ _ dec (fun p : List Bool × List Bool => p.2) dec_poly
      PvsNP.Units.m2_pair_split_polytime.2.1,
    fun _ => Iff.rfl⟩

theorem mem_iff (L₁ L₂ : Language Bool) (x : List Bool) :
    (∃ u v : List Bool, x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂) ↔
      x ∈ (Shape ⊓ First L₁) ⊓ Second L₂ := by
  show _ ↔ (enc (dec x) = x ∧ (dec x).1 ∈ L₁) ∧ (dec x).2 ∈ L₂
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    have h : dec (enc (u, v)) = (u, v) := dec_enc (u, v)
    simp only [enc] at h
    rw [h]
    exact ⟨⟨rfl, hu⟩, hv⟩
  · rintro ⟨⟨hs, h1⟩, h2⟩
    refine ⟨(dec x).1, (dec x).2, ?_, h1, h2⟩
    exact hs.symm

end PvsNP.Units.tc_exp_pair_lang

open PvsNP.Units.tc_exp_pair_lang in
theorem PvsNP.Units.tc_exp_pair_lang :
    ∀ L₁ L₂ : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ u v : List Bool, x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L₁ L₂ h₁ h₂
  have hS := PvsNP.Units.m2_p_subset_exp Shape shape_in_P
  have hA := PvsNP.Units.m2_exp_down_closed (First L₁) L₁ (first_karp L₁) h₁
  have hB := PvsNP.Units.m2_exp_down_closed (Second L₂) L₂ (second_karp L₂) h₂
  have hSA := PvsNP.Units.m2_exp_inter Shape (First L₁) hS hA
  obtain ⟨k, f, M, hf, ht⟩ := PvsNP.Units.m2_exp_inter _ (Second L₂) hSA hB
  exact ⟨k, f, M, fun x => (mem_iff L₁ L₂ x).trans (hf x), ht⟩
