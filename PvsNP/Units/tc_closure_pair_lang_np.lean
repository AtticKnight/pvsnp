import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_pair_lang_np

/-- The self-delimiting pair encoding. -/
def enc (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: (p.1 ++ p.2)

/-- Its decoder. -/
def dec (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep (n : ℕ) (w : List Bool) :
    (List.replicate n true ++ false :: w).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dropWhile_rep (n : ℕ) (w : List Bool) :
    (List.replicate n true ++ false :: w).dropWhile id = false :: w := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dec_enc (p : List Bool × List Bool) : dec (enc p) = p := by
  obtain ⟨u, v⟩ := p
  simp [dec, enc]

theorem enc_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString enc :=
  PvsNP.Units.m2_tm_self_delimiting_pair.1

theorem dec_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair dec :=
  PvsNP.Units.m2_tm_self_delimiting_pair.2

theorem id_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x) :=
  ⟨Turing.idComputableInPolyTime _⟩

theorem shape_p :
    ({x : List Bool | enc (dec x) = x} : Language Bool) ∈ PvsNP.P := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (enc ∘ dec) :=
    PvsNP.Units.m2_polytime_comp _ _ _ dec enc dec_poly enc_poly
  have h2 := PvsNP.Units.m2_pair_build_polytime (enc ∘ dec) (fun x => x) h1 id_poly
  have h3 := PvsNP.Units.m2_polytime_comp _ _ _ _
    (fun p : List Bool × List Bool => decide (p.1 = p.2)) h2 PvsNP.Units.m2_eq_polytime
  refine ⟨_, h3, fun x => ?_⟩
  simp [Function.comp]
  rfl

theorem part_np (L : Language Bool) (g : List Bool × List Bool → List Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g) (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | g (dec x) ∈ L} : Language Bool) ∈ PvsNP.NP := by
  apply PvsNP.Units.m2_np_down_closed _ L _ hL
  exact ⟨g ∘ dec, PvsNP.Units.m2_polytime_comp _ _ _ dec g dec_poly hg, fun x => Iff.rfl⟩

end PvsNP.Units.tc_closure_pair_lang_np

open PvsNP.Units.tc_closure_pair_lang_np in
theorem PvsNP.Units.tc_closure_pair_lang_np :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
      ({x : List Bool | ∃ u v : List Bool, x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.NP := by
  intro L₁ L₂ h₁ h₂
  have hS := PvsNP.Units.m2_p_subset_np shape_p
  have hA := part_np L₁ (fun p => p.1) PvsNP.Units.m2_pair_split_polytime.1 h₁
  have hB := part_np L₂ (fun p => p.2) PvsNP.Units.m2_pair_split_polytime.2.1 h₂
  have h := PvsNP.Units.m2_np_inter _ _ (PvsNP.Units.m2_np_inter _ _ hS hA) hB
  refine (congrArg (· ∈ PvsNP.NP) ?_).mpr h
  ext x
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    have e : dec (enc (u, v)) = (u, v) := dec_enc (u, v)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show enc (dec (enc (u, v))) = enc (u, v)
      rw [e]
    · show (dec (enc (u, v))).1 ∈ L₁
      rw [e]; exact hu
    · show (dec (enc (u, v))).2 ∈ L₂
      rw [e]; exact hv
  · rintro ⟨⟨hx, hu⟩, hv⟩
    exact ⟨(dec x).1, (dec x).2, hx.symm, hu, hv⟩
