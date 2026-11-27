import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tc_closure_pair_lang_p

private def enc (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: (p.1 ++ p.2)

private def dec (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

private theorem takeWhile_replicate_true (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (true :: ·) ih

private theorem dropWhile_replicate_true (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem dec_enc (u v : List Bool) : dec (enc (u, v)) = (u, v) := by
  simp only [dec, enc, takeWhile_replicate_true, dropWhile_replicate_true,
    List.length_replicate, List.tail_cons, List.take_left, List.drop_left]

end PvsNP.Units.tc_closure_pair_lang_p

/-- P is closed under self-delimiting pairing (TM2). -/
theorem PvsNP.Units.tc_closure_pair_lang_p :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
      ({x : List Bool | ∃ u v : List Bool,
          x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) ∈ PvsNP.P := by
  intro L₁ L₂ hL₁ hL₂
  let enc := PvsNP.Units.tc_closure_pair_lang_p.enc
  let dec := PvsNP.Units.tc_closure_pair_lang_p.dec
  have henc : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString enc :=
    PvsNP.Units.m2_tm_self_delimiting_pair.1
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair dec :=
    PvsNP.Units.m2_tm_self_delimiting_pair.2
  have henc_dec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (enc ∘ dec) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      dec enc hdec henc
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => ((enc ∘ dec) x, x)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ henc_dec hid
  have hshape_fn : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      ((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
        (fun x : List Bool => ((enc ∘ dec) x, x))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      _ _ hpair PvsNP.Units.m2_eq_polytime
  let Lshape : Language Bool := {x : List Bool | enc (dec x) = x}
  let Lleft : Language Bool := {x : List Bool | (dec x).1 ∈ L₁}
  let Lright : Language Bool := {x : List Bool | (dec x).2 ∈ L₂}
  have hshape : Lshape ∈ PvsNP.P := by
    refine ⟨_, hshape_fn, fun x => ?_⟩
    show enc (dec x) = x ↔ decide (enc (dec x) = x) = true
    exact decide_eq_true_iff.symm
  have hfst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun p : List Bool × List Bool => p.1) ∘ dec) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      dec _ hdec PvsNP.Units.m2_pair_split_polytime.1
  have hsnd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun p : List Bool × List Bool => p.2) ∘ dec) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      dec _ hdec PvsNP.Units.m2_pair_split_polytime.2.1
  have hleft : Lleft ∈ PvsNP.P :=
    PvsNP.Units.m2_p_down_closed Lleft L₁ ⟨_, hfst, fun _ => Iff.rfl⟩ hL₁
  have hright : Lright ∈ PvsNP.P :=
    PvsNP.Units.m2_p_down_closed Lright L₂ ⟨_, hsnd, fun _ => Iff.rfl⟩ hL₂
  have hinter : Lshape ⊓ (Lleft ⊓ Lright) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_inter _ _ hshape (PvsNP.Units.m2_p_inter _ _ hleft hright)
  have heq :
      ({x : List Bool | ∃ u v : List Bool,
          x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) = Lshape ⊓ (Lleft ⊓ Lright) := by
    ext x
    constructor
    · rintro ⟨u, v, rfl, hu, hv⟩
      have hde : dec (enc (u, v)) = (u, v) :=
        PvsNP.Units.tc_closure_pair_lang_p.dec_enc u v
      refine ⟨?_, ?_, ?_⟩
      · show enc (dec (enc (u, v))) = enc (u, v)
        rw [hde]
      · show (dec (enc (u, v))).1 ∈ L₁
        rw [hde]
        exact hu
      · show (dec (enc (u, v))).2 ∈ L₂
        rw [hde]
        exact hv
    · rintro ⟨hsh, hl, hr⟩
      exact ⟨(dec x).1, (dec x).2, hsh.symm, hl, hr⟩
  rw [heq]
  exact hinter
