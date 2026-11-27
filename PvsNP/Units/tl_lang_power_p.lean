import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_eq_polytime

/-
Built on the settled units PvsNP.Units.fr_ladner (`pairB`, `unpairB`, `unpairB_pairB`, `un`,
`sel`, `cpt_pairB2`, `cpt_unpairB1`, `cpt_unpairB2`, `cpt_unpairB1_1`, `cpt_unpairB2_1`,
`cpt_app2`, `cpt_cons1`, `cpt_const`, `cpt_id`, `cpt_pair`, `cpt_sel`, `cpt_bitFlag`,
`fst_polyTime`, `Iter.iter_polyTime`), m2_transducer_polytime, m2_polytime_comp, and
m2_eq_polytime of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.tl_lang_power_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem map_true_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun u : List Bool => u.map (fun _ => true)) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some true))
    (fun _ => none)
    (fun _ u => u.map (fun _ => true))
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

private theorem unpairB_map_true (u x : List Bool) :
    unpairB (u.map (fun _ => true) ++ false :: x) = (x.take u.length, x.drop u.length) := by
  have h1 : (u.map (fun _ => true) ++ false :: x).takeWhile id = u.map (fun _ => true) := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  have h2 : (u.map (fun _ => true) ++ false :: x).dropWhile id = false :: x := by
    induction u with
    | nil => simp
    | cons _ t ih => simp
  simp [unpairB]

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [fstRun, ih]

private theorem cpt_neU :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons _ l =>
        simp [fstRun, neU_true, PvsNP.encodeString, PvsNP.encodeAnswer,
          Computability.encodingList, Computability.encodeBool])

private theorem replicate_flatten_length (k : ℕ) (y : List Bool) :
    (List.replicate k y).flatten.length = k * y.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ, ih, Nat.succ_mul]
    omega

private theorem replicate_flatten_getElem (k : ℕ) (y : List Bool) (hy : 0 < y.length)
    (i : ℕ) (hi : i < (List.replicate k y).flatten.length) :
    (List.replicate k y).flatten[i]'hi = y[i % y.length]'(Nat.mod_lt i hy) := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    by_cases hlt : i < y.length
    · rw [List.getElem_append_left hlt]
      congr 1
      exact (Nat.mod_eq_of_lt hlt).symm
    · have hge : y.length ≤ i := by omega
      rw [List.getElem_append_right hge]
      have hi' : i - y.length < (List.replicate k y).flatten.length := by
        simp only [List.replicate_succ, List.flatten_cons, List.length_append] at hi
        omega
      rw [ih (i - y.length) hi']
      congr 1
      have hmod : (i - y.length) % y.length = i % y.length := by
        have h1 : i = (i - y.length) + y.length := by omega
        conv_rhs => rw [h1, Nat.add_mod_right]
      exact hmod

private theorem rot_iff_periodic (x : List Bool) {p : ℕ} (hp : p ≤ x.length) :
    x.drop p ++ x.take p = x ↔
      ∀ (i : ℕ) (hi : i < x.length),
        x[(i + p) % x.length]'(Nat.mod_lt _ (by omega)) = x[i]'hi := by
  constructor
  · intro hrot i hi
    have hlen : (x.drop p ++ x.take p).length = x.length := by
      simp [List.length_drop, List.length_take]; omega
    have hget := congrArg (fun l : List Bool => l[i]?) hrot
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : i < (x.drop p ++ x.take p).length)] at hget
    have heq := Option.some.inj hget
    by_cases h1 : i < x.length - p
    · have hlt_drop : i < (x.drop p).length := by simp [List.length_drop]; omega
      rw [List.getElem_append_left hlt_drop, List.getElem_drop] at heq
      have hmod : (i + p) % x.length = p + i := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simpa [hmod] using heq
    · have hge_drop : (x.drop p).length ≤ i := by simp [List.length_drop]; omega
      rw [List.getElem_append_right hge_drop, List.getElem_take] at heq
      have hmod : (i + p) % x.length = i - (x.drop p).length := by
        simp only [List.length_drop]
        have hlt2 : i + p - x.length < x.length := by omega
        have hsub : i + p = (i + p - x.length) + x.length := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        omega
      simpa [hmod] using heq
  · intro hper
    refine List.ext_getElem (by simp [List.length_drop, List.length_take]; omega) ?_
    intro i hi1 hi2
    by_cases h1 : i < (x.drop p).length
    · rw [List.getElem_append_left h1, List.getElem_drop]
      simp only [List.length_drop] at h1
      have hmod : (i + p) % x.length = p + i := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simpa [hmod] using hper i hi2
    · rw [List.getElem_append_right (by omega), List.getElem_take]
      simp only [List.length_drop] at h1
      have hmod : (i + p) % x.length = i - (x.length - p) := by
        have hlt2 : i + p - x.length < x.length := by omega
        have hsub : i + p = (i + p - x.length) + x.length := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        omega
      simpa [List.length_drop, hmod] using hper i hi2

private theorem power_iff_rot (x : List Bool) :
    (∃ (y : List Bool) (k : ℕ), 2 ≤ k ∧ x = (List.replicate k y).flatten) ↔
      (x = [] ∨ ∃ p, 1 ≤ p ∧ p < x.length ∧ x.drop p ++ x.take p = x) := by
  constructor
  · rintro ⟨y, k, hk, rfl⟩
    cases hy : y with
    | nil =>
      left
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih]
    | cons b ys =>
      right
      have hylen : 0 < (b :: ys).length := by simp
      have htot : (List.replicate k (b :: ys)).flatten.length = k * (b :: ys).length :=
        replicate_flatten_length k (b :: ys)
      refine ⟨(b :: ys).length, by omega, ?_, ?_⟩
      · rw [htot]
        have : 2 * (b :: ys).length ≤ k * (b :: ys).length := Nat.mul_le_mul_right _ hk
        omega
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        simp only [List.replicate_succ, List.flatten_cons, List.drop_left, List.take_left]
        clear hk htot
        induction k' with
        | zero => simp
        | succ m ih =>
          simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
          rw [ih]
  · rintro (rfl | ⟨p₀, hp₀1, hp₀lt, hrot₀⟩)
    · exact ⟨[], 2, le_rfl, rfl⟩
    · classical
      let P : ℕ → Prop := fun p => 1 ≤ p ∧ p ≤ x.length ∧
        ∀ (i : ℕ) (hi : i < x.length), x[(i + p) % x.length]'(Nat.mod_lt _ (by omega)) = x[i]'hi
      have hex : ∃ p, P p := ⟨p₀, hp₀1, by omega, (rot_iff_periodic x (by omega)).1 hrot₀⟩
      let p := Nat.find hex
      have hp_spec : P p := Nat.find_spec hex
      have hp_min : ∀ q < p, ¬ P q := fun q hq => Nat.find_min hex hq
      have hp_le_p0 : p ≤ p₀ := Nat.find_min' hex ⟨hp₀1, by omega, (rot_iff_periodic x (by omega)).1 hrot₀⟩
      have hplt : p < x.length := by omega
      have hpos : 0 < x.length := by omega
      have hmul : ∀ (q i : ℕ) (hi : i < x.length),
          x[(i + q * p) % x.length]'(Nat.mod_lt _ hpos) = x[i]'hi := by
        intro q
        induction q with
        | zero => intro i hi; simp [Nat.mod_eq_of_lt hi]
        | succ q ih =>
          intro i hi
          have h1 := hp_spec.2.2 ((i + q * p) % x.length) (Nat.mod_lt _ hpos)
          have hmod : ((i + q * p) % x.length + p) % x.length = (i + (q + 1) * p) % x.length := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mul, one_mul, Nat.add_assoc]
          have h1' : x[(i + (q + 1) * p) % x.length]'(Nat.mod_lt _ hpos) =
              x[(i + q * p) % x.length]'(Nat.mod_lt _ hpos) := by
            simpa only [hmod] using h1
          exact h1'.trans (ih i hi)
      have hmod0 : x.length % p = 0 := by
        by_contra hne
        let r := x.length % p
        have hr1 : 1 ≤ r := by omega
        have hrlt : r < p := Nat.mod_lt x.length (by omega)
        have hP_r : P r := by
          refine ⟨hr1, by omega, fun i hi => ?_⟩
          have hstep := hmul (x.length / p) ((i + r) % x.length) (Nat.mod_lt _ hpos)
          have hdm : (x.length / p) * p + r = x.length := by
            have := Nat.div_add_mod x.length p
            rw [Nat.mul_comm] at this
            exact this
          have hmod2 : ((i + r) % x.length + (x.length / p) * p) % x.length = i := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hsum : i + r + (x.length / p) * p = i + x.length := by omega
            rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
          have hstep' : x[i]'hi = x[(i + r) % x.length]'(Nat.mod_lt _ hpos) := by
            simpa only [hmod2] using hstep
          exact hstep'.symm
        exact hp_min r hrlt hP_r
      let k := x.length / p
      have hk_mul : k * p = x.length := by
        have := Nat.div_add_mod x.length p
        rw [hmod0, add_zero, Nat.mul_comm] at this
        exact this
      have hk2 : 2 ≤ k := by
        by_contra hlt2
        have : k ≤ 1 := by omega
        have : k * p ≤ 1 * p := Nat.mul_le_mul_right p this
        omega
      refine ⟨x.take p, k, hk2, ?_⟩
      have htake_len : (x.take p).length = p := List.length_take_of_le (by omega)
      refine List.ext_getElem (by rw [replicate_flatten_length, htake_len, hk_mul]) ?_
      intro i hi1 hi2
      rw [replicate_flatten_getElem k (x.take p) (by rw [htake_len]; omega) i hi2]
      have hmod_lt : i % p < p := Nat.mod_lt i (by omega)
      have htake_get : (x.take p)[i % (x.take p).length]'(Nat.mod_lt i (by rw [htake_len]; omega)) =
          x[i % p]'(by omega) := by
        simp only [List.getElem_take]
        congr 1; rw [htake_len]
      rw [htake_get]
      have hper_i := hmul (i / p) (i % p) (by omega)
      have hdm : (i % p + (i / p) * p) % x.length = i := by
        have h1 : i % p + (i / p) * p = i := by
          have := Nat.div_add_mod i p
          rw [Nat.mul_comm] at this
          omega
        rw [h1, Nat.mod_eq_of_lt hi1]
      have hper_i' : x[i]'hi1 = x[i % p]'(by omega) := by
        simpa only [hdm] using hper_i
      exact hper_i'

-- State: pairB x (pairB cnt found)
private def rawStep (st : List Bool) : List Bool :=
  let x := (unpairB st).1
  let var := (unpairB st).2
  let cnt := (unpairB var).1
  let found := (unpairB var).2
  let sp := unpairB (cnt.map (fun _ => true) ++ false :: x)
  let eqFlag := if decide (sp.2 ++ sp.1 = x) = true then [true] else []
  let hit := sel sp.2 [] eqFlag
  let found' := sel found hit [true]
  pairB x (pairB (true :: cnt) found')

private def pStep (st : List Bool) : List Bool :=
  let ns := rawStep st
  let bound := true :: true :: true :: st
  sel (ns.drop bound.length) ns st

private theorem pStep_length_le (st : List Bool) : (pStep st).length ≤ st.length + 3 := by
  unfold pStep sel
  dsimp only
  split_ifs with h
  · have hle := List.drop_eq_nil_iff.1 h
    simp only [List.length_cons] at hle
    omega
  · omega

private theorem pStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString pStep := by
  have hx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).1) := cpt_unpairB1
  have hvar : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB st).2) := cpt_unpairB2
  have hcnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).1) := cpt_unpairB1_1 hvar
  have hfound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => (unpairB (unpairB st).2).2) := cpt_unpairB2_1 hvar
  have hcnt_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => (unpairB (unpairB st).2).1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hcnt map_true_poly
  have hsp_code := cpt_app2 hcnt_map (cpt_cons1 false hx)
  have hsp1 := cpt_unpairB1_1 hsp_code
  have hsp2 := cpt_unpairB2_1 hsp_code
  have hrot := cpt_app2 hsp2 hsp1
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun st : List Bool =>
        ((unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB st).1)).2 ++
         (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB st).1)).1,
         (unpairB st).1)) := by
    rw [← encodePair_eq]
    exact cpt_pair hrot hx
  have heqB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      ((fun q : List Bool × List Bool => decide (q.1 = q.2)) ∘
        (fun st : List Bool =>
          ((unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB st).1)).2 ++
           (unpairB (((unpairB (unpairB st).2).1).map (fun _ => true) ++ false :: (unpairB st).1)).1,
           (unpairB st).1))) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpair PvsNP.Units.m2_eq_polytime
  have heqFlag := cpt_bitFlag heqB
  have hhit := cpt_sel hsp2 (cpt_const []) heqFlag
  have hfound' := cpt_sel hfound hhit (cpt_const [true])
  have hraw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rawStep :=
    cpt_pairB2 hx (cpt_pairB2 (cpt_cons1 true hcnt) hfound')
  have hbound : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool => true :: true :: true :: st) :=
    cpt_cons1 true (cpt_cons1 true (cpt_cons1 true cpt_id))
  have hbound_map : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun u : List Bool => u.map (fun _ => true)) ∘ (fun st : List Bool => true :: true :: true :: st)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hbound map_true_poly
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep st)).2) :=
    cpt_unpairB2_1 (cpt_app2 hbound_map (cpt_cons1 false hraw))
  have hsel : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun st : List Bool =>
        sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep st)).2
          (rawStep st) st) :=
    cpt_sel hdrop hraw cpt_id
  have heq : (fun st : List Bool =>
      sel (unpairB (((true :: true :: true :: st).map (fun _ => true)) ++ false :: rawStep st)).2
        (rawStep st) st) = pStep := by
    funext st
    simp only [pStep, unpairB_map_true]
  rwa [heq] at hsel

private theorem pStep_valid (x : List Bool) (p : ℕ) (b : Bool) :
    pStep (pairB x (pairB (un p) (if b then [true] else []))) =
      pairB x (pairB (un (p + 1))
        (if (b || (decide (p < x.length) && decide (x.drop p ++ x.take p = x))) then [true] else [])) := by
  have hraw : rawStep (pairB x (pairB (un p) (if b then [true] else []))) =
      pairB x (pairB (un (p + 1))
        (if (b || (decide (p < x.length) && decide (x.drop p ++ x.take p = x))) then [true] else [])) := by
    unfold rawStep
    simp only [unpairB_pairB, unpairB_map_true, un_length]
    have hcons : true :: un p = un (p + 1) := by simp [un, List.replicate_succ]
    rw [hcons]
    congr 1; congr 1
    by_cases hlt : p < x.length
    · have hne : x.drop p ≠ [] := by
        intro hnil
        have := List.drop_eq_nil_iff.1 hnil
        omega
      cases b <;> by_cases hrot : x.drop p ++ x.take p = x <;> simp [hlt, hne, hrot, sel]
    · have hnil : x.drop p = [] := List.drop_eq_nil_iff.2 (by omega)
      cases b <;> simp [hlt, hnil, sel]
  have hlen : (rawStep (pairB x (pairB (un p) (if b then [true] else [])))).length ≤
      (pairB x (pairB (un p) (if b then [true] else []))).length + 3 := by
    rw [hraw]
    simp only [pairB_length, un_length]
    cases b <;> cases (decide (p < x.length) && decide (x.drop p ++ x.take p = x)) <;> simp <;> omega
  unfold pStep
  dsimp only
  have hnil : (rawStep (pairB x (pairB (un p) (if b then [true] else [])))).drop
      (true :: true :: true :: pairB x (pairB (un p) (if b then [true] else []))).length = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_cons]
    omega
  rw [hnil]
  simp only [sel, ↓reduceIte]
  exact hraw

private theorem iter_pStep (x : List Bool) :
    ∀ (t p : ℕ) (b : Bool),
      pStep^[t] (pairB x (pairB (un p) (if b then [true] else []))) =
        pairB x (pairB (un (p + t))
          (if (b || (List.range t).any (fun r =>
              decide (p + r < x.length) && decide (x.drop (p + r) ++ x.take (p + r) = x)))
           then [true] else [])) := by
  intro t
  induction t with
  | zero => intro p b; simp
  | succ t ih =>
    intro p b
    rw [Function.iterate_succ_apply, pStep_valid, ih (p + 1)]
    have hadd : p + 1 + t = p + (t + 1) := by omega
    rw [hadd]
    congr 1; congr 1
    have heq : (b || (decide (p < x.length) && decide (x.drop p ++ x.take p = x)) ||
        (List.range t).any (fun r =>
          decide (p + 1 + r < x.length) && decide (x.drop (p + 1 + r) ++ x.take (p + 1 + r) = x))) =
      (b || (List.range (t + 1)).any (fun r =>
          decide (p + r < x.length) && decide (x.drop (p + r) ++ x.take (p + r) = x))) := by
      cases b with
      | true => simp
      | false =>
        simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨r, hr, h1, h2⟩)
          · exact ⟨0, by omega, by simpa using h1, by simpa using h2⟩
          · refine ⟨r + 1, by omega, ?_, ?_⟩
            · omega
            · have : p + (r + 1) = p + 1 + r := by omega
              rw [this]; exact h2
        · rintro ⟨r, hr, h1, h2⟩
          cases r with
          | zero => exact Or.inl ⟨by simpa using h1, by simpa using h2⟩
          | succ r' =>
            right
            refine ⟨r', by omega, ?_, ?_⟩
            · omega
            · have : p + 1 + r' = p + (r' + 1) := by omega
              rw [this]; exact h2
    rw [heq]

theorem main :
    ({x : List Bool | ∃ (y : List Bool) (k : ℕ), 2 ≤ k ∧ x = (List.replicate k y).flatten} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨cStep⟩ := pStep_poly
  have hIter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun q : List Bool × List Bool => pStep^[q.2.length] q.1) :=
    Iter.iter_polyTime pStep cStep 3 pStep_length_le
  have hInit := cpt_pairB2 cpt_id (cpt_const (pairB [true] []))
  have hPair := cpt_pair hInit cpt_id
  have hRun := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hPair hIter
  have hFound := cpt_unpairB2_1 (cpt_unpairB2_1 hRun)
  have hFinal := cpt_sel cpt_id (cpt_const [true]) hFound
  have hDec := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hFinal cpt_neU
  refine ⟨_, hDec, fun x => ?_⟩
  change (∃ (y : List Bool) (k : ℕ), 2 ≤ k ∧ x = (List.replicate k y).flatten) ↔ _
  rw [power_iff_rot]
  simp only [Function.comp_apply]
  cases hx : x with
  | nil =>
    simp [sel]
  | cons b xs =>
    have hiter := iter_pStep (b :: xs) (b :: xs).length 1 false
    simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hiter
    have hun1 : un 1 = [true] := rfl
    rw [hun1] at hiter
    simp only [Function.comp_apply, id_eq, sel, List.cons_ne_nil, ↓reduceIte]
    rw [hiter, unpairB_pairB, unpairB_pairB]
    have hiff : (∃ p, 1 ≤ p ∧ p < (b :: xs).length ∧ (b :: xs).drop p ++ (b :: xs).take p = b :: xs) ↔
        (List.range (b :: xs).length).any (fun r =>
          decide (1 + r < (b :: xs).length) &&
          decide ((b :: xs).drop (1 + r) ++ (b :: xs).take (1 + r) = b :: xs)) = true := by
      rw [List.any_eq_true]
      simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨p, hp1, hplt, hrot⟩
        have h1p : 1 + (p - 1) = p := by omega
        exact ⟨p - 1, by omega, by rwa [h1p], by rwa [h1p]⟩
      · rintro ⟨r, _, hlt, hrot⟩
        exact ⟨1 + r, by omega, hlt, hrot⟩
    simp only [List.cons_ne_nil, false_or]
    cases hany : (List.range (b :: xs).length).any (fun r =>
        decide (1 + r < (b :: xs).length) &&
        decide ((b :: xs).drop (1 + r) ++ (b :: xs).take (1 + r) = b :: xs)) with
    | false =>
      simp only [hany, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true] at hiff ⊢
      exact hiff
    | true =>
      simp only [hany, ↓reduceIte, List.isEmpty_cons, Bool.not_false] at hiff ⊢
      exact hiff

end PvsNP.Units.tl_lang_power_p

theorem PvsNP.Units.tl_lang_power_p :
    ({x : List Bool | ∃ (y : List Bool) (k : ℕ), 2 ≤ k ∧ x = (List.replicate k y).flatten} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_power_p.main
