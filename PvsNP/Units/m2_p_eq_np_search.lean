import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_poly_clock
import PvsNP.Units.m2_iterate_poly_times

set_option autoImplicit false

namespace PvsNP.Units.m2_p_eq_np_search

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

lemma encodeString_eq : PvsNP.encodeString = (fun x : List Bool => x) := by
  funext x; rfl

lemma encodePair_eq : PvsNP.encodePair = encodePair := by
  funext p; rfl

lemma poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

lemma fstRun_nonempty_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
      (fun st => some st) true l = [true] := by
  induction l with
  | nil => rfl
  | cons _ rest ih => simpa [fstRun] using ih

lemma cpt_isNonempty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => !s.isEmpty) := by
  refine fst_polyTime _ _ _
    (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun st => some st) false ?_
  intro s
  cases s with
  | nil => rfl
  | cons _ rest =>
    simpa [Computability.encodeBool, fstRun] using (fstRun_nonempty_true rest).symm

lemma cpt_andPair {f1 f2 : List Bool × List Bool → Bool}
    (hf1 : ComputableInPolyTime encodePair Computability.encodeBool f1)
    (hf2 : ComputableInPolyTime encodePair Computability.encodeBool f2) :
    ComputableInPolyTime encodePair Computability.encodeBool (fun q => f1 q && f2 q) := by
  have hfl1 := cpt_bitFlag hf1
  have hfl2 := cpt_bitFlag hf2
  have hcomb := cpt_comp (cpt_comp (cpt_pairG hfl1 hfl2) cpt_ifNonempty) cpt_isNonempty
  have heq : (fun q => !(if (if f1 q then [true] else []) = [] then []
      else if f2 q then [true] else []).isEmpty) = (fun q => f1 q && f2 q) := by
    funext q
    cases f1 q <;> cases f2 q <;> rfl
  rwa [← heq]

def Ext (V : List Bool × List Bool → Bool) (p : Polynomial ℕ) : Language Bool :=
  {s : List Bool |
    ∃ r : List Bool,
      ((unpairB s).2 ++ r).length ≤ p.eval (unpairB s).1.length ∧
      V ((unpairB s).1, (unpairB s).2 ++ r) = true}

def VExt (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (q : List Bool × List Bool) : Bool :=
  decide (((unpairB q.1).2 ++ q.2).length ≤
    (List.replicate (p.eval (unpairB q.1).1.length) true).length) &&
  V ((unpairB q.1).1, (unpairB q.1).2 ++ q.2)

lemma ext_mem_NP (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    Ext V p ∈ PvsNP.NP := by
  have hV' : ComputableInPolyTime encodePair Computability.encodeBool V := by
    rwa [← encodePair_eq]
  have hx : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => (unpairB q.1).1) :=
    cpt_comp (g := fun s => (unpairB s).1) cpt_fst cpt_unpairB1
  have hu : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => (unpairB q.1).2) :=
    cpt_comp (g := fun s => (unpairB s).2) cpt_fst cpt_unpairB2
  have hw : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => (unpairB q.1).2 ++ q.2) :=
    cpt_comp (cpt_pairG hu cpt_snd) cpt_append
  have hclk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
    PvsNP.Units.m2_poly_clock p
  have hbound : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool =>
        List.replicate (p.eval (unpairB q.1).1.length) true) :=
    cpt_comp hx hclk
  have hb1 : ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool =>
        decide (((unpairB q.1).2 ++ q.2).length ≤
          (List.replicate (p.eval (unpairB q.1).1.length) true).length)) :=
    cpt_comp (cpt_pairG hbound hw) LenCmp.lenLE_polyTime
  have hb2 : ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => V ((unpairB q.1).1, (unpairB q.1).2 ++ q.2)) :=
    cpt_comp (cpt_pairG hx hw) hV'
  have hVExt : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (VExt V p) := by
    rw [encodePair_eq]
    exact cpt_andPair hb1 hb2
  refine ⟨VExt V p, p, hVExt, ?_⟩
  intro s
  change (∃ r : List Bool,
    ((unpairB s).2 ++ r).length ≤ p.eval (unpairB s).1.length ∧
    V ((unpairB s).1, (unpairB s).2 ++ r) = true) ↔
    ∃ r : List Bool, r.length ≤ p.eval s.length ∧ VExt V p (s, r) = true
  constructor
  · rintro ⟨r, hlen, hvr⟩
    have hun : (unpairB s).1.length ≤ s.length := by
      have h := unpairB_length s
      omega
    have hrlen : r.length ≤ p.eval s.length :=
      calc r.length ≤ ((unpairB s).2 ++ r).length := by simp
        _ ≤ p.eval (unpairB s).1.length := hlen
        _ ≤ p.eval s.length := poly_eval_mono p hun
    refine ⟨r, hrlen, ?_⟩
    simp only [VExt, List.length_replicate, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlen, hvr⟩
  · rintro ⟨r, _, hvr⟩
    simp only [VExt, List.length_replicate, Bool.and_eq_true, decide_eq_true_eq] at hvr
    exact ⟨r, hvr.1, hvr.2⟩

def stepF (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let u := (unpairB s).2
  let vFlag := if V (x, u) then [true] else []
  let fFlag := if decExt (pairB x (u ++ [false])) then [true] else []
  let nextU := sel vFlag (sel fFlag (u ++ [true]) (u ++ [false])) u
  pairB x nextU

lemma stepF_length (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (s : List Bool) :
    (stepF V decExt s).length ≤ s.length + 2 := by
  have hun := unpairB_length s
  unfold stepF
  simp only [pairB_length]
  have hnext :
      (sel (if V ((unpairB s).1, (unpairB s).2) then [true] else [])
        (sel (if decExt (pairB (unpairB s).1 ((unpairB s).2 ++ [false])) then [true] else [])
          ((unpairB s).2 ++ [true]) ((unpairB s).2 ++ [false]))
        (unpairB s).2).length ≤ (unpairB s).2.length + 1 := by
    apply sel_length
    · apply sel_length <;> simp
    · omega
  omega

lemma cpt_stepF (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V)
    (hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decExt) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (stepF V decExt) := by
  have hV' : ComputableInPolyTime encodePair Computability.encodeBool V := by
    rwa [← encodePair_eq]
  have hdec' : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool decExt := by
    rwa [← encodeString_eq]
  have hvFlag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => if V ((unpairB s).1, (unpairB s).2) then [true] else []) :=
    cpt_bitFlag (cpt_comp cpt_unpairB hV')
  have huFalse : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2 ++ [false]) :=
    cpt_app2 cpt_unpairB2 (cpt_const [false])
  have huTrue : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2 ++ [true]) :=
    cpt_app2 cpt_unpairB2 (cpt_const [true])
  have hpFalse : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (unpairB s).1 ((unpairB s).2 ++ [false])) :=
    cpt_pairB2 cpt_unpairB1 huFalse
  have hfFlag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => if decExt (pairB (unpairB s).1 ((unpairB s).2 ++ [false])) then [true] else []) :=
    cpt_bitFlag (cpt_comp hpFalse hdec')
  have hnextU := cpt_sel hvFlag (cpt_sel hfFlag huTrue huFalse) cpt_unpairB2
  have hres := cpt_pairB2 cpt_unpairB1 hnextU
  rw [encodeString_eq]
  exact hres

lemma stepF_pairB_true (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (x u : List Bool) (hv : V (x, u) = true) :
    stepF V decExt (pairB x u) = pairB x u := by
  simp [stepF, unpairB_pairB, hv, sel]

lemma stepF_pairB_false (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (p : Polynomial ℕ)
    (hdec_iff : ∀ s, s ∈ Ext V p ↔ decExt s = true)
    (x u : List Bool) (hv : V (x, u) = false)
    (hinv : ∃ r : List Bool, (u ++ r).length ≤ p.eval x.length ∧ V (x, u ++ r) = true) :
    ∃ b : Bool,
      stepF V decExt (pairB x u) = pairB x (u ++ [b]) ∧
      ∃ r' : List Bool, ((u ++ [b]) ++ r').length ≤ p.eval x.length ∧
        V (x, (u ++ [b]) ++ r') = true := by
  obtain ⟨r, hlen, hvr⟩ := hinv
  cases r with
  | nil =>
    simp at hvr
    rw [hv] at hvr
    exact Bool.noConfusion hvr
  | cons b0 r' =>
    by_cases hf : decExt (pairB x (u ++ [false])) = true
    · refine ⟨false, ?_, ?_⟩
      · simp [stepF, unpairB_pairB, hv, hf, sel]
      · have hmem := (hdec_iff (pairB x (u ++ [false]))).mpr hf
        rcases hmem with ⟨r0, hr0len, hvr0⟩
        simp only [unpairB_pairB] at hr0len hvr0
        exact ⟨r0, hr0len, hvr0⟩
    · have hff : decExt (pairB x (u ++ [false])) = false := Bool.eq_false_iff.mpr hf
      have hb0 : b0 = true := by
        cases b0 with
        | true => rfl
        | false =>
          have hmem : pairB x (u ++ [false]) ∈ Ext V p := by
            change ∃ r0 : List Bool,
              ((unpairB (pairB x (u ++ [false]))).2 ++ r0).length ≤
                p.eval (unpairB (pairB x (u ++ [false]))).1.length ∧
              V ((unpairB (pairB x (u ++ [false]))).1,
                (unpairB (pairB x (u ++ [false]))).2 ++ r0) = true
            refine ⟨r', ?_, ?_⟩
            · simpa [unpairB_pairB, List.append_assoc] using hlen
            · simpa [unpairB_pairB, List.append_assoc] using hvr
          exact absurd ((hdec_iff _).mp hmem) hf
      subst hb0
      refine ⟨true, ?_, r', ?_, ?_⟩
      · simp [stepF, unpairB_pairB, hv, hff, sel]
      · simpa [List.append_assoc] using hlen
      · simpa [List.append_assoc] using hvr

lemma iter_stepF_inv (V : List Bool × List Bool → Bool) (decExt : List Bool → Bool)
    (p : Polynomial ℕ)
    (hdec_iff : ∀ s, s ∈ Ext V p ↔ decExt s = true)
    (x : List Bool) :
    ∀ (m : ℕ) (u : List Bool),
      (∃ r : List Bool, (u ++ r).length ≤ p.eval x.length ∧ V (x, u ++ r) = true) →
      ∃ u' : List Bool,
        (stepF V decExt)^[m] (pairB x u) = pairB x u' ∧
        (∃ r : List Bool, (u' ++ r).length ≤ p.eval x.length ∧ V (x, u' ++ r) = true) ∧
        (V (x, u') = true ∨ u'.length = u.length + m) := by
  intro m
  induction m with
  | zero =>
    intro u hinv
    exact ⟨u, rfl, hinv, Or.inr (by omega)⟩
  | succ m ih =>
    intro u hinv
    obtain ⟨u', hiter, hinv', hdisj⟩ := ih u hinv
    rw [Function.iterate_succ_apply', hiter]
    cases hv : V (x, u') with
    | true =>
      refine ⟨u', stepF_pairB_true V decExt x u' hv, hinv', Or.inl hv⟩
    | false =>
      have hlen_u' : u'.length = u.length + m := by
        rcases hdisj with ht | hl
        · rw [hv] at ht; exact Bool.noConfusion ht
        · exact hl
      obtain ⟨b, hstep, hinv''⟩ := stepF_pairB_false V decExt p hdec_iff x u' hv hinv'
      refine ⟨u' ++ [b], hstep, hinv'', Or.inr ?_⟩
      simp [hlen_u']
      omega

theorem main_proof :
    PvsNP.P = PvsNP.NP → ∀ (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      PvsNP.PolyTimeVerifier L V p →
        ∃ F : List Bool → List Bool,
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F ∧
          ∀ x ∈ L, (F x).length ≤ p.eval x.length ∧ V (x, F x) = true := by
  intro hPNP L V p hV
  have hExtNP : Ext V p ∈ PvsNP.NP := ext_mem_NP V p hV.1
  have hExtP : Ext V p ∈ PvsNP.P := hPNP.symm ▸ hExtNP
  obtain ⟨decExt, hdec, hdec_iff⟩ := hExtP
  have hstep : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (stepF V decExt) :=
    cpt_stepF V decExt hV.1 hdec
  have hiter : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun y : List Bool => (stepF V decExt)^[p.eval y.length] y) :=
    PvsNP.Units.m2_iterate_poly_times (stepF V decExt) 2 p hstep (stepF_length V decExt)
  have hinit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB x []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hiter' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun y : List Bool => (stepF V decExt)^[p.eval y.length] y) := by
    rwa [← encodeString_eq]
  let F : List Bool → List Bool :=
    fun x => (unpairB ((stepF V decExt)^[p.eval (pairB x []).length] (pairB x []))).2
  have hF : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F := by
    rw [encodeString_eq]
    exact cpt_comp (g := fun s => (unpairB s).2) (cpt_comp hinit hiter') cpt_unpairB2
  refine ⟨F, hF, ?_⟩
  intro x hx
  obtain ⟨w, hwlen, hvw⟩ := (hV.2 x).mp hx
  have hinv0 : ∃ r : List Bool, (([] : List Bool) ++ r).length ≤ p.eval x.length ∧
      V (x, ([] : List Bool) ++ r) = true :=
    ⟨w, by simpa using hwlen, by simpa using hvw⟩
  obtain ⟨u', hrun, ⟨r, hurlen, hvr⟩, hdisj⟩ :=
    iter_stepF_inv V decExt p hdec_iff x (p.eval (pairB x []).length) [] hinv0
  have hFx : F x = u' := by
    simp only [F, hrun, unpairB_pairB]
  rw [hFx]
  have hu'len : u'.length ≤ p.eval x.length := by
    have : u'.length ≤ (u' ++ r).length := by simp
    omega
  refine ⟨hu'len, ?_⟩
  rcases hdisj with hvt | hulen
  · exact hvt
  · have hpx : p.eval x.length ≤ p.eval (pairB x []).length :=
      poly_eval_mono p (by simp [pairB_length]; omega)
    have hr0 : r.length = 0 := by
      simp at hurlen hulen
      omega
    have hrnil : r = [] := List.eq_nil_of_length_eq_zero hr0
    subst hrnil
    simpa using hvr

end PvsNP.Units.m2_p_eq_np_search

theorem PvsNP.Units.m2_p_eq_np_search :
    PvsNP.P = PvsNP.NP → ∀ (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      PvsNP.PolyTimeVerifier L V p →
        ∃ F : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F ∧
          ∀ x ∈ L, (F x).length ≤ p.eval x.length ∧ V (x, F x) = true :=
  PvsNP.Units.m2_p_eq_np_search.main_proof
