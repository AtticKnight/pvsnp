import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_np_verifier_normal

/-
Proves `coNP` is closed under Kleene star (`KStar.kstar L ∈ PvsNP.coNP`) via DAG reachability
cuts: for any `x : List Bool`, `x ∉ KStar.kstar L` iff there exists a cut bitvector `cut` of
length `x.length + 1` with `cut[0] = true`, `cut[x.length] = false`, and for every `i < j ≤
x.length` with `cut[i] = true` and `cut[j] = false`, the substring `(x.drop i).take (j - i)`
lies in `Lᶜ`. The NP certificate packs `cut` together with a nested `pairB` stack of `Lᶜ`
witnesses for all crossing pairs in lexicographic order; two nested `Iter.iter_polyTime` loops
verify the cut and every crossing witness in polynomial time.

Built on the settled units PvsNP.Units.fr_ladner, m2_ite_polytime, m2_dfa_in_p,
m2_transducer_polytime, m2_polytime_comp, and m2_reverse_polytime of github.com/makedotfun/pvsnp
(Apache License 2.0).
-/

namespace PvsNP.Units.tc_closure_star_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem unpairB_len_bound (s : List Bool) :
    (unpairB s).1.length + (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

private theorem pairB_length (a b : List Bool) :
    (pairB a b).length = a.length + a.length + b.length + 1 := by
  simp only [pairB, List.length_append, un_length, List.length_cons]
  omega

private theorem headD_false_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y
    induction y with
    | nil => rfl
    | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => x.headD false := by
    funext x
    have hx := hdec x
    change ((x.foldl δ none == some true) = true) ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, List.headD_nil] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, δ, hfold_some, List.headD_cons] at hx ⊢
      cases b with
      | false => cases hcx : c (false :: y) <;> simp_all
      | true => exact hx.1 (by decide)
  rwa [← heq]

private theorem bool_not_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeAnswer PvsNP.encodeAnswer (fun b : Bool => !b) :=
  filterMap_polyTime Computability.encodeBool Computability.encodeBool (fun b : Bool => !b)
    (fun b => some (!b)) (fun b => by cases b <;> rfl)

private theorem bool_and_poly {f g : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => f s && g s) := by
  have hgL := PvsNP.Units.m2_ite_polytime g (fun _ => [true]) (fun _ => [false])
    hg (cpt_const [true]) (cpt_const [false])
  have handL := PvsNP.Units.m2_ite_polytime f _ (fun _ => [false]) hf hgL (cpt_const [false])
  have hres : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool =>
        (if f s = true then if g s = true then [true] else [false] else [false]).headD false) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
      _ (fun l => l.headD false) handL headD_false_poly
  have heq : (fun s : List Bool => (if f s = true then if g s = true then [true] else [false] else [false]).headD false) =
      (fun s => f s && g s) := by
    funext s
    cases f s <;> cases g s <;> rfl
  rwa [heq] at hres

private theorem len_le_poly {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((f s).length ≤ (g s).length)) :=
  cpt_comp (cpt_pair hg hf) LenCmp.lenLE_polyTime

private theorem len_eq_poly {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((f s).length = (g s).length)) := by
  have h := bool_and_poly (len_le_poly hf hg) (len_le_poly hg hf)
  have heq : (fun s => decide ((f s).length ≤ (g s).length) && decide ((g s).length ≤ (f s).length)) =
      (fun s => decide ((f s).length = (g s).length)) := by
    funext s
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rwa [heq] at h

-- ============================================================
-- Inner loop: for fixed i with cut[i] = true, check j = i+1 .. n
-- State: ok :: pairB (pairB (pairB cur_cut cur_pref) cur_rem_x) wStack
-- ============================================================

private def inCurCut (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s.tail).1).1).1
private def inCurPref (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s.tail).1).1).2
private def inCurRemX (s : List Bool) : List Bool := (unpairB (unpairB s.tail).1).2
private def inWStack (s : List Bool) : List Bool := (unpairB s.tail).2

private def inNewPref (s : List Bool) : List Bool :=
  if (inCurRemX s).headD false = true then
    inCurPref s ++ [true]
  else
    inCurPref s ++ [false]

private def inNextTrip (s : List Bool) : List Bool :=
  pairB (pairB (inCurCut s).tail (inNewPref s)) (inCurRemX s).tail

private def inStep (V : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  if (inCurCut s).headD false = true then
    if s.headD false = true then
      true :: pairB (inNextTrip s) (inWStack s)
    else
      false :: pairB (inNextTrip s) (inWStack s)
  else
    if (s.headD false && V (inNewPref s, (unpairB (inWStack s)).1)) = true then
      true :: pairB (inNextTrip s) (unpairB (inWStack s)).2
    else
      false :: pairB (inNextTrip s) (unpairB (inWStack s)).2

private theorem inStep_eq (V : List Bool × List Bool → Bool)
    (ok : Bool) (c : Bool) (cc cp rx ws : List Bool) :
    inStep V (ok :: pairB (pairB (pairB cc cp) (c :: rx)) ws) =
      if cc.headD false = true then
        ok :: pairB (pairB (pairB cc.tail (cp ++ [c])) rx) ws
      else
        (ok && V (cp ++ [c], (unpairB ws).1)) ::
          pairB (pairB (pairB cc.tail (cp ++ [c])) rx) (unpairB ws).2 := by
  unfold inStep inNextTrip inNewPref inCurCut inCurPref inCurRemX inWStack
  simp only [List.headD_cons, List.tail_cons, unpairB_pairB]
  cases c <;> cases hcc : cc.headD false <;> cases ok <;>
    cases hv : V (cp ++ [_], (unpairB ws).1) <;> simp [hcc, hv]

private theorem inStep_wStack_le (V : List Bool × List Bool → Bool) (s : List Bool) :
    (unpairB (inStep V s).tail).2.length ≤ (unpairB s.tail).2.length := by
  unfold inStep
  split_ifs <;> simp only [List.tail_cons, unpairB_pairB, inWStack]
  · exact le_rfl
  · exact le_rfl
  · have := unpairB_len_bound (unpairB s.tail).2; omega
  · have := unpairB_len_bound (unpairB s.tail).2; omega

private theorem inStep_iter_wStack_le (V : List Bool × List Bool → Bool) (m : ℕ) (s : List Bool) :
    (unpairB ((inStep V)^[m] s).tail).2.length ≤ (unpairB s.tail).2.length := by
  induction m generalizing s with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (inStep V s)).trans (inStep_wStack_le V s)

private theorem inStep_len (V : List Bool × List Bool → Bool) (s : List Bool) :
    (inStep V s).length ≤ s.length + 12 := by
  have h1 := unpairB_len_bound s.tail
  have h2 := unpairB_len_bound (unpairB s.tail).1
  have h3 := unpairB_len_bound (unpairB (unpairB s.tail).1).1
  have h4 := unpairB_len_bound (unpairB s.tail).2
  have ht : s.tail.length ≤ s.length := by simp
  have hnp : (inNewPref s).length = (inCurPref s).length + 1 := by
    unfold inNewPref; split_ifs <;> simp
  have hnt : (inNextTrip s).length ≤
      4 * (inCurCut s).length + 2 * (inCurPref s).length + (inCurRemX s).length + 5 := by
    unfold inNextTrip
    rw [pairB_length, pairB_length, hnp]
    have hc1 : (inCurCut s).tail.length ≤ (inCurCut s).length := by simp
    have hx1 : (inCurRemX s).tail.length ≤ (inCurRemX s).length := by simp
    omega
  have hbound : 8 * (inCurCut s).length + 4 * (inCurPref s).length +
      2 * (inCurRemX s).length + (inWStack s).length ≤ s.length := by
    unfold inCurCut inCurPref inCurRemX inWStack
    omega
  unfold inStep
  split_ifs <;> simp only [List.length_cons] <;> rw [pairB_length] <;>
    (try unfold inWStack at hbound ⊢) <;> omega

private theorem inStep_poly (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (inStep V) := by
  have htail := cpt_tail1 cpt_id
  have h1 := cpt_unpairB1_1 htail
  have hws : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inWStack :=
    cpt_unpairB2_1 htail
  have h11 := cpt_unpairB1_1 h1
  have hrx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inCurRemX :=
    cpt_unpairB2_1 h1
  have hcc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inCurCut :=
    cpt_unpairB1_1 h11
  have hcp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inCurPref :=
    cpt_unpairB2_1 h11
  have hrx_hd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    inCurRemX (fun l => l.headD false) hrx headD_false_poly
  have hnp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inNewPref :=
    PvsNP.Units.m2_ite_polytime _ _ _ hrx_hd
      (cpt_app2 hcp (cpt_const [true])) (cpt_app2 hcp (cpt_const [false]))
  have hnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString inNextTrip :=
    cpt_pairB2 (cpt_pairB2 (cpt_tail1 hcc) hnp) (cpt_tail1 hrx)
  have hkeep := cpt_pairB2 hnt hws
  have hpop := cpt_pairB2 hnt (cpt_unpairB2_1 hws)
  have hV' : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeAnswer V := by rwa [encodePair_eq]
  have hVcall : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => V (inNewPref s, (unpairB (inWStack s)).1)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeAnswer
      (fun s => (inNewPref s, (unpairB (inWStack s)).1)) V
      (cpt_pair hnp (cpt_unpairB1_1 hws)) hV'
  have hok_and_V := bool_and_poly headD_false_poly hVcall
  have hcc_hd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    inCurCut (fun l => l.headD false) hcc headD_false_poly
  have hbr1 := PvsNP.Units.m2_ite_polytime (fun s => s.headD false) _ _
    headD_false_poly (cpt_cons1 true hkeep) (cpt_cons1 false hkeep)
  have hbr2 := PvsNP.Units.m2_ite_polytime _ _ _
    hok_and_V (cpt_cons1 true hpop) (cpt_cons1 false hpop)
  exact PvsNP.Units.m2_ite_polytime _ _ _ hcc_hd hbr1 hbr2

-- ============================================================
-- Outer loop: iterate i = 0 .. n-1
-- State: ok :: pairB (pairB rem_cut rem_x) wStack
-- ============================================================

private def outRemCut (s : List Bool) : List Bool := (unpairB (unpairB s.tail).1).1
private def outRemX (s : List Bool) : List Bool := (unpairB (unpairB s.tail).1).2
private def outWStack (s : List Bool) : List Bool := (unpairB s.tail).2

private def runInner (V : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  (inStep V)^[(outRemX s).length]
    (s.headD false :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s))

private def outStep (V : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  if (outRemCut s).headD false = true then
    if (runInner V s).headD false = true then
      true :: pairB (pairB (outRemCut s).tail (outRemX s).tail) (unpairB (runInner V s).tail).2
    else
      false :: pairB (pairB (outRemCut s).tail (outRemX s).tail) (unpairB (runInner V s).tail).2
  else
    if s.headD false = true then
      true :: pairB (pairB (outRemCut s).tail (outRemX s).tail) (outWStack s)
    else
      false :: pairB (pairB (outRemCut s).tail (outRemX s).tail) (outWStack s)

private theorem outStep_len (V : List Bool × List Bool → Bool) (s : List Bool) :
    (outStep V s).length ≤ s.length + 6 := by
  have h1 := unpairB_len_bound s.tail
  have h2 := unpairB_len_bound (unpairB s.tail).1
  have ht : s.tail.length ≤ s.length := by simp
  have hws_in : (unpairB (runInner V s).tail).2.length ≤ (outWStack s).length := by
    unfold runInner
    have h := inStep_iter_wStack_le V (outRemX s).length
      (s.headD false :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s))
    simpa [List.tail_cons, unpairB_pairB] using h
  have hrc : (outRemCut s).tail.length ≤ (outRemCut s).length := by simp
  have hrx : (outRemX s).tail.length ≤ (outRemX s).length := by simp
  have hb : 4 * (outRemCut s).length + 2 * (outRemX s).length + (outWStack s).length ≤ s.length := by
    unfold outRemCut outRemX outWStack
    omega
  unfold outStep
  split_ifs <;> simp only [List.length_cons] <;> rw [pairB_length, pairB_length] <;> omega

private theorem outStep_poly (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (outStep V) := by
  have htail := cpt_tail1 cpt_id
  have h1 := cpt_unpairB1_1 htail
  have hws : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString outWStack :=
    cpt_unpairB2_1 htail
  have hrc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString outRemCut :=
    cpt_unpairB1_1 h1
  have hrx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString outRemX :=
    cpt_unpairB2_1 h1
  obtain ⟨cin⟩ := inStep_poly V hV
  have hiter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun p : List Bool × List Bool => (inStep V)^[p.2.length] p.1) :=
    Iter.iter_polyTime (inStep V) cin 12 (inStep_len V)
  have hinitBase := cpt_pairB2 (cpt_pairB2 (cpt_pairB2 (cpt_tail1 hrc) (cpt_const [])) hrx) hws
  have hinit0 := PvsNP.Units.m2_ite_polytime (fun s => s.headD false)
    (fun s => true :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s))
    (fun s => false :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s))
    headD_false_poly (cpt_cons1 true hinitBase) (cpt_cons1 false hinitBase)
  have hinit_eq :
      (fun x : List Bool =>
        if x.headD false = true then
          true :: pairB (pairB (pairB (outRemCut x).tail []) (outRemX x)) (outWStack x)
        else
          false :: pairB (pairB (pairB (outRemCut x).tail []) (outRemX x)) (outWStack x)) =
      (fun s : List Bool =>
        s.headD false :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s)) := by
    funext s
    cases s.headD false <;> rfl
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => s.headD false :: pairB (pairB (pairB (outRemCut s).tail []) (outRemX s)) (outWStack s)) := by
    rwa [hinit_eq] at hinit0
  have hrun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (runInner V) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      _ _ (cpt_pair hinit hrx) hiter
  have hrun_hd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    (runInner V) (fun l => l.headD false) hrun headD_false_poly
  have hrun_ws := cpt_unpairB2_1 (cpt_tail1 hrun)
  have hnextPair := cpt_pairB2 (cpt_tail1 hrc) (cpt_tail1 hrx)
  have hbr1_body := cpt_pairB2 hnextPair hrun_ws
  have hbr2_body := cpt_pairB2 hnextPair hws
  have hbr1 := PvsNP.Units.m2_ite_polytime _ _ _ hrun_hd
    (cpt_cons1 true hbr1_body) (cpt_cons1 false hbr1_body)
  have hbr2 := PvsNP.Units.m2_ite_polytime (fun s => s.headD false) _ _ headD_false_poly
    (cpt_cons1 true hbr2_body) (cpt_cons1 false hbr2_body)
  have hrc_hd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    outRemCut (fun l => l.headD false) hrc headD_false_poly
  exact PvsNP.Units.m2_ite_polytime _ _ _ hrc_hd hbr1 hbr2

-- ============================================================
-- Full verifier on (x, cert) where cert = pairB cut wStack
-- ============================================================

private def checkS (V : List Bool × List Bool → Bool) (s : List Bool) : Bool :=
  let x := (unpairB s).1
  let cert := (unpairB s).2
  let cut := (unpairB cert).1
  let ws := (unpairB cert).2
  decide (cut.length = (true :: x).length) &&
    cut.headD false &&
    !(cut.reverse.headD false) &&
    ((outStep V)^[x.length] (true :: pairB (pairB cut x) ws)).headD false

private def verif (V : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  checkS V (pairB p.1 p.2)

private theorem verif_poly (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verif V) := by
  have hx := cpt_unpairB1
  have hcert := cpt_unpairB2
  have hcut := cpt_unpairB1_1 hcert
  have hws := cpt_unpairB2_1 hcert
  have hc1 := len_eq_poly hcut (cpt_cons1 true hx)
  have hc2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    _ (fun l => l.headD false) hcut headD_false_poly
  have hcut_rev := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ List.reverse hcut PvsNP.Units.m2_reverse_polytime
  have hcut_last := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    _ (fun l => l.headD false) hcut_rev headD_false_poly
  have hc3 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeAnswer PvsNP.encodeAnswer
    _ (fun b => !b) hcut_last bool_not_poly
  obtain ⟨cout⟩ := outStep_poly V hV
  have hiter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun p : List Bool × List Bool => (outStep V)^[p.2.length] p.1) :=
    Iter.iter_polyTime (outStep V) cout 6 (outStep_len V)
  have hinit := cpt_cons1 true (cpt_pairB2 (cpt_pairB2 hcut hx) hws)
  have hrun := PvsNP.Units.m2_polytime_comp PvsNP.encodeString
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
    _ _ (cpt_pair hinit hx) hiter
  have hc4 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    _ (fun l => l.headD false) hrun headD_false_poly
  have hcheck : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (checkS V) :=
    bool_and_poly (bool_and_poly (bool_and_poly hc1 hc2) hc3) hc4
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    rw [← encodePair_eq]
    exact cpt_pairB
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
    (fun p => pairB p.1 p.2) (checkS V) hpb hcheck

-- ============================================================
-- Soundness of inner & outer loops
-- ============================================================

private theorem inStep_iter_sound (V : List Bool × List Bool → Bool)
    (L : Language Bool)
    (hVsound : ∀ u w : List Bool, V (u, w) = true → u ∉ L) :
    ∀ (rx cc cp ws : List Bool) (ok : Bool),
      ((inStep V)^[rx.length] (ok :: pairB (pairB (pairB cc cp) rx) ws)).headD false = true →
        ok = true ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ rx.length →
          (cc.drop (k - 1)).headD false = false →
          cp ++ rx.take k ∉ L := by
  intro rx
  induction rx with
  | nil =>
    intro cc cp ws ok h
    simp only [List.length_nil, Function.iterate_zero, id, List.headD_cons] at h
    exact ⟨h, fun k hk1 hk2 => by simp at hk2; omega⟩
  | cons c rx ih =>
    intro cc cp ws ok h
    rw [List.length_cons, Function.iterate_succ_apply, inStep_eq] at h
    by_cases hcc : cc.headD false = true
    · rw [if_pos hcc] at h
      obtain ⟨hok, hrest⟩ := ih cc.tail (cp ++ [c]) ws ok h
      refine ⟨hok, fun k hk1 hk2 hcut => ?_⟩
      cases k with
      | zero => omega
      | succ k' =>
        cases k' with
        | zero =>
          simp only [Nat.sub_self, List.drop_zero] at hcut
          rw [hcc] at hcut
          exact Bool.noConfusion hcut
        | succ m =>
          have h1 := hrest (m + 1) (by omega) (by simp at hk2; omega) (by simpa using hcut)
          simpa [List.append_assoc] using h1
    · rw [if_neg hcc] at h
      obtain ⟨hand, hrest⟩ := ih cc.tail (cp ++ [c]) (unpairB ws).2
        (ok && V (cp ++ [c], (unpairB ws).1)) h
      rw [Bool.and_eq_true] at hand
      refine ⟨hand.1, fun k hk1 hk2 hcut => ?_⟩
      cases k with
      | zero => omega
      | succ k' =>
        cases k' with
        | zero =>
          simpa using hVsound (cp ++ [c]) (unpairB ws).1 hand.2
        | succ m =>
          have h1 := hrest (m + 1) (by omega) (by simp at hk2; omega) (by simpa using hcut)
          simpa [List.append_assoc] using h1

private theorem outStep_iter_sound (V : List Bool × List Bool → Bool)
    (L : Language Bool)
    (hVsound : ∀ u w : List Bool, V (u, w) = true → u ∉ L) :
    ∀ (rx rc ws : List Bool) (ok : Bool),
      ((outStep V)^[rx.length] (ok :: pairB (pairB rc rx) ws)).headD false = true →
        ok = true ∧
        ∀ i j : ℕ, i < j → j ≤ rx.length →
          (rc.drop i).headD false = true →
          (rc.drop j).headD false = false →
          (rx.drop i).take (j - i) ∉ L := by
  intro rx
  induction rx with
  | nil =>
    intro rc ws ok h
    simp only [List.length_nil, Function.iterate_zero, id, List.headD_cons] at h
    exact ⟨h, fun i j hij hj => by simp at hj; omega⟩
  | cons c rx ih =>
    intro rc ws ok h
    rw [List.length_cons, Function.iterate_succ_apply] at h
    have hout : outStep V (ok :: pairB (pairB rc (c :: rx)) ws) =
        if rc.headD false = true then
          let r := (inStep V)^[(c :: rx).length]
            (ok :: pairB (pairB (pairB rc.tail []) (c :: rx)) ws)
          r.headD false :: pairB (pairB rc.tail rx) (unpairB r.tail).2
        else
          ok :: pairB (pairB rc.tail rx) ws := by
      unfold outStep runInner outRemCut outRemX outWStack
      simp only [List.headD_cons, List.tail_cons, unpairB_pairB]
      cases hrc : rc.headD false <;> cases ok <;>
        cases hr : ((inStep V)^[(c :: rx).length]
          (_ :: pairB (pairB (pairB rc.tail []) (c :: rx)) ws)).headD false <;>
        simp [hrc, hr]
    rw [hout] at h
    by_cases hrc : rc.headD false = true
    · rw [if_pos hrc] at h
      set r := (inStep V)^[(c :: rx).length]
        (ok :: pairB (pairB (pairB rc.tail []) (c :: rx)) ws)
      obtain ⟨hr_ok, hrest⟩ := ih rc.tail (unpairB r.tail).2 (r.headD false) h
      obtain ⟨hok, hcur⟩ := inStep_iter_sound V L hVsound (c :: rx) rc.tail [] ws ok hr_ok
      refine ⟨hok, fun i j hij hj hi_t hj_f => ?_⟩
      cases i with
      | zero =>
        have h1 := hcur j (by omega) (by simpa using hj) (by
          cases j with
          | zero => omega
          | succ j' => simpa using hj_f)
        simpa using h1
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have h1 := hrest i' j' (by omega) (by simpa using hj)
            (by simpa using hi_t)
            (by simpa using hj_f)
          simpa [Nat.succ_sub_succ] using h1
    · rw [if_neg hrc] at h
      obtain ⟨hok, hrest⟩ := ih rc.tail ws ok h
      refine ⟨hok, fun i j hij hj hi_t hj_f => ?_⟩
      cases i with
      | zero =>
        simp only [List.drop_zero] at hi_t
        rw [hi_t] at hrc
        exact absurd rfl hrc
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have h1 := hrest i' j' (by omega) (by simpa using hj)
            (by simpa using hi_t)
            (by simpa using hj_f)
          simpa [Nat.succ_sub_succ] using h1

-- ============================================================
-- Completeness: build wStack for valid cut & bound its length
-- ============================================================

private theorem eval_poly_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add ihp ihq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

private theorem inStep_iter_complete (V : List Bool × List Bool → Bool)
    (L : Language Bool) (p : Polynomial ℕ)
    (hVcomp : ∀ u : List Bool, u ∉ L → ∃ w : List Bool, w.length ≤ p.eval u.length ∧ V (u, w) = true) :
    ∀ (rx cc cp ws_tail : List Bool) (n : ℕ),
      cp.length + rx.length ≤ n →
      (∀ k : ℕ, 1 ≤ k → k ≤ rx.length → (cc.drop (k - 1)).headD false = false → cp ++ rx.take k ∉ L) →
      ∃ ws_head : List Bool,
        ws_head.length ≤ rx.length * (2 * p.eval n + 1) + ws_tail.length ∧
        (inStep V)^[rx.length] (true :: pairB (pairB (pairB cc cp) rx) ws_head) =
          true :: pairB (pairB (pairB (cc.drop rx.length) (cp ++ rx)) []) ws_tail := by
  intro rx
  induction rx with
  | nil =>
    intro cc cp ws_tail n _ _
    exact ⟨ws_tail, by simp, by simp⟩
  | cons c rx ih =>
    intro cc cp ws_tail n hlen hcut
    have hrest_cut : ∀ k : ℕ, 1 ≤ k → k ≤ rx.length →
        (cc.tail.drop (k - 1)).headD false = false → (cp ++ [c]) ++ rx.take k ∉ L := by
      intro k hk1 hk2 hc
      have h := hcut (k + 1) (by omega) (by simp; omega) (by
        have hk' : k = (k - 1) + 1 := by omega
        rw [Nat.add_sub_cancel, hk']
        cases cc <;> simpa using hc)
      simpa [List.append_assoc] using h
    obtain ⟨ws_mid, hmid_len, hmid_run⟩ := ih cc.tail (cp ++ [c]) ws_tail n
      (by simp at hlen ⊢; omega) hrest_cut
    by_cases hcc : cc.headD false = true
    · refine ⟨ws_mid, ?_, ?_⟩
      · simp only [List.length_cons]
        have : rx.length * (2 * p.eval n + 1) ≤ (rx.length + 1) * (2 * p.eval n + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · rw [List.length_cons, Function.iterate_succ_apply, inStep_eq, if_pos hcc, hmid_run]
        simp [List.append_assoc]
    · have hcc_f : cc.headD false = false := by cases h : cc.headD false <;> simp_all
      have hnotL : cp ++ [c] ∉ L := by
        have h := hcut 1 le_rfl (by simp) (by simpa using hcc_f)
        simpa using h
      obtain ⟨w, hw_len, hwV⟩ := hVcomp (cp ++ [c]) hnotL
      have hw_le_n : w.length ≤ p.eval n :=
        hw_len.trans (eval_poly_mono p (by simp at hlen ⊢; omega))
      refine ⟨pairB w ws_mid, ?_, ?_⟩
      · rw [pairB_length]
        simp only [List.length_cons, Nat.add_mul, one_mul]
        omega
      · rw [List.length_cons, Function.iterate_succ_apply, inStep_eq, if_neg hcc]
        simp only [unpairB_pairB, Bool.true_and, hwV]
        rw [hmid_run]
        simp [List.append_assoc]

private theorem outStep_iter_complete (V : List Bool × List Bool → Bool)
    (L : Language Bool) (p : Polynomial ℕ)
    (hVcomp : ∀ u : List Bool, u ∉ L → ∃ w : List Bool, w.length ≤ p.eval u.length ∧ V (u, w) = true) :
    ∀ (rx rc : List Bool) (n : ℕ),
      rx.length ≤ n →
      (∀ i j : ℕ, i < j → j ≤ rx.length →
        (rc.drop i).headD false = true →
        (rc.drop j).headD false = false →
        (rx.drop i).take (j - i) ∉ L) →
      ∃ ws : List Bool,
        ws.length ≤ rx.length * n * (2 * p.eval n + 1) ∧
        ((outStep V)^[rx.length] (true :: pairB (pairB rc rx) ws)).headD false = true := by
  intro rx
  induction rx with
  | nil =>
    intro rc n _ _
    exact ⟨[], by simp, by simp⟩
  | cons c rx ih =>
    intro rc n hlen hcut
    have hrest_cut : ∀ i j : ℕ, i < j → j ≤ rx.length →
        (rc.tail.drop i).headD false = true →
        (rc.tail.drop j).headD false = false →
        (rx.drop i).take (j - i) ∉ L := by
      intro i j hij hj hi_t hj_f
      have h := hcut (i + 1) (j + 1) (by omega) (by simp; omega)
        (by simpa using hi_t)
        (by simpa using hj_f)
      simpa [Nat.succ_sub_succ] using h
    obtain ⟨ws_tail, htail_len, htail_run⟩ := ih rc.tail n (by simp at hlen; omega) hrest_cut
    by_cases hrc : rc.headD false = true
    · have hcur_cut : ∀ k : ℕ, 1 ≤ k → k ≤ (c :: rx).length →
          (rc.tail.drop (k - 1)).headD false = false → [] ++ (c :: rx).take k ∉ L := by
        intro k hk1 hk2 hk_f
        have h := hcut 0 k (by omega) hk2 (by simpa using hrc) (by
          cases k with
          | zero => omega
          | succ k' => simpa using hk_f)
        simpa using h
      obtain ⟨ws, hws_len, hws_run⟩ := inStep_iter_complete V L p hVcomp (c :: rx) rc.tail [] ws_tail n
        (by simpa using hlen) hcur_cut
      refine ⟨ws, ?_, ?_⟩
      · have hmul : (c :: rx).length * (2 * p.eval n + 1) ≤ n * (2 * p.eval n + 1) :=
          Nat.mul_le_mul_right _ hlen
        have hstep_le : (rx.length + 1) * n * (2 * p.eval n + 1) =
            rx.length * n * (2 * p.eval n + 1) + n * (2 * p.eval n + 1) := by ring
        simp only [List.length_cons] at hstep_le ⊢
        omega
      · rw [List.length_cons, Function.iterate_succ_apply]
        have hout : outStep V (true :: pairB (pairB rc (c :: rx)) ws) =
            true :: pairB (pairB rc.tail rx) ws_tail := by
          unfold outStep runInner outRemCut outRemX outWStack
          simp only [List.headD_cons, List.tail_cons, unpairB_pairB, hrc, ↓reduceIte]
          rw [hws_run]
          simp [unpairB_pairB]
        rw [hout]
        exact htail_run
    · refine ⟨ws_tail, ?_, ?_⟩
      · have hle : rx.length * n * (2 * p.eval n + 1) ≤ (rx.length + 1) * n * (2 * p.eval n + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
        simpa using hle.trans' htail_len
      · rw [List.length_cons, Function.iterate_succ_apply]
        have hout : outStep V (true :: pairB (pairB rc (c :: rx)) ws_tail) =
            true :: pairB (pairB rc.tail rx) ws_tail := by
          have hrc_f : rc.headD false = false := by cases h : rc.headD false <;> simp_all
          unfold outStep outRemCut outRemX outWStack
          simp only [List.headD_cons, List.tail_cons, unpairB_pairB, hrc_f,
            Bool.false_eq_true, ↓reduceIte]
        rw [hout]
        exact htail_run

-- ============================================================
-- Graph-cut equivalence for `x ∉ KStar.kstar L`
-- ============================================================

private theorem append_mem_kstar {L : Language Bool} {a b : List Bool}
    (ha : a ∈ KStar.kstar L) (hb : b ∈ L) : a ++ b ∈ KStar.kstar L := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 ha
  refine Language.mem_kstar.2 ⟨S ++ [b], by simp, ?_⟩
  intro w hw
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hS w hw
  · exact hb

private theorem take_append_drop_take (x : List Bool) {j m : ℕ} (hj : j ≤ m) :
    x.take j ++ (x.drop j).take (m - j) = x.take m := by
  rw [← List.take_add, Nat.add_sub_of_le hj]

private theorem kstar_take_succ_mem {L : Language Bool} {x : List Bool} {m : ℕ}
    (hm : m + 1 ≤ x.length) (hx : x.take (m + 1) ∈ KStar.kstar L) :
    ∃ j < m + 1, x.take j ∈ KStar.kstar L ∧ (x.drop j).take (m + 1 - j) ∈ L := by
  obtain ⟨S, hflat, hS⟩ := Language.mem_kstar_iff_exists_nonempty.1 hx
  have hSne : S ≠ [] := by
    intro hnil
    subst hnil
    simp only [List.flatten_nil] at hflat
    have hlen := congrArg List.length hflat
    simp only [List.length_take, List.length_nil] at hlen
    omega
  have hsplit : S.dropLast ++ [S.getLast hSne] = S := List.dropLast_append_getLast hSne
  have hlast_mem : S.getLast hSne ∈ S := List.getLast_mem hSne
  have hlast_inL : S.getLast hSne ∈ L := (hS _ hlast_mem).1
  have hlast_ne : S.getLast hSne ≠ [] := (hS _ hlast_mem).2
  have hlast_pos : 0 < (S.getLast hSne).length := List.length_pos_iff.2 hlast_ne
  have hcat : S.dropLast.flatten ++ S.getLast hSne = x.take (m + 1) := by
    calc S.dropLast.flatten ++ S.getLast hSne
        = (S.dropLast ++ [S.getLast hSne]).flatten := by simp
      _ = S.flatten := by rw [hsplit]
      _ = x.take (m + 1) := hflat.symm
  have hlen_sum : S.dropLast.flatten.length + (S.getLast hSne).length = m + 1 := by
    have h := congrArg List.length hcat
    simp only [List.length_append, List.length_take] at h
    omega
  refine ⟨S.dropLast.flatten.length, by omega, ?_, ?_⟩
  · have htake : x.take S.dropLast.flatten.length = S.dropLast.flatten := by
      have h1 := congrArg (List.take S.dropLast.flatten.length) hcat
      rw [List.take_left, List.take_take, Nat.min_eq_left (by omega)] at h1
      exact h1.symm
    rw [htake]
    refine Language.mem_kstar.2 ⟨S.dropLast, rfl, ?_⟩
    intro w hw
    exact (hS w (List.dropLast_subset S hw)).1
  · have hsub : (x.drop S.dropLast.flatten.length).take (m + 1 - S.dropLast.flatten.length) =
        S.getLast hSne := by
      have h1 := congrArg (List.drop S.dropLast.flatten.length) hcat
      rw [List.drop_left, List.drop_take] at h1
      exact h1.symm
    rw [hsub]
    exact hlast_inL

private theorem cut_sound {L : Language Bool} {x cut : List Bool}
    (h0 : cut.headD false = true)
    (hn : (cut.drop x.length).headD false = false)
    (hcut : ∀ i j : ℕ, i < j → j ≤ x.length →
      (cut.drop i).headD false = true →
      (cut.drop j).headD false = false →
      (x.drop i).take (j - i) ∉ L) :
    x ∉ KStar.kstar L := by
  have hreach : ∀ k : ℕ, k ≤ x.length → x.take k ∈ KStar.kstar L →
      (cut.drop k).headD false = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hmem
      cases k with
      | zero => simpa using h0
      | succ m =>
        obtain ⟨j, hj, hj_mem, hsub_L⟩ := kstar_take_succ_mem hk hmem
        have hj_t := ih j hj (by omega) hj_mem
        cases hres : (cut.drop (m + 1)).headD false with
        | true => rfl
        | false => exact absurd hsub_L (hcut j (m + 1) hj hk hj_t hres)
  intro hx
  have h1 := hreach x.length le_rfl (by simpa using hx)
  rw [hn] at h1
  exact Bool.noConfusion h1

private theorem rev_headD_eq_drop {l : List Bool} {n : ℕ} (hlen : l.length = n + 1) :
    l.reverse.headD false = (l.drop n).headD false := by
  have hne : l ≠ [] := by intro h; subst h; simp at hlen
  have hsp : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
  have hdl : l.dropLast.length = n := by simp [hlen]
  set a := l.dropLast
  set b := l.getLast hne
  rw [← hsp, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.headD_cons, ← hdl, List.drop_left, List.headD_cons]

theorem main :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → KStar.kstar L ∈ PvsNP.coNP := by
  intro L hL
  obtain ⟨V, p, ⟨hV, hspec⟩, hbound⟩ := PvsNP.Units.m2_np_verifier_normal Lᶜ hL
  classical
  let q : Polynomial ℕ :=
    Polynomial.X * Polynomial.X * (Polynomial.C 2 * p + 1) +
      Polynomial.C 2 * (Polynomial.X + 1) + 1
  refine ⟨verif V, q, verif_poly V hV, fun x => ?_⟩
  change x ∉ KStar.kstar L ↔ ∃ cert : List Bool, cert.length ≤ q.eval x.length ∧ verif V (x, cert) = true
  constructor
  · intro hnot
    let cut : List Bool := (List.range (x.length + 1)).map (fun i => decide (x.take i ∈ KStar.kstar L))
    have hcut_len : cut.length = x.length + 1 := by simp [cut]
    have hcut_drop : ∀ i ≤ x.length, (cut.drop i).headD false = decide (x.take i ∈ KStar.kstar L) := by
      intro i hi
      have hlt : i < cut.length := by omega
      have hget : (cut.drop i).headD false = cut[i]'hlt := by
        rw [List.drop_eq_getElem_cons hlt, List.headD_cons]
      rw [hget]
      simp [cut]
    have hcut0 : cut.headD false = true := by
      have h := hcut_drop 0 (Nat.zero_le _)
      simpa [Language.nil_mem_kstar] using h
    have hcutN : (cut.drop x.length).headD false = false := by
      rw [hcut_drop x.length le_rfl]
      simp [hnot]
    have hcut_prop : ∀ i j : ℕ, i < j → j ≤ x.length →
        (cut.drop i).headD false = true →
        (cut.drop j).headD false = false →
        (x.drop i).take (j - i) ∉ L := by
      intro i j hij hj hi_t hj_f hmemL
      rw [hcut_drop i (by omega), decide_eq_true_eq] at hi_t
      rw [hcut_drop j hj, decide_eq_false_iff_not] at hj_f
      have := append_mem_kstar hi_t hmemL
      rw [take_append_drop_take x (Nat.le_of_lt hij)] at this
      exact hj_f this
    have hVcomp : ∀ u : List Bool, u ∉ L →
        ∃ w : List Bool, w.length ≤ p.eval u.length ∧ V (u, w) = true :=
      fun u hu => (hspec u).1 hu
    obtain ⟨ws, hws_len, hws_run⟩ := outStep_iter_complete V L p hVcomp x cut x.length le_rfl hcut_prop
    refine ⟨pairB cut ws, ?_, ?_⟩
    · rw [pairB_length, hcut_len]
      simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_one]
      omega
    · unfold verif checkS
      simp only [unpairB_pairB, List.length_cons, hcut_len, decide_true, Bool.true_and,
        hcut0, rev_headD_eq_drop hcut_len, hcutN, Bool.not_false, hws_run]
  · rintro ⟨cert, -, hok⟩
    unfold verif checkS at hok
    simp only [unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq, List.length_cons,
      Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hlen, h0⟩, hlast⟩, hrun⟩ := hok
    have hn : ((unpairB cert).1.drop x.length).headD false = false := by
      rwa [← rev_headD_eq_drop hlen]
    have hVsound : ∀ u w : List Bool, V (u, w) = true → u ∉ L :=
      fun u w hvw => (hspec u).2 ⟨w, hbound u w hvw, hvw⟩
    obtain ⟨-, hcut_prop⟩ := outStep_iter_sound V L hVsound x (unpairB cert).1 (unpairB cert).2 true hrun
    exact cut_sound h0 hn hcut_prop

end PvsNP.Units.tc_closure_star_conp

theorem PvsNP.Units.tc_closure_star_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → KStar.kstar L ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_star_conp.main
