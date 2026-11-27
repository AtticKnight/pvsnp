import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_transducer_polytime

/-
Proof of m2_tm_sync_transducer, following the settled unit m2_zip_bne_polytime:
interleave the pair with an iterated one-step function (pairB-encoded state),
then run a one-string transducer with states Q × Option Bool (settled
m2_transducer_polytime), composed by the settled m2_polytime_comp.
-/

namespace PvsNP.Units.m2_tm_sync_transducer

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

private theorem nonempty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => !x.isEmpty) := by
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p Bool (fun _ _ => true) false id
  have hfold_true : ∀ y : List Bool, y.foldl (fun _ _ => true) true = true := by
    intro y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => !x.isEmpty := by
    funext x
    have hx := hdec x
    change id (x.foldl (fun _ _ => true) false) = true ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, id, List.isEmpty_nil, Bool.not_true] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, hfold_true, id, List.isEmpty_cons, Bool.not_false] at hx ⊢
      exact hx.1 trivial
  rwa [← heq]

private theorem headD_false_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y; induction y with | nil => rfl | cons _ _ ih => exact ih
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

private def sA (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
private def sB (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
private def sAcc (s : List Bool) : List Bool := (unpairB s).2

/-- One interleave step: move the heads of the two remaining lists onto the
accumulator, or stay put when either list is empty. -/
private def iStep (s : List Bool) : List Bool :=
  if !(sA s).isEmpty = true then
    if !(sB s).isEmpty = true then
      if (sA s).headD false = true then
        if (sB s).headD false = true then
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [true, true])
        else
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [true, false])
      else
        if (sB s).headD false = true then
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [false, true])
        else
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [false, false])
    else
      pairB (pairB (sA s) (sB s)) (sAcc s)
  else
    pairB (pairB (sA s) (sB s)) (sAcc s)

private theorem iStep_len (s : List Bool) : (iStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_len_bound s
  have h2 := unpairB_len_bound (unpairB s).1
  have ha : (sA s).tail.length ≤ (sA s).length := by simp
  have hb : (sB s).tail.length ≤ (sB s).length := by simp
  have hbound : 4 * (sA s).length + 2 * (sB s).length + (sAcc s).length ≤ s.length := by
    unfold sA sB sAcc; omega
  unfold iStep
  split_ifs <;> simp only [pairB_length, List.length_append, List.length_cons,
    List.length_nil] <;> omega

private theorem iStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString iStep := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sA :=
    cpt_unpairB1_1 cpt_unpairB1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sB :=
    cpt_unpairB2_1 cpt_unpairB1
  have hAcc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sAcc :=
    cpt_unpairB2
  have hAne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sA (fun x => !x.isEmpty) hA nonempty_poly
  have hBne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sB (fun x => !x.isEmpty) hB nonempty_poly
  have hAhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sA (fun x => x.headD false) hA headD_false_poly
  have hBhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sB (fun x => x.headD false) hB headD_false_poly
  have hpairT := cpt_pairB2 (cpt_tail1 hA) (cpt_tail1 hB)
  have hpushTT := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [true, true]))
  have hpushTF := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [true, false]))
  have hpushFT := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [false, true]))
  have hpushFF := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [false, false]))
  have hstay := cpt_pairB2 (cpt_pairB2 hA hB) hAcc
  have h1 := PvsNP.Units.m2_ite_polytime _ _ _ hBhd hpushTT hpushTF
  have h2 := PvsNP.Units.m2_ite_polytime _ _ _ hBhd hpushFT hpushFF
  have h3 := PvsNP.Units.m2_ite_polytime _ _ _ hAhd h1 h2
  have h4 := PvsNP.Units.m2_ite_polytime _ _ _ hBne h3 hstay
  exact PvsNP.Units.m2_ite_polytime _ _ _ hAne h4 hstay

private theorem iStep_stay_nil_right (m : ℕ) (a acc : List Bool) :
    (unpairB (iStep^[m] (pairB (pairB a []) acc))).2 = acc := by
  induction m generalizing a acc with
  | zero => simp [unpairB_pairB]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hs : iStep (pairB (pairB a []) acc) = pairB (pairB a []) acc := by
      unfold iStep sA sB sAcc
      cases a <;> simp [unpairB_pairB]
    rw [hs]
    exact ih a acc

private theorem iStep_iter (a b acc : List Bool) :
    (unpairB (iStep^[a.length] (pairB (pairB a b) acc))).2 =
      acc ++ (List.zipWith (fun x y : Bool => [x, y]) a b).flatten := by
  induction a generalizing b acc with
  | nil =>
    simp [unpairB_pairB]
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [List.zipWith_nil_right, List.flatten_nil, List.append_nil]
      exact iStep_stay_nil_right (x :: a).length (x :: a) acc
    | cons y b =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hs : iStep (pairB (pairB (x :: a) (y :: b)) acc) =
          pairB (pairB a b) (acc ++ [x, y]) := by
        unfold iStep sA sB sAcc
        simp only [unpairB_pairB, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
          List.headD_cons, List.tail_cons]
        cases x <;> cases y <;> rfl
      rw [hs, ih b (acc ++ [x, y])]
      simp [List.append_assoc]

/-- Interleaving two lists is polynomial-time computable. -/
private theorem zip_interleave :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (List.zipWith (fun x y : Bool => [x, y]) p.1 p.2).flatten) := by
  obtain ⟨cz⟩ := iStep_poly
  have hiter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun p : List Bool × List Bool => iStep^[p.2.length] p.1) :=
    Iter.iter_polyTime iStep cz 5 iStep_len
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    rw [← encodePair_eq]
    exact cpt_pairB
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => pairB s []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hrunS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB (iStep^[(unpairB s).1.length] (pairB s []))).2) :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit cpt_unpairB1) hiter)
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => pairB p.1 p.2)
    (fun s : List Bool => (unpairB (iStep^[(unpairB s).1.length] (pairB s []))).2) hpb hrunS
  have heq :
      ((fun s : List Bool => (unpairB (iStep^[(unpairB s).1.length] (pairB s []))).2) ∘
        (fun p : List Bool × List Bool => pairB p.1 p.2)) =
      (fun p : List Bool × List Bool =>
        (List.zipWith (fun x y : Bool => [x, y]) p.1 p.2).flatten) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB]
    have h := iStep_iter a b []
    simpa using h
  rwa [heq] at hcomp

/-- The one-string transducer over the interleaved list: states `Q × Option Bool`
hold the first bit of each pair until the second bit arrives. -/
private def delta' {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool) :
    (Q × Option Bool) → Bool → (Q × Option Bool) × Option Bool
  | (q, none), b => ((q, some b), none)
  | (q, some a), b => (((δ q a b).1, none), (δ q a b).2)

private def fin' {Q : Type} : (Q × Option Bool) → Option Bool := fun _ => none

private theorem delta'_none {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool)
    (q : Q) (b : Bool) :
    delta' δ (q, none) b = ((q, some b), none) := rfl

private theorem delta'_some {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool)
    (q : Q) (a b : Bool) :
    delta' δ (q, some a) b = (((δ q a b).1, none), (δ q a b).2) := rfl

/-- The transducer run on the interleaved list equals the two-string function. -/
private theorem fstRun_interleave {Q : Type} [Fintype Q]
    (δ : Q → Bool → Bool → Q × Option Bool)
    (F : Q → List Bool → List Bool → List Bool)
    (h0 : ∀ (q : Q) (y : List Bool), F q [] y = [])
    (h1 : ∀ (q : Q) (a : Bool) (x : List Bool), F q (a :: x) [] = [])
    (h2 : ∀ (q : Q) (a b : Bool) (x y : List Bool),
      F q (a :: x) (b :: y) = (δ q a b).2.toList ++ F (δ q a b).1 x y)
    (x y : List Bool) (q : Q) :
    fstRun (delta' δ) fin' (q, none)
        ((List.zipWith (fun a b : Bool => [a, b]) x y).flatten) = F q x y := by
  induction x generalizing y q with
  | nil =>
    cases y with
    | nil => simp [h0, fstRun, fin']
    | cons b y => simp [h0, fstRun, fin']
  | cons a x ih =>
    cases y with
    | nil => simp [h1, fstRun, fin']
    | cons b y =>
      have hstep : fstRun (delta' δ) fin' (q, none)
          ((List.zipWith (fun a b : Bool => [a, b]) (a :: x) (b :: y)).flatten)
          = (δ q a b).2.toList ++
            fstRun (delta' δ) fin' ((δ q a b).1, none)
              ((List.zipWith (fun a b : Bool => [a, b]) x y).flatten) := by
        simp [List.zipWith_cons_cons, List.flatten_cons, fstRun, delta'_none,
          delta'_some, fin']
      rw [hstep, ih y (δ q a b).1, ← h2 q a b x y]

end PvsNP.Units.m2_tm_sync_transducer

theorem PvsNP.Units.m2_tm_sync_transducer :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool → Bool → Q × Option Bool)
      (F : Q → List Bool → List Bool → List Bool),
      (∀ (q : Q) (y : List Bool), F q [] y = []) →
      (∀ (q : Q) (a : Bool) (x : List Bool), F q (a :: x) [] = []) →
      (∀ (q : Q) (a b : Bool) (x y : List Bool),
        F q (a :: x) (b :: y) = (δ q a b).2.toList ++ F (δ q a b).1 x y) →
      ∀ q₀ : Q, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => F q₀ p.1 p.2) := by
  intro Q _ δ F h0 h1 h2 q₀
  have hTrans : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun l : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun
          (PvsNP.Units.m2_tm_sync_transducer.delta' δ)
          PvsNP.Units.m2_tm_sync_transducer.fin' (q₀, none) l) := by
    apply PvsNP.Units.m2_transducer_polytime (Q × Option Bool)
      (PvsNP.Units.m2_tm_sync_transducer.delta' δ)
      PvsNP.Units.m2_tm_sync_transducer.fin'
      (fun s l => PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun
        (PvsNP.Units.m2_tm_sync_transducer.delta' δ)
        PvsNP.Units.m2_tm_sync_transducer.fin' s l)
    · intro s
      simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
    · intro s b x
      simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun]
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
    PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      (List.zipWith (fun x y : Bool => [x, y]) p.1 p.2).flatten)
    (fun l : List Bool =>
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun
        (PvsNP.Units.m2_tm_sync_transducer.delta' δ)
        PvsNP.Units.m2_tm_sync_transducer.fin' (q₀, none) l)
    PvsNP.Units.m2_tm_sync_transducer.zip_interleave hTrans
  have heq : ((fun l : List Bool =>
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun
        (PvsNP.Units.m2_tm_sync_transducer.delta' δ)
        PvsNP.Units.m2_tm_sync_transducer.fin' (q₀, none) l) ∘
      (fun p : List Bool × List Bool =>
        (List.zipWith (fun x y : Bool => [x, y]) p.1 p.2).flatten)) =
      (fun p : List Bool × List Bool => F q₀ p.1 p.2) := by
    funext ⟨x, y⟩
    simp only [Function.comp_apply]
    exact PvsNP.Units.m2_tm_sync_transducer.fstRun_interleave δ F h0 h1 h2 x y q₀
  rwa [heq] at hcomp
