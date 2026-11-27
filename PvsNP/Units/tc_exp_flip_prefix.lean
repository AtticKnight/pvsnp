import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tr_rel_val_dvd
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_padded_test_exp

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_flip_prefix

def encPair (u v : List Bool) : List Bool :=
  List.replicate u.length true ++ false :: (u ++ v)

def decPair (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.takeWhile_cons, id_eq, ↓reduceIte, ih]

theorem dropWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.dropWhile_cons, id_eq, ↓reduceIte, ih]

theorem decPair_encPair (u v : List Bool) : decPair (encPair u v) = (u, v) := by
  simp only [decPair, encPair, takeWhile_rep_false, dropWhile_rep_false, List.tail_cons,
    List.length_replicate, List.take_left, List.drop_left]

theorem rep_false_inj {n m : ℕ} {a b : List Bool}
    (h : List.replicate n true ++ false :: a = List.replicate m true ++ false :: b) : a = b := by
  have hd := congrArg (fun l => (l.dropWhile id).tail) h
  simp only [dropWhile_rep_false, List.tail_cons] at hd
  exact hd

theorem encPair_length (u v : List Bool) :
    (encPair u v).length = 2 * u.length + 1 + v.length := by
  simp only [encPair, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem decPair_len_bound (s : List Bool) :
    2 * (decPair s).1.length + (decPair s).2.length ≤ s.length := by
  simp only [decPair, List.length_take, List.length_drop, List.length_tail]
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : PvsNP.PolyTimeComputable ea eb f) (heq : ∀ x, f x = g x) :
    PvsNP.PolyTimeComputable ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

def takeWhileTrue (s : List Bool) : List Bool := s.takeWhile id

theorem cpt_takeWhileTrue :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString takeWhileTrue :=
  cpt_congr
    (PvsNP.Units.m2_transducer_polytime Bool
      (fun q b => if q && b then (true, some true) else (false, none))
      (fun _ => none)
      (fun q l => if q then l.takeWhile id else [])
      (fun q => by cases q <;> rfl)
      (fun q b l => by cases q <;> cases b <;> rfl)
      true)
    (fun _ => rfl)

private theorem cpt_encPair_app {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => encPair (f s) (g s)) :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (f s, g s))
      (fun p : List Bool × List Bool => List.replicate p.1.length true ++ false :: (p.1 ++ p.2))
      (PvsNP.Units.m2_pair_build_polytime f g hf hg)
      PvsNP.Units.m2_tm_self_delimiting_pair.1)
    (fun _ => rfl)

private theorem cpt_append_fn {f g : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => f s ++ g s) :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (f s, g s))
      (fun p : List Bool × List Bool => p.1 ++ p.2)
      (PvsNP.Units.m2_pair_build_polytime f g hf hg)
      PvsNP.Units.m2_pair_split_polytime.2.2)
    (fun _ => rfl)

def getPad (s : List Bool) : List Bool := (decPair s).1
def getRest (s : List Bool) : List Bool := (decPair s).2
def getMid (s : List Bool) : List Bool := (decPair (getRest s)).1
def getFlag (s : List Bool) : List Bool := (decPair (getRest s)).2
def getSuf (s : List Bool) : List Bool := (decPair (getMid s)).1
def getRev (s : List Bool) : List Bool := (decPair (getMid s)).2
def curCand (s : List Bool) : List Bool := getRev s ++ getSuf s
def paddedCand (s : List Bool) : List Bool := getPad s ++ (false :: curCand s)

def nextMid (s : List Bool) : List Bool :=
  if !(getSuf s).isEmpty = true then
    encPair (getSuf s).tail
      (if (getSuf s).headD false = true then [true] ++ getRev s else [false] ++ getRev s)
  else
    encPair [] (getRev s)

def flipStep (g : List Bool → Bool) (s : List Bool) : List Bool :=
  encPair (getPad s)
    (encPair (nextMid s) (if g (paddedCand s) = true then [true] else getFlag s))

theorem cpt_decPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair :=
  cpt_congr PvsNP.Units.m2_tm_self_delimiting_pair.2 (fun _ => by simp only [decPair])

theorem cpt_getPad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getPad :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      decPair (fun p : List Bool × List Bool => p.1) cpt_decPair PvsNP.Units.m2_pair_split_polytime.1)
    (fun _ => rfl)

theorem cpt_getRest : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getRest :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      decPair (fun p : List Bool × List Bool => p.2) cpt_decPair PvsNP.Units.m2_pair_split_polytime.2.1)
    (fun _ => rfl)

theorem cpt_getMid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getMid :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getRest getPad cpt_getRest cpt_getPad)
    (fun _ => rfl)

theorem cpt_getFlag : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getFlag :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getRest getRest cpt_getRest cpt_getRest)
    (fun _ => rfl)

theorem cpt_getSuf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getSuf :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getMid getPad cpt_getMid cpt_getPad)
    (fun _ => rfl)

theorem cpt_getRev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getRev :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getMid getRest cpt_getMid cpt_getRest)
    (fun _ => rfl)

theorem cpt_paddedCand : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString paddedCand := by
  have hcur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString curCand :=
    cpt_append_fn cpt_getRev cpt_getSuf
  have hfcur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => false :: curCand s) :=
    cpt_congr (cpt_append_fn (PvsNP.Units.m2_const_polytime [false]) hcur) (fun _ => rfl)
  exact cpt_congr (cpt_append_fn cpt_getPad hfcur) (fun _ => rfl)

theorem cpt_nextMid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString nextMid := by
  have hne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    getSuf (fun x => !x.isEmpty) cpt_getSuf PvsNP.Units.tr_rel_val_dvd.nonempty_poly
  have hhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    getSuf (fun x => x.headD false) cpt_getSuf PvsNP.Units.tr_rel_val_dvd.headD_false_poly
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (getSuf s).tail) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1 cpt_getSuf
  have hrevNext := PvsNP.Units.m2_ite_polytime _ _ _ hhd
    (cpt_append_fn (PvsNP.Units.m2_const_polytime [true]) cpt_getRev)
    (cpt_append_fn (PvsNP.Units.m2_const_polytime [false]) cpt_getRev)
  have hpos := cpt_encPair_app htail hrevNext
  have hnil := cpt_encPair_app (PvsNP.Units.m2_const_polytime []) cpt_getRev
  exact PvsNP.Units.m2_ite_polytime _ _ _ hne hpos hnil

theorem cpt_flipStep (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (flipStep g) := by
  have hcond : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => g (paddedCand s)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
        paddedCand g cpt_paddedCand hg)
      (fun _ => rfl)
  have hflag : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if g (paddedCand s) = true then [true] else getFlag s) :=
    PvsNP.Units.m2_ite_polytime (fun s => g (paddedCand s))
      (fun _ => [true]) getFlag hcond (PvsNP.Units.m2_const_polytime [true]) cpt_getFlag
  exact cpt_encPair_app cpt_getPad (cpt_encPair_app cpt_nextMid hflag)

theorem flipStep_length (g : List Bool → Bool) (s : List Bool) :
    (flipStep g s).length ≤ s.length + 5 := by
  have h1 := decPair_len_bound s
  have h2 := decPair_len_bound (getRest s)
  have h3 := decPair_len_bound (getMid s)
  have hmid : (nextMid s).length ≤ (getMid s).length + 1 := by
    unfold nextMid
    split_ifs with hne hhd
    · have hpos : 0 < (getSuf s).length := by
        cases h : getSuf s with
        | nil => simp [h] at hne
        | cons _ _ => simp
      rw [encPair_length]
      simp only [List.length_tail, List.length_append, List.length_singleton]
      change 2 * (getSuf s).length + (getRev s).length ≤ (getMid s).length at h3
      omega
    · have hpos : 0 < (getSuf s).length := by
        cases h : getSuf s with
        | nil => simp [h] at hne
        | cons _ _ => simp
      rw [encPair_length]
      simp only [List.length_tail, List.length_append, List.length_singleton]
      change 2 * (getSuf s).length + (getRev s).length ≤ (getMid s).length at h3
      omega
    · rw [encPair_length]
      simp only [List.length_nil]
      change 2 * (getSuf s).length + (getRev s).length ≤ (getMid s).length at h3
      omega
  have hflag : (if g (paddedCand s) = true then [true] else getFlag s).length ≤ (getFlag s).length + 1 := by
    split_ifs
    · simp only [List.length_cons, List.length_nil]; omega
    · omega
  rw [flipStep, encPair_length, encPair_length]
  change 2 * (decPair s).1.length + 1 +
      (2 * (nextMid s).length + 1 + (if g (paddedCand s) = true then [true] else getFlag s).length) ≤
    s.length + 5
  change 2 * (getMid s).length + (getFlag s).length ≤ (decPair s).2.length at h2
  omega

def initPair (p : List Bool × List Bool) : List Bool × List Bool :=
  (encPair (takeWhileTrue p.1) (encPair (encPair p.2 []) []), true :: p.2)

def finalFlag (g : List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  getFlag ((flipStep g)^[(initPair p).2.length] (initPair p).1)

def flipTest (g : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide (([true] : List Bool).length ≤ (finalFlag g p).length)

theorem cpt_flipTest (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (flipTest g) := by
  have henc1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => encPair x []) :=
    cpt_encPair_app PvsNP.Units.m2_prod_map_polytime.ident (PvsNP.Units.m2_const_polytime [])
  have henc2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => encPair (encPair x []) []) :=
    cpt_encPair_app henc1 (PvsNP.Units.m2_const_polytime [])
  have hst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => encPair (takeWhileTrue p.1) (encPair (encPair p.2 []) [])) := by
    have hprod := PvsNP.Units.m2_prod_map_polytime takeWhileTrue
      (fun x : List Bool => encPair (encPair x []) []) cpt_takeWhileTrue henc2
    exact cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => (takeWhileTrue p.1, encPair (encPair p.2 []) []))
        (fun p : List Bool × List Bool => List.replicate p.1.length true ++ false :: (p.1 ++ p.2))
        hprod PvsNP.Units.m2_tm_self_delimiting_pair.1)
      (fun _ => rfl)
  have htx : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => true :: x) :=
    cpt_congr (cpt_append_fn (PvsNP.Units.m2_const_polytime [true]) PvsNP.Units.m2_prod_map_polytime.ident) (fun _ => rfl)
  have hcnt : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => true :: p.2) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
        (fun p : List Bool × List Bool => p.2) (fun x : List Bool => true :: x)
        PvsNP.Units.m2_pair_split_polytime.2.1 htx)
      (fun _ => rfl)
  have hdecPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair := cpt_decPair
  have hencPair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => encPair p.1 p.2) :=
    cpt_congr PvsNP.Units.m2_tm_self_delimiting_pair.1 (fun _ => rfl)
  have hstS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => encPair (takeWhileTrue (decPair s).1) (encPair (encPair (decPair s).2 []) [])) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
        decPair _ hdecPair hst)
      (fun _ => rfl)
  have hcntS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => true :: (decPair s).2) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
        decPair _ hdecPair hcnt)
      (fun _ => rfl)
  have hinitS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => (encPair (takeWhileTrue (decPair s).1) (encPair (encPair (decPair s).2 []) []), true :: (decPair s).2)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ hstS hcntS
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair initPair :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodePair
        (fun p : List Bool × List Bool => encPair p.1 p.2) _ hencPair hinitS)
      (fun p => by simp only [Function.comp_apply, decPair_encPair, initPair])
  have hiter := PvsNP.Units.m2_iterate_polytime (flipStep g) 5 (cpt_flipStep g hg) (flipStep_length g)
  have hrun := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    initPair (fun q : List Bool × List Bool => (flipStep g)^[q.2.length] q.1) hinit hiter
  have hff : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (finalFlag g) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
        _ getFlag hrun cpt_getFlag)
      (fun _ => rfl)
  have hffS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => finalFlag g (decPair s)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
        decPair (finalFlag g) hdecPair hff)
      (fun _ => rfl)
  have hlenPairS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => ([true], finalFlag g (decPair s))) :=
    PvsNP.Units.m2_pair_build_polytime (fun _ : List Bool => [true]) _
      (PvsNP.Units.m2_const_polytime [true]) hffS
  have hlenS := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    _ (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length))
    hlenPairS PvsNP.Units.m2_len_le_polytime
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => encPair p.1 p.2) _ hencPair hlenS)
    (fun p => by simp only [Function.comp_apply, decPair_encPair, flipTest])

theorem nextMid_take_drop (x : List Bool) (t : ℕ) (pad flag : List Bool) :
    nextMid (encPair pad (encPair (encPair (x.drop t) (x.take t).reverse) flag)) =
      encPair (x.drop (t + 1)) (x.take (t + 1)).reverse := by
  by_cases hlt : t < x.length
  · have hdrop : x.drop t = x[t] :: x.drop (t + 1) := List.drop_eq_getElem_cons hlt
    have htake : (x.take (t + 1)).reverse = x[t] :: (x.take t).reverse := by
      rw [List.take_succ_eq_append_getElem hlt, List.reverse_append]
      rfl
    unfold nextMid
    simp only [getSuf, getRev, getMid, getRest, decPair_encPair, hdrop, htake]
    cases x[t] <;> simp
  · have hge : x.length ≤ t := Nat.le_of_not_lt hlt
    have hd1 : x.drop t = [] := List.drop_eq_nil_of_le hge
    have hd2 : x.drop (t + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have ht1 : x.take t = x := List.take_of_length_le hge
    have ht2 : x.take (t + 1) = x := List.take_of_length_le (by omega)
    unfold nextMid
    simp only [getSuf, getRev, getMid, getRest, decPair_encPair, hd1, hd2, ht1, ht2]
    rfl

theorem flipStep_enc (g : List Bool → Bool) (pad x : List Bool) (t : ℕ) (flag : List Bool) :
    flipStep g (encPair pad (encPair (encPair (x.drop t) (x.take t).reverse) flag)) =
      encPair pad (encPair (encPair (x.drop (t + 1)) (x.take (t + 1)).reverse)
        (if g (pad ++ false :: ((x.take t).reverse ++ x.drop t)) = true then [true] else flag)) := by
  unfold flipStep
  rw [nextMid_take_drop]
  simp only [paddedCand, curCand, getFlag, getSuf, getRev, getMid, getRest, getPad, decPair_encPair]

theorem flip_inv (g : List Bool → Bool) (pad x : List Bool) :
    ∀ t : ℕ, ∃ flag : List Bool,
      (flipStep g)^[t] (encPair pad (encPair (encPair x []) [])) =
        encPair pad (encPair (encPair (x.drop t) (x.take t).reverse) flag) ∧
      (1 ≤ flag.length ↔ ∃ j < t, g (pad ++ false :: ((x.take j).reverse ++ x.drop j)) = true)
  | 0 => ⟨[], by simp only [Function.iterate_zero_apply, List.drop_zero, List.take_zero, List.reverse_nil], by
      constructor
      · intro h; simp only [List.length_nil] at h; omega
      · rintro ⟨j, hj, -⟩; omega⟩
  | t + 1 => by
    obtain ⟨flag, hst, hiff⟩ := flip_inv g pad x t
    rw [Function.iterate_succ_apply', hst, flipStep_enc]
    cases hhit : g (pad ++ false :: ((x.take t).reverse ++ x.drop t))
    · refine ⟨flag, rfl, ?_⟩
      rw [hiff]
      constructor
      · rintro ⟨j, hj, hgj⟩; exact ⟨j, Nat.lt_succ_of_lt hj, hgj⟩
      · rintro ⟨j, hj, hgj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
        · exact ⟨j, hlt, hgj⟩
        · rw [hhit] at hgj; exact False.elim (Bool.false_ne_true hgj)
    · refine ⟨[true], rfl, ?_⟩
      constructor
      · intro _; exact ⟨t, Nat.lt_succ_self t, hhit⟩
      · intro _; exact le_refl 1

theorem flipTest_iff (g : List Bool → Bool) (N : ℕ) (x : List Bool) :
    flipTest g (List.replicate N true ++ false :: x, x) = true ↔
      ∃ i : ℕ, g (List.replicate N true ++ false :: ((x.take i).reverse ++ x.drop i)) = true := by
  have htw : takeWhileTrue (List.replicate N true ++ false :: x) = List.replicate N true :=
    takeWhile_rep_false N x
  obtain ⟨flag, hst, hiff⟩ := flip_inv g (List.replicate N true) x (x.length + 1)
  have hff : finalFlag g (List.replicate N true ++ false :: x, x) = flag := by
    simp only [finalFlag, initPair, htw, List.length_cons, hst, getFlag, getRest, decPair_encPair]
  rw [flipTest, decide_eq_true_iff, hff]
  change 1 ≤ flag.length ↔ _
  rw [hiff]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨i, hi⟩
    by_cases hle : i ≤ x.length
    · exact ⟨i, Nat.lt_succ_of_le hle, hi⟩
    · have hgt : x.length ≤ i := Nat.le_of_not_le hle
      refine ⟨x.length, Nat.lt_succ_self x.length, ?_⟩
      rw [List.take_of_length_le hgt, List.drop_eq_nil_of_le hgt] at hi
      simpa only [List.take_length, List.drop_length] using hi

end PvsNP.Units.tc_exp_flip_prefix

theorem PvsNP.Units.tc_exp_flip_prefix :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, htime⟩
  obtain ⟨g, hg, hpad⟩ := PvsNP.Units.m2_upward_padding L k ⟨f, M, hf, htime⟩
  obtain ⟨j, M', hM'⟩ := PvsNP.Units.m2_padded_test_exp k
    (fun x : List Bool => x) (fun x : List Bool => x)
    (PvsNP.Units.tc_exp_flip_prefix.flipTest g)
    PvsNP.Units.m2_prod_map_polytime.ident
    PvsNP.Units.m2_prod_map_polytime.ident
    (PvsNP.Units.tc_exp_flip_prefix.cpt_flipTest g hg)
  refine ⟨j, _, M', fun x => ?_, hM'⟩
  rw [PvsNP.Units.tc_exp_flip_prefix.flipTest_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (hpad _).1 ⟨(x.take i).reverse ++ x.drop i, hi, ?_⟩⟩
    have hlen : ((x.take i).reverse ++ x.drop i).length = x.length := by
      simp only [List.length_append, List.length_reverse, List.length_take, List.length_drop]
      omega
    rw [hlen]
  · rintro ⟨i, hi⟩
    obtain ⟨y, hy, heq⟩ := (hpad _).2 hi
    have hxy : (x.take i).reverse ++ x.drop i = y := PvsNP.Units.tc_exp_flip_prefix.rep_false_inj heq
    exact ⟨i, hxy.symm ▸ hy⟩
