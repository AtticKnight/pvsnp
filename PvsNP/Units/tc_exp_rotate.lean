import Mathlib
import PvsNP.Defs
import CookLevin
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
import PvsNP.Units.tf_fun_rotate
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_padded_test_exp

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_rotate

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
def getCur (s : List Bool) : List Bool := (decPair (getRest s)).1
def getFlag (s : List Bool) : List Bool := (decPair (getRest s)).2
def paddedCur (s : List Bool) : List Bool := getPad s ++ (false :: getCur s)

def rotStep (g : List Bool → Bool) (s : List Bool) : List Bool :=
  encPair (getPad s)
    (encPair ((getCur s).rotate 1) (if g (paddedCur s) = true then [true] else getFlag s))

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

theorem cpt_getCur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getCur :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getRest getPad cpt_getRest cpt_getPad)
    (fun _ => rfl)

theorem cpt_getFlag : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString getFlag :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      getRest getRest cpt_getRest cpt_getRest)
    (fun _ => rfl)

theorem cpt_paddedCur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString paddedCur := by
  have hfcur : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => false :: getCur s) :=
    cpt_congr (cpt_append_fn (PvsNP.Units.m2_const_polytime [false]) cpt_getCur) (fun _ => rfl)
  exact cpt_congr (cpt_append_fn cpt_getPad hfcur) (fun _ => rfl)

theorem cpt_rotStep (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (rotStep g) := by
  have hcond : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => g (paddedCur s)) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
        paddedCur g cpt_paddedCur hg)
      (fun _ => rfl)
  have hflag : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if g (paddedCur s) = true then [true] else getFlag s) :=
    PvsNP.Units.m2_ite_polytime (fun s => g (paddedCur s))
      (fun _ => [true]) getFlag hcond (PvsNP.Units.m2_const_polytime [true]) cpt_getFlag
  have hrot : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (getCur s).rotate 1) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
        getCur (fun x : List Bool => x.rotate 1) cpt_getCur PvsNP.Units.tf_fun_rotate)
      (fun _ => rfl)
  exact cpt_encPair_app cpt_getPad (cpt_encPair_app hrot hflag)

theorem rotStep_length (g : List Bool → Bool) (s : List Bool) :
    (rotStep g s).length ≤ s.length + 3 := by
  have h1 := decPair_len_bound s
  have h2 := decPair_len_bound (getRest s)
  have hflag : (if g (paddedCur s) = true then [true] else getFlag s).length ≤ (getFlag s).length + 1 := by
    split_ifs
    · simp only [List.length_cons, List.length_nil]; omega
    · omega
  rw [rotStep, encPair_length, encPair_length, List.length_rotate]
  change 2 * (decPair s).1.length + 1 +
      (2 * (getCur s).length + 1 + (if g (paddedCur s) = true then [true] else getFlag s).length) ≤
    s.length + 3
  change 2 * (getCur s).length + (getFlag s).length ≤ (decPair s).2.length at h2
  omega

def initPair (p : List Bool × List Bool) : List Bool × List Bool :=
  (encPair (takeWhileTrue p.1) (encPair p.2 []), true :: p.2)

def finalFlag (g : List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  getFlag ((rotStep g)^[(initPair p).2.length] (initPair p).1)

def rotTest (g : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  decide (([true] : List Bool).length ≤ (finalFlag g p).length)

theorem cpt_rotTest (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (rotTest g) := by
  have henc2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => encPair x []) :=
    cpt_encPair_app PvsNP.Units.m2_prod_map_polytime.ident (PvsNP.Units.m2_const_polytime [])
  have hst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => encPair (takeWhileTrue p.1) (encPair p.2 [])) := by
    have hprod := PvsNP.Units.m2_prod_map_polytime takeWhileTrue (fun x : List Bool => encPair x [])
      cpt_takeWhileTrue henc2
    exact cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => (takeWhileTrue p.1, encPair p.2 []))
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
  -- Build initPair via encPair -> string -> pair_build -> pair
  have hstS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => encPair (takeWhileTrue (decPair s).1) (encPair (decPair s).2 [])) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
        decPair (fun p : List Bool × List Bool => encPair (takeWhileTrue p.1) (encPair p.2 []))
        hdecPair hst)
      (fun _ => rfl)
  have hcntS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => true :: (decPair s).2) :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
        decPair (fun p : List Bool × List Bool => true :: p.2)
        hdecPair hcnt)
      (fun _ => rfl)
  have hinitS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s => (encPair (takeWhileTrue (decPair s).1) (encPair (decPair s).2 []), true :: (decPair s).2)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ hstS hcntS
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair initPair :=
    cpt_congr
      (PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodePair
        (fun p : List Bool × List Bool => encPair p.1 p.2) _ hencPair hinitS)
      (fun p => by simp only [Function.comp_apply, decPair_encPair, initPair])
  have hiter := PvsNP.Units.m2_iterate_polytime (rotStep g) 3 (cpt_rotStep g hg) (rotStep_length g)
  have hrun := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    initPair (fun q : List Bool × List Bool => (rotStep g)^[q.2.length] q.1) hinit hiter
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
    (fun p => by simp only [Function.comp_apply, decPair_encPair, rotTest])

theorem rotStep_enc (g : List Bool → Bool) (pad cur flag : List Bool) :
    rotStep g (encPair pad (encPair cur flag)) =
      encPair pad (encPair (cur.rotate 1) (if g (pad ++ false :: cur) = true then [true] else flag)) := by
  simp only [rotStep, paddedCur, getFlag, getCur, getRest, getPad, decPair_encPair]

theorem rot_inv (g : List Bool → Bool) (pad x : List Bool) :
    ∀ t : ℕ, ∃ flag : List Bool,
      (rotStep g)^[t] (encPair pad (encPair x [])) = encPair pad (encPair (x.rotate t) flag) ∧
      (1 ≤ flag.length ↔ ∃ j < t, g (pad ++ false :: x.rotate j) = true)
  | 0 => ⟨[], by simp only [Function.iterate_zero_apply, List.rotate_zero], by
      constructor
      · intro h; simp only [List.length_nil] at h; omega
      · rintro ⟨j, hj, -⟩; omega⟩
  | t + 1 => by
    obtain ⟨flag, hst, hiff⟩ := rot_inv g pad x t
    rw [Function.iterate_succ_apply', hst, rotStep_enc, List.rotate_rotate]
    cases hhit : g (pad ++ false :: x.rotate t)
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

theorem rotTest_iff (g : List Bool → Bool) (N : ℕ) (x : List Bool) :
    rotTest g (List.replicate N true ++ false :: x, x) = true ↔
      ∃ i : ℕ, g (List.replicate N true ++ false :: x.rotate i) = true := by
  have htw : takeWhileTrue (List.replicate N true ++ false :: x) = List.replicate N true :=
    takeWhile_rep_false N x
  obtain ⟨flag, hst, hiff⟩ := rot_inv g (List.replicate N true) x (x.length + 1)
  have hff : finalFlag g (List.replicate N true ++ false :: x, x) = flag := by
    simp only [finalFlag, initPair, htw, List.length_cons, hst, getFlag, getRest, decPair_encPair]
  rw [rotTest, decide_eq_true_iff, hff]
  change 1 ≤ flag.length ↔ _
  rw [hiff]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨i, hi⟩
    rcases Nat.eq_zero_or_pos x.length with hlen0 | hlenpos
    · have hnil : x = [] := List.eq_nil_of_length_eq_zero hlen0
      subst hnil
      refine ⟨0, by decide, ?_⟩
      simp only [List.rotate_nil] at hi ⊢
      exact hi
    · refine ⟨i % x.length, Nat.lt_succ_of_lt (Nat.mod_lt i hlenpos), ?_⟩
      rw [List.rotate_mod]
      exact hi

end PvsNP.Units.tc_exp_rotate

/-- Exponential time is closed under cyclic shift (TM2): pad `L` into P via `m2_upward_padding`,
iterate `tf_fun_rotate` for `|x| + 1` steps via `m2_iterate_polytime` testing each rotation with the
same length-dependent padding prefix, and convert back to EXP via `m2_padded_test_exp`. -/
theorem PvsNP.Units.tc_exp_rotate :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ i : ℕ, x.rotate i ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, hf, htime⟩
  obtain ⟨g, hg, hpad⟩ := PvsNP.Units.m2_upward_padding L k ⟨f, M, hf, htime⟩
  obtain ⟨j, M', hM'⟩ := PvsNP.Units.m2_padded_test_exp k
    (fun x : List Bool => x) (fun x : List Bool => x)
    (PvsNP.Units.tc_exp_rotate.rotTest g)
    PvsNP.Units.m2_prod_map_polytime.ident
    PvsNP.Units.m2_prod_map_polytime.ident
    (PvsNP.Units.tc_exp_rotate.cpt_rotTest g hg)
  refine ⟨j, _, M', fun x => ?_, hM'⟩
  rw [PvsNP.Units.tc_exp_rotate.rotTest_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (hpad _).1 ⟨x.rotate i, hi, ?_⟩⟩
    rw [List.length_rotate]
  · rintro ⟨i, hi⟩
    obtain ⟨y, hy, heq⟩ := (hpad _).2 hi
    have hxy : x.rotate i = y := PvsNP.Units.tc_exp_rotate.rep_false_inj heq
    exact ⟨i, hxy.symm ▸ hy⟩
