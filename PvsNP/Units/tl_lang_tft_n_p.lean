import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tl_lang_tft_n_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def thirdδ : Fin 3 → Bool → Fin 3 × Option Bool
  | ⟨0, _⟩, _ => (⟨1, by omega⟩, none)
  | ⟨1, _⟩, _ => (⟨2, by omega⟩, none)
  | ⟨2, _⟩, _ => (⟨0, by omega⟩, some true)

def thirdF : Fin 3 → List Bool → List Bool
  | _, [] => []
  | q, b :: xs => (thirdδ q b).2.toList ++ thirdF (thirdδ q b).1 xs

def thirdUnary (x : List Bool) : List Bool := thirdF ⟨0, by omega⟩ x

theorem thirdF_formula (q : Fin 3) (x : List Bool) :
    thirdF q x = List.replicate ((x.length + q.val) / 3) true := by
  induction x generalizing q with
  | nil =>
    have : q.val / 3 = 0 := Nat.div_eq_of_lt q.isLt
    simp [thirdF, this]
  | cons b xs ih =>
    rcases q with ⟨_ | _ | _ | m, hm⟩
    · simp [thirdF, thirdδ, ih]
    · simp [thirdF, thirdδ, ih]
    · have ih0 := ih ⟨0, by omega⟩
      change true :: thirdF ⟨0, by omega⟩ xs =
        List.replicate ((xs.length + 1 + 2) / 3) true
      have : (xs.length + 1 + 2) / 3 = xs.length / 3 + 1 := by omega
      rw [this, ih0, List.replicate_succ]
      simp
    · omega

theorem thirdUnary_eq (x : List Bool) :
    thirdUnary x = List.replicate (x.length / 3) true := by
  simpa [thirdUnary] using thirdF_formula ⟨0, by omega⟩ x

theorem cpt_thirdUnary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString thirdUnary :=
  PvsNP.Units.m2_transducer_polytime (Fin 3) thirdδ (fun _ => none) thirdF
    (fun q => by simp [thirdF])
    (fun q b x => rfl)
    ⟨0, by omega⟩

theorem drop_iterate (k : ℕ) (l : List Bool) :
    l.drop k = List.tail^[k] l := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil =>
      simp only [List.drop_nil]
      have hnil : List.tail^[k] ([] : List Bool) = [] := by
        simpa using (ih []).symm
      rw [Function.iterate_succ_apply', hnil]
      rfl
    | cons _ t => simp [List.drop_succ_cons, ih]

theorem cpt_tail_pow (f cnt : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hcnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString cnt) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => (f x).drop (cnt x).length) := by
  have hiter : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => List.tail^[(cnt s).length] (f s)) :=
    cpt_iterLen cpt_tail (fun s => by cases s <;> simp) hcnt hf
  have heq : (fun s => List.tail^[(cnt s).length] (f s)) =
      (fun s => (f s).drop (cnt s).length) := by
    funext s
    exact (drop_iterate (cnt s).length (f s)).symm
  rwa [heq] at hiter

def dropN (x : List Bool) : List Bool := x.drop (thirdUnary x).length
def twoThirds (x : List Bool) : List Bool := thirdUnary x ++ thirdUnary x
def takeN (x : List Bool) : List Bool :=
  (x.reverse.drop (twoThirds x).length).reverse
/-- The middle block of length `n`, computed as `take n` of `x.drop n`
    via `reverse; drop n; reverse` (valid once `|x| = 3n`). -/
def midN (x : List Bool) : List Bool :=
  ((dropN x).reverse.drop (thirdUnary x).length).reverse
def lastN (x : List Bool) : List Bool := x.drop (twoThirds x).length
def allTrue (u : List Bool) : List Bool := u.map (fun _ => true)
def allFalse (u : List Bool) : List Bool := u.map (fun _ => false)

theorem cpt_dropN :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString dropN :=
  cpt_tail_pow (fun x => x) thirdUnary cpt_id cpt_thirdUnary

theorem cpt_reverse :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.reverse) :=
  PvsNP.Units.m2_reverse_polytime

theorem cpt_twoThirds :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString twoThirds :=
  cpt_app2 cpt_thirdUnary cpt_thirdUnary

theorem cpt_takeN :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString takeN := by
  have hdrop := cpt_tail_pow (fun x => x.reverse) twoThirds cpt_reverse cpt_twoThirds
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x => x.reverse.drop (twoThirds x).length) (fun y => y.reverse) hdrop cpt_reverse

theorem cpt_midN :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString midN := by
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    dropN (fun y => y.reverse) cpt_dropN cpt_reverse
  have hdrop := cpt_tail_pow (fun x => (dropN x).reverse) thirdUnary h1 cpt_thirdUnary
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x => (dropN x).reverse.drop (thirdUnary x).length) (fun y => y.reverse)
    hdrop cpt_reverse

theorem cpt_lastN :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString lastN :=
  cpt_tail_pow (fun x => x) twoThirds cpt_id cpt_twoThirds

theorem cpt_allTrue :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString allTrue :=
  filterMap_polyTime _ _ _ (fun _ : Bool => some true) (fun x => by
    change allTrue x = List.filterMap (fun _ => some true) x
    induction x with
    | nil => rfl
    | cons b xs ih => simp [allTrue, ih])

theorem cpt_allFalse :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString allFalse :=
  filterMap_polyTime _ _ _ (fun _ : Bool => some false) (fun x => by
    change allFalse x = List.filterMap (fun _ => some false) x
    induction x with
    | nil => rfl
    | cons b xs ih => simp [allFalse, ih])

theorem cpt_eq_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => decide (f x = g x)) := by
  have hp : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun x : List Bool => (f x, g x)) := cpt_pair hf hg
  exact cpt_comp hp PvsNP.Units.m2_eq_polytime

def lenOk (x : List Bool) : Bool := decide (allTrue x = twoThirds x ++ thirdUnary x)
def firstOk (x : List Bool) : Bool := decide (takeN x = thirdUnary x)
def midOk (x : List Bool) : Bool := decide (midN x = allFalse (thirdUnary x))
def lastOk (x : List Bool) : Bool := decide (lastN x = thirdUnary x)
def dec (x : List Bool) : Bool := lenOk x && firstOk x && midOk x && lastOk x

theorem cpt_lenOk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer lenOk :=
  cpt_eq_fun allTrue (fun x => twoThirds x ++ thirdUnary x) cpt_allTrue
    (cpt_app2 cpt_twoThirds cpt_thirdUnary)

theorem cpt_firstOk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer firstOk :=
  cpt_eq_fun takeN thirdUnary cpt_takeN cpt_thirdUnary

theorem cpt_midOk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer midOk :=
  cpt_eq_fun midN (fun x => allFalse (thirdUnary x)) cpt_midN
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      thirdUnary allFalse cpt_thirdUnary cpt_allFalse)

theorem cpt_lastOk :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer lastOk :=
  cpt_eq_fun lastN thirdUnary cpt_lastN cpt_thirdUnary

theorem cpt_dec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer dec := by
  have h1 := PvsNP.Units.m2_bool_combine_polytime and lenOk firstOk cpt_lenOk cpt_firstOk
  have h2 := PvsNP.Units.m2_bool_combine_polytime and midOk lastOk cpt_midOk cpt_lastOk
  have h3 := PvsNP.Units.m2_bool_combine_polytime and
    (fun x => lenOk x && firstOk x) (fun x => midOk x && lastOk x) h1 h2
  have heq : (fun x : List Bool => (lenOk x && firstOk x) && (midOk x && lastOk x)) = dec := by
    funext x; simp [dec, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  rwa [heq] at h3

theorem reverse_drop_reverse (l : List Bool) (k : ℕ) :
    (l.reverse.drop k).reverse = l.take (l.length - k) := by
  rw [List.drop_reverse, List.reverse_reverse]

theorem lenOk_length {x : List Bool} (h : lenOk x = true) :
    x.length = 3 * (thirdUnary x).length := by
  have heq : allTrue x = twoThirds x ++ thirdUnary x := of_decide_eq_true h
  have := congrArg List.length heq
  simp [allTrue, twoThirds, List.length_append] at this
  omega

theorem takeN_eq {x : List Bool} (h : x.length = 3 * (thirdUnary x).length) :
    takeN x = x.take (thirdUnary x).length := by
  have h2 : (twoThirds x).length = 2 * (thirdUnary x).length := by
    simp [twoThirds, List.length_append, Nat.two_mul]
  rw [takeN, reverse_drop_reverse, h2, h]
  have : 3 * (thirdUnary x).length - 2 * (thirdUnary x).length = (thirdUnary x).length := by
    omega
  simp [this]

theorem midN_eq {x : List Bool} (h : x.length = 3 * (thirdUnary x).length) :
    midN x = (x.drop (thirdUnary x).length).take (thirdUnary x).length := by
  set n := (thirdUnary x).length
  rw [midN, dropN, reverse_drop_reverse]
  change (x.drop n).take ((x.drop n).length - n) = (x.drop n).take n
  have : (x.drop n).length - n = n := by
    have : (x.drop n).length = x.length - n := by simp
    omega
  rw [this]

theorem lastN_eq (x : List Bool) :
    lastN x = x.drop (2 * (thirdUnary x).length) := by
  simp [lastN, twoThirds, List.length_append, Nat.two_mul]

theorem drop_exact_append (n : ℕ) (b : Bool) (y : List Bool) :
    List.drop n (List.replicate n b ++ y) = y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, ih]

theorem take_exact_append (n : ℕ) (b : Bool) (y : List Bool) :
    List.take n (List.replicate n b ++ y) = List.replicate n b := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, ih]

theorem dec_iff (x : List Bool) :
    dec x = true ↔
      ∃ n : ℕ, x = List.replicate n true ++ List.replicate n false ++ List.replicate n true := by
  constructor
  · intro hdec
    have hand : (lenOk x && firstOk x && midOk x && lastOk x) = true := hdec
    have h1 : lenOk x = true := by
      simp only [Bool.and_eq_true] at hand; exact hand.1.1.1
    have h2 : firstOk x = true := by
      simp only [Bool.and_eq_true] at hand; exact hand.1.1.2
    have h3 : midOk x = true := by
      simp only [Bool.and_eq_true] at hand; exact hand.1.2
    have h4 : lastOk x = true := by
      simp only [Bool.and_eq_true] at hand; exact hand.2
    have hlen := lenOk_length h1
    set n := (thirdUnary x).length with hn_def
    have hn : thirdUnary x = List.replicate n true := by
      simp [thirdUnary_eq, n]
    have ht : takeN x = List.replicate n true := by
      have := of_decide_eq_true h2
      exact this.trans hn
    have hm : midN x = List.replicate n false := by
      have := of_decide_eq_true h3
      have hz : allFalse (thirdUnary x) = List.replicate n false := by
        simp [allFalse, hn]
      exact this.trans hz
    have hl : lastN x = List.replicate n true := by
      have := of_decide_eq_true h4
      exact this.trans hn
    have hx : x = x.take n ++ (x.drop n).take n ++ x.drop (2 * n) := by
      have hdd : (x.drop n).drop n = x.drop (2 * n) := by
        rw [List.drop_drop]
        simp [Nat.two_mul, Nat.add_comm]
      calc
        x = x.take n ++ x.drop n := (List.take_append_drop n x).symm
        _ = x.take n ++ ((x.drop n).take n ++ (x.drop n).drop n) := by
              rw [List.take_append_drop n (x.drop n)]
        _ = x.take n ++ (x.drop n).take n ++ x.drop (2 * n) := by
              rw [hdd, List.append_assoc]
    refine ⟨n, ?_⟩
    have hlen' : x.length = 3 * n := by simpa [n] using hlen
    have hdrop : x.drop (2 * n) = List.replicate n true := by
      have hln : lastN x = x.drop (2 * n) := by simp [lastN_eq, n]
      exact hln.symm.trans hl
    rw [hx, ← takeN_eq hlen', ← midN_eq hlen', ht, hm, hdrop]
  · intro ⟨n, hx⟩
    have hlenx : x.length = 3 * n := by
      simp [hx, List.length_append, List.length_replicate]
      omega
    have hn : thirdUnary x = List.replicate n true := by
      rw [thirdUnary_eq, hlenx]
      simp
    have hnl : (thirdUnary x).length = n := by simp [hn]
    have hlen : x.length = 3 * (thirdUnary x).length := by simp [hlenx, hnl]
    have hlenOk : lenOk x = true := by
      apply decide_eq_true
      have hall : ∀ y : List Bool, allTrue y = List.replicate y.length true := by
        intro y
        induction y with
        | nil => simp [allTrue]
        | cons _ xs ih => simp [allTrue, ih, List.replicate_succ]
      change allTrue x = twoThirds x ++ thirdUnary x
      rw [hall, hlenx, twoThirds, hn]
      have : 3 * n = n + (n + n) := by omega
      rw [this, List.replicate_add, List.replicate_add]
      simp [List.append_assoc]
      omega
    have hfirst : firstOk x = true := by
      apply decide_eq_true
      rw [takeN_eq hlen, hnl, hn, hx]
      simpa using take_exact_append n true (List.replicate n false ++ List.replicate n true)
    have hx' : x = List.replicate n true ++
        (List.replicate n false ++ List.replicate n true) := by
      simpa [List.append_assoc] using hx
    have hlast : lastOk x = true := by
      apply decide_eq_true
      rw [lastN_eq, hnl, hn, hx']
      have : 2 * n = n + n := by omega
      rw [this, ← List.drop_drop]
      rw [drop_exact_append n true]
      exact drop_exact_append n false (List.replicate n true)
    have hmid : midOk x = true := by
      apply decide_eq_true
      have hm1 : midN x = (x.drop n).take n := by
        simpa [hnl] using midN_eq hlen
      rw [hm1]
      have hdrop : x.drop n = List.replicate n false ++ List.replicate n true := by
        rw [hx']
        exact drop_exact_append n true _
      rw [hdrop, take_exact_append n false]
      simp [allFalse, hn]
    simp [dec, hlenOk, hfirst, hmid, hlast]

end PvsNP.Units.tl_lang_tft_n_p

open PvsNP.Units.tl_lang_tft_n_p

theorem PvsNP.Units.tl_lang_tft_n_p :
    ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate n false ++
      List.replicate n true} : Language Bool) ∈ PvsNP.P :=
  ⟨dec, cpt_dec, fun x => by
    change (∃ n : ℕ, x = List.replicate n true ++ List.replicate n false ++
      List.replicate n true) ↔ dec x = true
    exact (dec_iff x).symm⟩
