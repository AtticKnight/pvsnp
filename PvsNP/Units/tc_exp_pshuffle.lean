import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_transducer_polytime

namespace PvsNP.Units.tc_exp_pshuffle

def pick (q : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => (if q then [b] else []) ++ pick (!q) bs

theorem poly (q : Bool) : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (pick q) := by
  apply PvsNP.Units.m2_transducer_polytime Bool (fun s b => (!s, if s then some b else none)) (fun _ => none) pick _ _ q
  · intro s; rfl
  · intro s b xs; cases s <;> rfl

def even (x : List Bool) := x.foldl (fun q _ => !q) true = true

theorem unzip (x : List Bool) (he : even x) :
    (pick true x).length = (pick false x).length ∧
      x = (List.zipWith (fun a b => [a,b]) (pick true x) (pick false x)).flatten := by
  match x with
  | [] => exact ⟨rfl,rfl⟩
  | [_] => contradiction
  | a::b::xs =>
    obtain ⟨hlen, hz⟩ := unzip xs he
    simp [pick, hlen, hz.symm]

theorem recover (u v : List Bool) (h : u.length = v.length) :
    let x := (List.zipWith (fun a b => [a,b]) u v).flatten
    even x ∧ pick true x = u ∧ pick false x = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all [even,pick]
  | cons a us ih =>
    cases v with
    | nil => simp at h
    | cons b vs =>
      obtain ⟨he, hu, hv⟩ := ih vs (by simpa using h)
      exact ⟨he, congrArg (a :: ·) hu, congrArg (b :: ·) hv⟩

end PvsNP.Units.tc_exp_pshuffle

theorem PvsNP.Units.tc_exp_pshuffle :
∀ L₁ L₂ : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L R hL hR
  let A : Language Bool := {x | tc_exp_pshuffle.pick true x ∈ L}
  let B : Language Bool := {x | tc_exp_pshuffle.pick false x ∈ R}
  let E : Language Bool := {x | tc_exp_pshuffle.even x}
  have hA := m2_exp_down_closed A L ⟨_, tc_exp_pshuffle.poly true, fun _ => Iff.rfl⟩ hL
  have hB := m2_exp_down_closed B R ⟨_, tc_exp_pshuffle.poly false, fun _ => Iff.rfl⟩ hR
  have hE := m2_p_subset_exp E (m2_dfa_in_p Bool (fun q _ => !q) true id)
  obtain ⟨k,f,M,hf,ht⟩ := m2_exp_inter E (A ⊓ B) hE (m2_exp_inter A B hA hB)
  refine ⟨k,f,M,fun x => Iff.trans ?_ (hf x),ht⟩
  constructor
  · rintro ⟨u,v,h,rfl,hu,hv⟩
    obtain ⟨he,h1,h2⟩ := tc_exp_pshuffle.recover u v h
    refine ⟨he, ?_, ?_⟩
    · change tc_exp_pshuffle.pick true _ ∈ L
      rwa [h1]
    · change tc_exp_pshuffle.pick false _ ∈ R
      rwa [h2]
  · rintro ⟨he,h1,h2⟩
    obtain ⟨hl,hz⟩ := tc_exp_pshuffle.unzip x he
    exact ⟨_,_,hl,hz,h1,h2⟩
