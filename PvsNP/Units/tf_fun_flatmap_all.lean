import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_flatmap_all

private abbrev K := Fin 3
private abbrev Γ : K → Type := fun _ => Bool
private abbrev Stmt := Turing.TM2.Stmt Γ Bool (Option Bool)

private def pushList : List Bool → Stmt → Stmt
  | [], next => next
  | c :: cs, next => Turing.TM2.Stmt.push 2 (fun _ => c) (pushList cs next)

private abbrev flatMapTM (h : Bool → List Bool) : Turing.FinTM2 where
  K := K
  k₀ := 0
  k₁ := 2
  Γ := Γ
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstance
  m
    | false =>
      Turing.TM2.Stmt.pop 0 (fun _ ob => ob)
        (Turing.TM2.Stmt.branch (fun ob => ob.isSome)
          (Turing.TM2.Stmt.push 1 (fun ob => ob.getD false)
            (Turing.TM2.Stmt.load (fun _ => none) (Turing.TM2.Stmt.goto (fun _ => false))))
          (Turing.TM2.Stmt.goto (fun _ => true)))
    | true =>
      Turing.TM2.Stmt.pop 1 (fun _ ob => ob)
        (Turing.TM2.Stmt.branch (fun ob => ob.isSome)
          (Turing.TM2.Stmt.branch (fun ob => ob.getD false)
            (pushList (h true).reverse
              (Turing.TM2.Stmt.load (fun _ => none) (Turing.TM2.Stmt.goto (fun _ => true))))
            (pushList (h false).reverse
              (Turing.TM2.Stmt.load (fun _ => none) (Turing.TM2.Stmt.goto (fun _ => true)))))
          Turing.TM2.Stmt.halt)

private def mkStk (s0 s1 s2 : List Bool) : ∀ k : K, List (Γ k)
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2

private lemma update_mkStk0 (s0 s1 s2 s0' : List Bool) :
    Function.update (mkStk s0 s1 s2) (0 : K) s0' = mkStk s0' s1 s2 := by
  funext k; rcases k with ⟨k, hk⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

private lemma update_mkStk1 (s0 s1 s2 s1' : List Bool) :
    Function.update (mkStk s0 s1 s2) (1 : K) s1' = mkStk s0 s1' s2 := by
  funext k; rcases k with ⟨k, hk⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

private lemma update_mkStk2 (s0 s1 s2 s2' : List Bool) :
    Function.update (mkStk s0 s1 s2) (2 : K) s2' = mkStk s0 s1 s2' := by
  funext k; rcases k with ⟨k, hk⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

private lemma stepAux_pushList (l : List Bool) (next : Stmt) (v : Option Bool)
    (s0 s1 s2 : List Bool) :
    Turing.TM2.stepAux (pushList l next) v (mkStk s0 s1 s2) =
      Turing.TM2.stepAux next v (mkStk s0 s1 (l.reverse ++ s2)) := by
  induction l generalizing s2 with
  | nil => simp [pushList]
  | cons c cs ih =>
    simp only [pushList, Turing.TM2.stepAux, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    have h2 : mkStk s0 s1 s2 2 = s2 := rfl
    rw [h2, update_mkStk2]
    exact ih (c :: s2)

private lemma phase1_run (h : Bool → List Bool) :
    ∀ (s0 s1 : List Bool),
      (flip bind (flatMapTM h).step)^[s0.length + 1]
        (some (⟨some false, none, mkStk s0 s1 []⟩ : (flatMapTM h).Cfg)) =
      some (⟨some true, none, mkStk [] (s0.reverse ++ s1) []⟩ : (flatMapTM h).Cfg) := by
  intro s0
  induction s0 with
  | nil =>
    intro s1
    change (flatMapTM h).step (⟨some false, none, mkStk [] s1 []⟩ : (flatMapTM h).Cfg) =
      some (⟨some true, none, mkStk [] s1 []⟩ : (flatMapTM h).Cfg)
    change some (Turing.TM2.stepAux ((flatMapTM h).m false) none (mkStk [] s1 [])) = _
    simp only [flatMapTM, Turing.TM2.stepAux]
    have h0 : mkStk [] s1 [] 0 = [] := rfl
    rw [h0]
    simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkStk0]
  | cons b xs ih =>
    intro s1
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have hstep : (flatMapTM h).step (⟨some false, none, mkStk (b :: xs) s1 []⟩ : (flatMapTM h).Cfg) =
        some (⟨some false, none, mkStk xs (b :: s1) []⟩ : (flatMapTM h).Cfg) := by
      change some (Turing.TM2.stepAux ((flatMapTM h).m false) none (mkStk (b :: xs) s1 [])) = _
      simp only [flatMapTM, Turing.TM2.stepAux]
      have h0 : mkStk (b :: xs) s1 [] 0 = b :: xs := rfl
      rw [h0]
      simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
        Bool.cond_true]
      rw [update_mkStk0]
      have h1 : mkStk xs s1 [] 1 = s1 := rfl
      rw [h1, update_mkStk1]
    change (flip bind (flatMapTM h).step)^[xs.length + 1]
      ((flatMapTM h).step (⟨some false, none, mkStk (b :: xs) s1 []⟩ : (flatMapTM h).Cfg)) = _
    rw [hstep, List.reverse_cons, List.append_assoc]
    exact ih (b :: s1)

private lemma haltList_eq (h : Bool → List Bool) (s2 : List Bool) :
    Turing.haltList (flatMapTM h) s2 = (⟨none, none, mkStk [] [] s2⟩ : (flatMapTM h).Cfg) := by
  change (⟨none, none, _⟩ : (flatMapTM h).Cfg) = _
  congr 1
  funext k
  rcases k with ⟨k, hk⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

private lemma initList_eq (h : Bool → List Bool) (x : List Bool) :
    Turing.initList (flatMapTM h) x = (⟨some false, none, mkStk x [] []⟩ : (flatMapTM h).Cfg) := by
  change (⟨some false, none, _⟩ : (flatMapTM h).Cfg) = _
  congr 1
  funext k
  rcases k with ⟨k, hk⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

private lemma phase2_run (h : Bool → List Bool) :
    ∀ (s1 s2 : List Bool),
      (flip bind (flatMapTM h).step)^[s1.length + 1]
        (some (⟨some true, none, mkStk [] s1 s2⟩ : (flatMapTM h).Cfg)) =
      some (Turing.haltList (flatMapTM h) (s1.reverse.flatMap h ++ s2)) := by
  intro s1
  induction s1 with
  | nil =>
    intro s2
    rw [haltList_eq]
    change some (Turing.TM2.stepAux ((flatMapTM h).m true) none (mkStk [] [] s2)) = _
    simp only [flatMapTM, Turing.TM2.stepAux]
    have h1 : mkStk [] [] s2 1 = [] := rfl
    rw [h1]
    simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkStk1]
    rfl
  | cons b rs ih =>
    intro s2
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have hstep : (flatMapTM h).step (⟨some true, none, mkStk [] (b :: rs) s2⟩ : (flatMapTM h).Cfg) =
        some (⟨some true, none, mkStk [] rs (h b ++ s2)⟩ : (flatMapTM h).Cfg) := by
      change some (Turing.TM2.stepAux ((flatMapTM h).m true) none (mkStk [] (b :: rs) s2)) = _
      simp only [flatMapTM, Turing.TM2.stepAux]
      have h1 : mkStk [] (b :: rs) s2 1 = b :: rs := rfl
      rw [h1]
      simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
        Bool.cond_true]
      rw [update_mkStk1]
      cases b with
      | false =>
        simp only [Bool.cond_false]
        rw [stepAux_pushList, List.reverse_reverse]
        rfl
      | true =>
        simp only [Bool.cond_true]
        rw [stepAux_pushList, List.reverse_reverse]
        rfl
    change (flip bind (flatMapTM h).step)^[rs.length + 1]
      ((flatMapTM h).step (⟨some true, none, mkStk [] (b :: rs) s2⟩ : (flatMapTM h).Cfg)) = _
    rw [hstep, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]
    exact ih (h b ++ s2)

private noncomputable def flatMapPoly (h : Bool → List Bool) :
    Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.flatMap h) where
  tm := flatMapTM h
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun x :=
    { steps := x.length + 1 + (x.length + 1)
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun (PvsNP.encodeString l) = l := by
          intro l; simp [PvsNP.encodeString, Computability.encodingList]
        change (flip bind (flatMapTM h).step)^[(x.length + 1) + (x.length + 1)]
          (some (Turing.initList (flatMapTM h)
            (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x)))) =
          some (Turing.haltList (flatMapTM h)
            (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString (x.flatMap h))))
        rw [hm x, hm (x.flatMap h), initList_eq, Function.iterate_add_apply, phase1_run h x [],
          List.append_nil]
        have h2 := phase2_run h x.reverse []
        simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
        exact h2
      steps_le_m := by
        simp only [PvsNP.encodeString, Computability.encodingList, id_eq,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        omega }

end PvsNP.Units.tf_fun_flatmap_all

theorem PvsNP.Units.tf_fun_flatmap_all :
    ∀ h : Bool → List Bool,
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => x.flatMap h) :=
  fun h => ⟨PvsNP.Units.tf_fun_flatmap_all.flatMapPoly h⟩
