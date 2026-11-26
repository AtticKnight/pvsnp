import Mathlib
import PvsNP.Defs
import CookLevin

/- Original occurrence-splitting construction prepared by AtticKnight with OpenAI Codex.
For an input formula with an m-cell encoding, literal occurrence i of variable v
gets the fresh variable v * (m+1) + i. Each block of m+1 consecutive copies is
joined by a directed cycle of binary implications. The cycle enforces equality
and contributes exactly two occurrences per variable. The register program
first scans the source formula and then emits the cycles using bounded loops. -/
namespace PvsNP.Units.m3_sat_to_3occ_sat

def renameClause (width : Nat) : Nat → clause → clause
  | _, [] => []
  | offset, l :: ls =>
      (l.1, l.2 * width + offset) :: renameClause width (offset + 1) ls

def rename (width : Nat) : Nat → cnf → cnf
  | _, [] => []
  | offset, c :: cs =>
      renameClause width offset c :: rename width (offset + c.length) cs

def edge (x y : var) : clause := [(false, x), (true, y)]

def path (last : var) : var → List var → cnf
  | x, [] => [edge x last]
  | x, y :: ys => edge x y :: path last y ys

def block (m v : Nat) : cnf :=
  let start := v * (m + 1)
  path start start (List.range' (start + 1) m)

def links (m : Nat) : Nat → cnf
  | 0 => []
  | n + 1 => links m n ++ block m n

def numOcc (v : var) (f : cnf) : Nat := f.flatten.countP (fun l => l.2 == v)

theorem numOcc_append (v : var) (f g : cnf) :
    numOcc v (f ++ g) = numOcc v f + numOcc v g := by
  simp [numOcc]

theorem path_count (v last first : var) (rest : List var) :
    numOcc v (path last first rest) =
      (first :: rest).count v + (rest ++ [last]).count v := by
  induction rest generalizing first with
  | nil => simp [numOcc, path, edge, List.count_cons, List.countP_cons, BEq.comm, Nat.add_comm]
  | cons y ys ih =>
    have h := ih y
    simp only [path, numOcc, List.flatten_cons, List.countP_append] at h ⊢
    simp [edge, List.count_cons, List.countP_cons, BEq.comm] at h ⊢
    omega

theorem block_count (v m k : Nat) :
    numOcc v (block m k) = 2 * (List.range' (k*(m+1)) (m+1)).count v := by
  rw [block, path_count]
  simp [List.range'_succ, List.count_cons, two_mul, Nat.add_comm, Nat.add_left_comm]

theorem links_count (v m n : Nat) :
    numOcc v (links m n) = 2 * (List.range' 0 (n*(m+1))).count v := by
  induction n with
  | zero => simp [links, numOcc]
  | succ n ih =>
    rw [links, numOcc_append, ih, block_count, Nat.succ_mul n (m+1),
      ← List.range'_append_1 (s := 0) (m := n*(m+1)) (n := m+1)]
    rw [Nat.zero_add, List.count_append]
    exact (Nat.mul_add 2 _ _).symm

theorem clause_offsets (m offset : Nat) (c : clause) (bound : offset + c.length ≤ m+1) :
    (renameClause (m+1) offset c).map (fun l => l.2 % (m+1)) =
      List.range' offset c.length := by
  induction c generalizing offset with
  | nil => simp [renameClause]
  | cons l ls ih =>
    have ho : offset < m+1 := by simp at bound; omega
    have hb : offset + 1 + ls.length ≤ m+1 := by simp at bound; omega
    simp [renameClause, List.range'_succ, Nat.mod_eq_of_lt ho, ih _ hb]

theorem formula_offsets (m offset : Nat) (f : cnf) (bound : offset + f.flatten.length ≤ m+1) :
    (rename (m+1) offset f).flatten.map (fun l => l.2 % (m+1)) =
      List.range' offset f.flatten.length := by
  induction f generalizing offset with
  | nil => simp [rename]
  | cons c cs ih =>
    simp only [List.flatten_cons, List.length_append] at bound ⊢
    rw [rename, List.flatten_cons, List.map_append, clause_offsets m offset c (by omega),
      ih (offset+c.length) (by omega), List.range'_append_1]

theorem rename_bound (v m : Nat) (f : cnf) (len : f.flatten.length ≤ m+1) :
    numOcc v (rename (m+1) 0 f) ≤ 1 := by
  let xs := (rename (m+1) 0 f).flatten.map Prod.snd
  have ho : xs.map (· % (m+1)) = List.range' 0 f.flatten.length := by
    simpa [xs, Function.comp_def] using formula_offsets m 0 f (by omega)
  have h := List.count_le_count_map (l := xs) (f := (· % (m+1))) (x := v)
  rw [ho] at h
  have hr : (List.range' 0 f.flatten.length).Nodup := List.nodup_range'
  have hk := (List.nodup_iff_count_le_one.mp hr) (v % (m+1))
  change (rename (m+1) 0 f).flatten.countP (fun l => l.2 == v) ≤ 1
  simpa [xs, List.count_eq_countP, Function.comp_def, BEq.comm] using (h.trans hk)

def split (f : cnf) (m n : Nat) := rename (m+1) 0 f ++ links m n

theorem occurrence_bound (v m n : Nat) (f : cnf) (len : f.flatten.length ≤ m+1) :
    numOcc v (split f m n) ≤ 3 := by
  rw [split, numOcc_append, links_count]
  have hn : (List.range' 0 (n*(m+1))).Nodup := List.nodup_range'
  have h1 := List.nodup_iff_count_le_one.mp hn v
  have h2 := rename_bound v m f len
  omega

theorem edge_ok (a : assgn) (x y : var) :
    evalClause a (edge x y) = true ↔ (x ∈ a → y ∈ a) := by
  by_cases hx : x ∈ a <;> simp [edge, evalClause, evalLiteral, evalVar, hx]

theorem cnf_cons_ok (a : assgn) (c : clause) (cs : cnf) :
    evalCnf a (c :: cs) = true ↔ evalClause a c = true ∧ evalCnf a cs = true := by
  simp [evalCnf]

theorem path_chain (a : assgn) (last first : var) (rest : List var)
    (h : evalCnf a (path last first rest) = true) :
    (first ∈ a → (∀ z ∈ rest, z ∈ a) ∧ last ∈ a) ∧
    (∀ z ∈ rest, z ∈ a → last ∈ a) := by
  induction rest generalizing first with
  | nil =>
    have hxy := (edge_ok a first last).mp ((cnf_cons_ok _ _ _).mp h).1
    simpa using hxy
  | cons y ys ih =>
    obtain ⟨hxy, htail⟩ := (cnf_cons_ok _ _ _).mp h
    have hxy' := (edge_ok a first y).mp hxy
    obtain ⟨forward, back⟩ := ih y htail
    constructor
    · intro hx
      have hy := hxy' hx
      exact ⟨by simpa using And.intro hy (forward hy).1, (forward hy).2⟩
    · intro z hz hz'
      rcases List.mem_cons.mp hz with rfl | hrest
      · exact (forward hz').2
      · exact back z hrest hz'

theorem path_holds (a : assgn) (last first : var) (rest : List var)
    (h : ∀ z ∈ first :: rest, z ∈ a ↔ last ∈ a) :
    evalCnf a (path last first rest) = true := by
  induction rest generalizing first with
  | nil =>
    apply (cnf_cons_ok _ _ _).mpr
    exact ⟨(edge_ok _ _ _).mpr (h first (by simp)).mp, rfl⟩
  | cons y ys ih =>
    apply (cnf_cons_ok _ _ _).mpr
    refine ⟨(edge_ok _ _ _).mpr (fun hx => (h y (by simp)).mpr ((h first (by simp)).mp hx)), ?_⟩
    exact ih y (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem block_agree (a : assgn) {m v i : Nat} (hi : i < m+1)
    (h : evalCnf a (block m v) = true) :
    v*(m+1)+i ∈ a ↔ v*(m+1) ∈ a := by
  cases i with
  | zero => simp
  | succ j =>
    let start := v*(m+1)
    have hj : start+(j+1) ∈ List.range' (start+1) m := List.mem_range'_1.mpr (by omega)
    obtain ⟨forward, back⟩ := path_chain a start start (List.range' (start+1) m) h
    exact ⟨back _ hj, fun hs => (forward hs).1 _ hj⟩

theorem links_ok (a : assgn) (m n : Nat) :
    evalCnf a (links m n) = true ↔ ∀ v < n, evalCnf a (block m v) = true := by
  induction n with
  | zero => simp [links, evalCnf]
  | succ n ih =>
    rw [links, evalCnf_app_iff, ih]
    exact ⟨fun ⟨hs, hn⟩ v hv => (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv)).elim
      (hs v) (fun e => e ▸ hn), fun h => ⟨fun v hv => h v (by omega), h n (by omega)⟩⟩

def bounded (n : Nat) (f : cnf) : Prop := ∀ c ∈ f, ∀ l ∈ c, l.2 < n

theorem eval_renameClause (a b : assgn) (m n : Nat)
    (agrees : ∀ v < n, ∀ i < m+1, v*(m+1)+i ∈ b ↔ v ∈ a)
    (c : clause) (offset : Nat) (length_ok : offset+c.length ≤ m+1)
    (vars_ok : ∀ l ∈ c, l.2 < n) :
    evalClause b (renameClause (m+1) offset c) = evalClause a c := by
  induction c generalizing offset with
  | nil => rfl
  | cons l ls ih =>
    have hi : offset < m+1 := by simp at length_ok; omega
    have hlen : offset+1+ls.length ≤ m+1 := by simp at length_ok; omega
    have he := agrees l.2 (vars_ok l (by simp)) offset hi
    have ht := ih (offset+1) hlen (fun p hp => vars_ok p (List.mem_cons_of_mem _ hp))
    change (evalLiteral b (l.1,l.2*(m+1)+offset) || evalClause b _) =
      (evalLiteral a l || evalClause a ls)
    rw [ht]
    cases l
    simp_all [evalLiteral, evalVar]
    rfl

theorem eval_rename (a b : assgn) (m n : Nat)
    (agrees : ∀ v < n, ∀ i < m+1, v*(m+1)+i ∈ b ↔ v ∈ a)
    (f : cnf) (offset : Nat) (len : offset+f.flatten.length ≤ m+1)
    (vars_ok : bounded n f) :
    evalCnf b (rename (m+1) offset f) = evalCnf a f := by
  induction f generalizing offset with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatten_cons, List.length_append] at len
    have hc := eval_renameClause a b m n agrees c offset (by omega) (vars_ok c (by simp))
    have ht := ih (offset+c.length) (by omega) (fun d hd => vars_ok d (List.mem_cons_of_mem _ hd))
    change (evalClause b _ && evalCnf b _) = (evalClause a c && evalCnf a cs)
    rw [hc, ht]

def liftAssignment (a : assgn) (m n : Nat) : assgn :=
  (List.range (n*(m+1))).filter (fun z => decide (z/(m+1) ∈ a))

theorem lift_iff (a : assgn) (m n v i : Nat) (hv : v < n) (hi : i < m+1) :
    v*(m+1)+i ∈ liftAssignment a m n ↔ v ∈ a := by
  have hb : v*(m+1)+i < n*(m+1) := calc
    _ < v*(m+1)+(m+1) := by omega
    _ = (v+1)*(m+1) := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hv
  have hd : (v*(m+1)+i)/(m+1) = v := by
    rw [Nat.mul_comm v (m+1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  simp [liftAssignment, hb, hd]

theorem split_sat (f : cnf) (m n : Nat) (len : f.flatten.length ≤ m+1)
    (vars_ok : bounded n f) : SAT (split f m n) ↔ SAT f := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hmain, hl⟩ := (evalCnf_app_iff _ _ _).mp hb
    let a := (List.range n).filter (fun v => decide (v*(m+1) ∈ b))
    have ha : ∀ v < n, ∀ i < m+1, v*(m+1)+i ∈ b ↔ v ∈ a := by
      intro v hv i hi
      rw [block_agree b hi ((links_ok b m n).mp hl v hv)]
      simp [a, hv]
    exact ⟨a, (eval_rename a b m n ha f 0 (by omega) vars_ok).symm.trans hmain⟩
  · rintro ⟨a, ha⟩
    let b := liftAssignment a m n
    have ha' : ∀ v < n, ∀ i < m+1, v*(m+1)+i ∈ b ↔ v ∈ a :=
      fun v hv i hi => lift_iff a m n v i hv hi
    refine ⟨b, (evalCnf_app_iff _ _ _).mpr ⟨(eval_rename a b m n ha' f 0 (by omega) vars_ok).trans ha, ?_⟩⟩
    apply (links_ok b m n).mpr
    intro v hv
    apply path_holds
    intro z hz
    have hmem : z ∈ List.range' (v*(m+1)) (m+1) := hz
    have bounds : v*(m+1) ≤ z ∧ z < v*(m+1)+(m+1) := List.mem_range'_1.mp hmem
    obtain ⟨hle, hlt⟩ := bounds
    have hi : z-v*(m+1) < m+1 := Nat.sub_lt_left_of_lt_add hle hlt
    have he := (ha' v hv (z-v*(m+1)) hi).trans (ha' v hv 0 (by omega)).symm
    simpa [Nat.add_sub_of_le hle] using he

open CookLevin.Lang
open EvalCnfCmd (encodeLit encodeClause encodeCnf)

theorem clause_budget (c : clause) :
    c.length ≤ (encodeClause c).length ∧ ∀ l ∈ c, l.2 < (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l ls ih =>
    have hlen : (encodeClause (l::ls)).length = l.2+3+(encodeClause ls).length := by
      rcases l with ⟨p,v⟩
      simp [encodeClause, encodeLit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    simp only [hlen]
    constructor
    · simp only [List.length_cons]; omega
    · intro p hp; rcases List.mem_cons.mp hp with rfl | hm
      · exact (show ∀ a b : Nat, a < a+3+b from by intros; omega) _ _
      · exact Nat.lt_of_lt_of_le (ih.2 p hm) (Nat.le_add_left _ _)

theorem formula_budget (f : cnf) :
    f.flatten.length ≤ (encodeCnf f).length ∧ bounded ((encodeCnf f).length+1) f := by
  induction f with
  | nil => simp [bounded, encodeCnf]
  | cons c cs ih =>
    have bh := clause_budget c
    simp only [bounded, CnfSerialize.encodeCnf_cons, List.length_append, List.flatten_cons] at ih ⊢
    constructor
    · omega
    · intro d hd l hl
      rcases List.mem_cons.mp hd with rfl | hs
      · exact Nat.lt_of_lt_of_le (bh.2 l hl) ((Nat.le_add_right _ _).trans (Nat.le_succ _))
      · exact Nat.lt_of_lt_of_le (ih.2 d hs l hl) (Nat.add_le_add_right (Nat.le_add_left _ _) 1)

def outputCnf (x : List Bool) : cnf :=
  let f := SATStr.cnfOf x
  let m := (encodeCnf f).length
  split f m (m+1)

def transformBits (x : List Bool) : List Bool := SATToSATStr.satToStr (outputCnf x)

theorem transform_correct (x : List Bool) :
    SATStr x ↔
      (∀ v : var, ((SATStr.cnfOf (transformBits x)).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
      SAT (SATStr.cnfOf (transformBits x)) := by
  have hp : SATStr.cnfOf (transformBits x) = outputCnf x := by
    unfold SATStr.cnfOf transformBits
    rw [SATToSATStr.strBits_satToStr, CnfWellFormed.parseTotal_encodeCnf]
  rw [hp]
  let f := SATStr.cnfOf x
  let m := (encodeCnf f).length
  obtain ⟨hlen,hvars⟩ := formula_budget f
  have len : f.flatten.length ≤ m+1 := Nat.le_succ_of_le hlen
  have hsat := split_sat f m (m+1) len hvars
  exact ⟨fun h => ⟨fun v => occurrence_bound v m (m+1) f len, hsat.mpr h⟩,
         fun h => hsat.mp h.2⟩

/- Registers 0 through 24 belong to the official CNF reader. Register 0 is
also the canonical output after we have saved the reader's CNF stream. -/
abbrev stream : Var := 25
abbrev width : Var := 26
abbrev index : Var := 27
abbrev cursor : Var := 28
abbrev headBit : Var := 29
abbrev signMode : Var := 30
abbrev varMode : Var := 31
abbrev offset : Var := 32
abbrev startId : Var := 33
abbrev currentId : Var := 34
abbrev blockIndex : Var := 35
abbrev pathIndex : Var := 36
abbrev acc : Var := 0

def setFlag (r : Var) : Cmd := Cmd.op (.clear r) ;; Cmd.op (.appendOne r)

def onSign : Cmd :=
  Cmd.op (.concat acc acc headBit) ;; Cmd.op (.concat acc acc offset) ;;
  Cmd.op (.appendOne offset) ;; Cmd.op (.clear signMode) ;; setFlag varMode

def onVar : Cmd :=
  Cmd.ifBit headBit (Cmd.op (.concat acc acc width))
    (Cmd.op (.appendZero acc) ;; Cmd.op (.clear varMode))

def onSlot : Cmd :=
  Cmd.ifBit headBit (Cmd.op (.appendOne acc) ;; setFlag signMode) (Cmd.op (.appendZero acc))

def scanOne : Cmd :=
  Cmd.op (.head headBit cursor) ;; Cmd.op (.tail cursor cursor) ;;
  Cmd.ifBit signMode onSign (Cmd.ifBit varMode onVar onSlot)

def buildWidth : Cmd := Cmd.forBnd index stream (Cmd.op (.appendOne width))

def scanFront : Cmd :=
  Cmd.op (.copy stream EvalCnfCmd.CNF_STREAM) ;; Cmd.op (.clear acc) ;; Cmd.op (.clear width)

def scanBack : Cmd :=
  Cmd.op (.appendOne width) ;; Cmd.op (.copy cursor stream) ;;
  Cmd.op (.clear offset) ;; Cmd.op (.clear signMode) ;; Cmd.op (.clear varMode)

def scanInit : Cmd := scanFront ;; buildWidth ;; scanBack

def edgeLeft : Cmd :=
  Cmd.op (.appendOne acc) ;; Cmd.op (.appendZero acc) ;; Cmd.op (.concat acc acc currentId) ;;
  Cmd.op (.appendZero acc)

def edgeRight (id : Var) : Cmd :=
  Cmd.op (.appendOne acc) ;; Cmd.op (.appendOne acc) ;; Cmd.op (.concat acc acc id) ;;
  Cmd.op (.appendZero acc) ;; Cmd.op (.appendZero acc)

def stepEdge : Cmd := edgeLeft ;; Cmd.op (.appendOne currentId) ;; edgeRight currentId

def blockFinish : Cmd := edgeLeft ;; edgeRight startId ;; Cmd.op (.concat startId startId width)

def blockBody : Cmd :=
  Cmd.op (.copy currentId startId) ;; Cmd.forBnd pathIndex stream stepEdge ;; blockFinish

def readFormula : Cmd := Cmd.op (.clear 1) ;; SATStr.satStrBuild
def rewriteFormula : Cmd := scanInit ;; Cmd.forBnd index stream scanOne
def appendLinks : Cmd := Cmd.op (.clear startId) ;; Cmd.forBnd blockIndex width blockBody
def program : Cmd := readFormula ;; (rewriteFormula ;; appendLinks)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem program_checked : (program.chk (2^37-1)).1 = true := by decide

inductive ScanMode where
  | slot | sign | variable
  deriving DecidableEq

structure ScanView where
  mode : ScanMode
  nextOffset : Nat
  emitted : List Nat

abbrev ones (n : Nat) : List Nat := List.replicate n 1

def advance (w : Nat) (a : ScanView) (b : Nat) : ScanView :=
  match a.mode with
  | .slot => if b = 1 then ⟨.sign, a.nextOffset, a.emitted ++ [1]⟩
             else ⟨.slot, a.nextOffset, a.emitted ++ [0]⟩
  | .sign => ⟨.variable, a.nextOffset+1, (a.emitted ++ [b]) ++ ones a.nextOffset⟩
  | .variable => if b = 1 then ⟨.variable, a.nextOffset, a.emitted ++ ones w⟩
                 else ⟨.slot, a.nextOffset, a.emitted ++ [0]⟩

structure ScanInv (s : State) (w : Nat) (rest : List Nat) (a : ScanView) : Prop where
  cur : s.get cursor = rest
  wid : s.get width = ones w
  off : s.get offset = ones a.nextOffset
  out : s.get acc = a.emitted
  sign : s.get signMode = (if a.mode = .sign then [1] else [])
  variableFlag : s.get varMode = (if a.mode = .variable then [1] else [])

theorem regRead (s : State) (r t : Var) (v : List Nat) :
    (s.set r v).get t = if t = r then v else s.get t := by
  by_cases h : t = r
  · subst t; simp [State.get_set_eq]
  · simp [h, State.get_set_ne _ _ _ _ h]

theorem condRun (r : Var) (p q : Cmd) (s : State) :
    (Cmd.ifBit r p q).eval s = if s.get r = [1] then p.eval s else q.eval s := by
  split <;> rename_i h
  · exact Cmd.eval_ifBit_true _ _ _ _ h
  · exact Cmd.eval_ifBit_false _ _ _ _ h

theorem ones_succ (n : Nat) : ones (n+1) = ones n ++ [1] := by
  rw [ones, List.replicate_add]; rfl

theorem scan_record (s : State) (w j b : Nat) (rest : List Nat) (a : ScanView)
    (h : ScanInv s w (b::rest) a) :
    ScanInv (scanOne.eval (s.set index (ones j))) w rest (advance w a b) := by
  obtain ⟨m,o,z⟩ := a
  obtain ⟨hc,hw,ho,hz,hs,hv⟩ := h
  cases m <;> by_cases hb : b=1 <;>
    simp_all [advance, scanOne, onSlot, onSign, onVar, setFlag, Cmd.eval_seq, Cmd.eval_op,
      Op.eval, regRead, condRun, signMode, varMode, headBit, cursor, width, index, acc, offset,
      ones_succ, ScanInv.mk]

theorem scan_fold (s : State) (w j : Nat) (bits suffix : List Nat) (a : ScanView)
    (h : ScanInv s w (bits ++ suffix) a) :
    ScanInv (Cmd.foldlState scanOne index (List.range' j bits.length) s) w suffix
      (bits.foldl (advance w) a) := by
  induction bits generalizing j s a with
  | nil => simpa [Cmd.foldlState] using h
  | cons b bs ih =>
    rw [List.length_cons, List.range'_succ, Cmd.foldlState, List.foldl_cons, List.foldl_cons]
    exact ih _ _ _ (scan_record s w j b (bs ++ suffix) a h)

theorem scan_unary (w o v : Nat) (z : List Nat) :
    (ones v).foldl (advance w) ⟨.variable,o,z⟩ =
      ⟨.variable,o,z ++ ones (v*w)⟩ := by
  induction v with
  | zero => simp [ones]
  | succ v ih =>
    rw [ones_succ, List.foldl_append, ih, Nat.succ_mul]
    simp [advance, ones, -List.replicate_append_replicate, List.replicate_add, List.append_assoc]

theorem scan_lit (w o : Nat) (z : List Nat) (l : literal) :
    (encodeLit l).foldl (advance w) ⟨.slot,o,z⟩ =
      ⟨.slot,o+1,z ++ encodeLit (l.1,l.2*w+o)⟩ := by
  obtain ⟨p,v⟩ := l
  unfold encodeLit
  simp only [List.foldl_cons, List.foldl_append, List.foldl_nil]
  change advance w ((ones v).foldl (advance w)
    ⟨.variable,o+1,((z ++ [1]) ++ [if p then 1 else 0]) ++ ones o⟩) 0 = _
  rw [scan_unary, Nat.add_comm (v*w) o]
  simp [advance, ones, -List.replicate_append_replicate, List.replicate_add, List.append_assoc]

theorem encode_clause_cons (l : literal) (c : clause) :
    encodeClause (l::c) = encodeLit l ++ encodeClause c := by
  simp [encodeClause, List.append_assoc]

theorem scan_clause (w o : Nat) (z : List Nat) (c : clause) :
    (encodeClause c).foldl (advance w) ⟨.slot,o,z⟩ =
      ⟨.slot,o+c.length,z ++ encodeClause (renameClause w o c)⟩ := by
  induction c generalizing o z with
  | nil => simp [encodeClause, renameClause, advance]
  | cons l cs ih =>
    rw [encode_clause_cons, List.foldl_append, scan_lit, ih, renameClause, encode_clause_cons]
    simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scan_cnf (w o : Nat) (z : List Nat) (f : cnf) :
    (encodeCnf f).foldl (advance w) ⟨.slot,o,z⟩ =
      ⟨.slot,o+f.flatten.length,z ++ encodeCnf (rename w o f)⟩ := by
  induction f generalizing o z with
  | nil => simp [encodeCnf, rename]
  | cons c cs ih =>
    rw [CnfSerialize.encodeCnf_cons, List.foldl_append, scan_clause, ih, rename,
      CnfSerialize.encodeCnf_cons]
    simp [List.append_assoc, Nat.add_assoc]

theorem buildWidth_get (s : State) (hz : s.get width = []) :
    (buildWidth.eval s).get width = ones (s.get stream).length := by
  rw [buildWidth, Cmd.eval_forBnd]
  refine Cmd.foldlState_range_induct _ _ _ _ (fun i t => t.get width = ones i) hz ?_
  intro i t _ hi
  simp [Cmd.eval_op, Op.eval, regRead, hi, width, index, ones_succ]

theorem init_record (s : State) (b : List Nat) (hc : s.get EvalCnfCmd.CNF_STREAM = b) :
    ScanInv (scanInit.eval s) (b.length+1) b ⟨.slot,0,[]⟩ ∧
      (scanInit.eval s).get stream = b := by
  let a := scanFront.eval s
  have ha : a.get width = [] ∧ a.get stream = b ∧ a.get acc = [] := by
    simp [a, scanFront, Cmd.eval_seq, Cmd.eval_op, Op.eval, regRead, acc, width, stream, hc]
  let t := buildWidth.eval a
  have tw : t.get width = ones b.length := by rw [show t.get width = _ from buildWidth_get a ha.1, ha.2.1]
  have ts : t.get stream = b :=
    (Cmd.eval_get_of_not_writes buildWidth a stream (by decide)).trans ha.2.1
  have ta : t.get acc = [] :=
    (Cmd.eval_get_of_not_writes buildWidth a acc (by decide)).trans ha.2.2
  simp only [scanInit, Cmd.eval_seq]
  change ScanInv (scanBack.eval t) (b.length+1) b ⟨.slot,0,[]⟩ ∧ (scanBack.eval t).get stream = b
  constructor
  · constructor <;> simp_all [scanBack, Cmd.eval_seq, Cmd.eval_op, Op.eval, regRead, cursor,
      signMode, varMode, offset, width, stream, acc, ones_succ, ones]
  · exact (Cmd.eval_get_of_not_writes scanBack t stream (by decide)).trans ts

theorem after_scan (s : State) (f : cnf) (hc : s.get EvalCnfCmd.CNF_STREAM = encodeCnf f) :
    let m := (encodeCnf f).length
    let t := (Cmd.forBnd index stream scanOne).eval (scanInit.eval s)
    t.get acc = encodeCnf (rename (m+1) 0 f) ∧ t.get stream = encodeCnf f ∧
      t.get width = ones (m+1) := by
  obtain ⟨h,hs⟩ := init_record _ _ hc
  let a := scanInit.eval s
  have h' := scan_fold a _ 0 (encodeCnf f) [] ⟨.slot,0,[]⟩ (by simpa [a] using h)
  rw [scan_cnf] at h'
  have he : (Cmd.forBnd index stream scanOne).eval a =
      Cmd.foldlState scanOne index (List.range' 0 (encodeCnf f).length) a := by
    rw [Cmd.eval_forBnd, show a.get stream = _ from hs, List.range_eq_range']
  exact ⟨he ▸ (by simpa using h'.out),
    (Cmd.eval_get_of_not_writes _ a stream (by decide)).trans hs, he ▸ h'.wid⟩

def steps (j : Nat) : Nat → cnf
  | 0 => []
  | k+1 => steps j k ++ [edge (j+k) (j+k+1)]

theorem steps_front (j k : Nat) :
    steps j (k+1) = edge j (j+1) :: steps (j+1) k := by
  induction k with
  | zero => simp [steps]
  | succ k ih =>
    rw [steps, ih]
    simp only [steps]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem path_steps (last j k : Nat) :
    path last j (List.range' (j+1) k) = steps j k ++ [edge (j+k) last] := by
  induction k generalizing j with
  | zero => simp [path, steps]
  | succ k ih =>
    rw [List.range'_succ, path, ih (j+1), steps_front]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem cnf_cat (f g : cnf) : encodeCnf (f++g) = encodeCnf f ++ encodeCnf g := by
  induction f with
  | nil => rfl
  | cons c f ih => simp [CnfSerialize.encodeCnf_cons, ih, List.append_assoc]

theorem edge_cells (j k : Nat) :
    encodeCnf [edge j k] = [1,0] ++ ones j ++ [0,1,1] ++ ones k ++ [0,0] := by
  simp [edge, ones, encodeCnf, encodeClause, encodeLit, List.append_assoc]

theorem step_record (s : State) (j h : Nat) (z : List Nat)
    (hc : s.get currentId = ones j) (ha : s.get acc = z) :
    let t := stepEdge.eval (s.set pathIndex (ones h))
    t.get currentId = ones (j+1) ∧ t.get acc = z ++ encodeCnf [edge j (j+1)] := by
  simp_all [stepEdge, edgeLeft, edgeRight, edge_cells, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    regRead, currentId, acc, pathIndex, ones_succ, List.append_assoc]

theorem step_loop (s : State) (j m : Nat) (z : List Nat) (hm : (s.get stream).length = m)
    (hc : s.get currentId = ones j) (ha : s.get acc = z) :
    let t := (Cmd.forBnd pathIndex stream stepEdge).eval s
    t.get currentId = ones (j+m) ∧ t.get acc = z ++ encodeCnf (steps j m) := by
  simp only [Cmd.eval_forBnd, hm]
  refine Cmd.foldlState_range_induct _ _ _ _
    (fun i t => t.get currentId = ones (j+i) ∧ t.get acc = z ++ encodeCnf (steps j i))
    (by simpa [steps, encodeCnf] using And.intro hc ha) ?_
  intro i t _ h
  rw [steps, cnf_cat, ← List.append_assoc]
  exact step_record t (j+i) i _ h.1 h.2

theorem finish_block (t : State) (j m : Nat) (z : List Nat)
    (hj : t.get startId = ones j) (hc : t.get currentId = ones (j+m))
    (hw : t.get width = ones (m+1)) (ha : t.get acc = z) :
    (blockFinish.eval t).get acc = z ++ encodeCnf [edge (j+m) j] ∧
      (blockFinish.eval t).get startId = ones (j+(m+1)) := by
  simp_all [blockFinish, edgeLeft, edgeRight, edge_cells, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    regRead, currentId, startId, width, acc, ones, List.append_assoc]

theorem block_record (s : State) (i m : Nat) (z : List Nat)
    (hj : s.get startId = ones (i*(m+1))) (hm : (s.get stream).length = m)
    (hw : s.get width = ones (m+1)) (ha : s.get acc = z) :
    let t := blockBody.eval (s.set blockIndex (ones i))
    t.get acc = z ++ encodeCnf (block m i) ∧ t.get startId = ones ((i+1)*(m+1)) := by
  let j := i*(m+1)
  let a := (s.set blockIndex (ones i)).set currentId (ones j)
  have am : (a.get stream).length = m := by simpa [a, regRead, stream, currentId, blockIndex] using hm
  have ac : a.get currentId = ones j := State.get_set_eq _ _ _
  have aa : a.get acc = z := by simpa [a, regRead, acc, currentId, blockIndex] using ha
  let t := (Cmd.forBnd pathIndex stream stepEdge).eval a
  obtain ⟨tc,ta⟩ := step_loop a j m z am ac aa
  have tj : t.get startId = ones j := by
    rw [show t.get startId = a.get startId from Cmd.eval_get_of_not_writes _ _ _ (by decide)]
    simpa [a, j, regRead, startId, blockIndex, currentId] using hj
  have tw : t.get width = ones (m+1) := by
    rw [show t.get width = a.get width from Cmd.eval_get_of_not_writes _ _ _ (by decide)]
    simpa [a, regRead, width, blockIndex, currentId] using hw
  obtain ⟨fa,fj⟩ := finish_block t j m _ tj tc tw ta
  have hin : (Cmd.op (.copy currentId startId)).eval (s.set blockIndex (ones i)) = a := by
    simp_all [a, j, Cmd.eval_op, Op.eval, regRead, startId, blockIndex]
  simp only [blockBody, Cmd.eval_seq, hin]
  change (blockFinish.eval t).get acc = _ ∧ (blockFinish.eval t).get startId = _
  rw [block, path_steps, cnf_cat, ← List.append_assoc, Nat.succ_mul]
  exact ⟨fa,fj⟩

theorem links_run (s : State) (m : Nat) (z : List Nat)
    (hj : s.get startId = []) (hm : (s.get stream).length = m)
    (hw : s.get width = ones (m+1)) (ha : s.get acc = z) :
    ((Cmd.forBnd blockIndex width blockBody).eval s).get acc = z ++ encodeCnf (links m (m+1)) := by
  rw [Cmd.eval_forBnd, hw, List.length_replicate]
  let inv := fun i (t : State) =>
    t.get acc = z ++ encodeCnf (links m i) ∧ t.get startId = ones (i*(m+1)) ∧
    (t.get stream).length = m ∧ t.get width = ones (m+1)
  have h0 : inv 0 s := by simpa [inv, links, encodeCnf, ones] using And.intro ha ⟨hj,hm,hw⟩
  apply (Cmd.foldlState_range_induct _ _ _ _ inv h0 ?_).1
  intro i t _ hi
  obtain ⟨ta,tj,tm,tw⟩ := hi
  obtain ⟨fa,fj⟩ := block_record t i m _ tj tm tw ta
  let a := t.set blockIndex (ones i)
  have fs := Cmd.eval_get_of_not_writes blockBody a stream (by decide)
  have fw := Cmd.eval_get_of_not_writes blockBody a width (by decide)
  have fsm : ((blockBody.eval a).get stream).length = m := by
    rw [fs]; simpa [a, regRead, stream, blockIndex] using tm
  have fww : (blockBody.eval a).get width = ones (m+1) := by
    rw [fw]; simpa [a, regRead, width, blockIndex] using tw
  exact ⟨by simpa [links, cnf_cat, List.append_assoc] using fa, fj, fsm, fww⟩

theorem read_formula (x : List Bool) :
    (readFormula.eval (certState x)).get EvalCnfCmd.CNF_STREAM = encodeCnf (SATStr.cnfOf x) := by
  have hin : (Cmd.op (.clear 1)).eval (certState x) = SATStr.strEIn (x, []) := by
    rw [SATStr.strEIn_lit]; rfl
  rw [readFormula, Cmd.eval_seq, hin]
  exact (SATStr.satStrBuild_get x []).2.2.1

theorem finish_formula (t : State) (f : cnf)
    (ta : t.get acc = encodeCnf (rename ((encodeCnf f).length+1) 0 f))
    (ts : t.get stream = encodeCnf f)
    (tw : t.get width = ones ((encodeCnf f).length+1)) :
    (appendLinks.eval t).get acc =
      encodeCnf (split f (encodeCnf f).length ((encodeCnf f).length+1)) := by
  let m := (encodeCnf f).length
  let u := t.set startId []
  have um : (u.get stream).length = m := by
    change ((t.set startId []).get stream).length = _
    rw [State.get_set_ne _ _ _ _ (by decide : stream ≠ startId), show t.get stream = _ from ts]
  have uw : u.get width = ones (m+1) :=
    (State.get_set_ne _ _ _ _ (by decide : width ≠ startId)).trans tw
  have ua : u.get acc = encodeCnf (rename (m+1) 0 f) :=
    (State.get_set_ne _ _ _ _ (by decide : acc ≠ startId)).trans ta
  rw [appendLinks, Cmd.eval_seq, split, cnf_cat]
  exact links_run u m _ (State.get_set_eq t startId []) um uw ua

theorem transform_state (a : State) (f : cnf) (hc : a.get EvalCnfCmd.CNF_STREAM = encodeCnf f) :
    ((rewriteFormula ;; appendLinks).eval a).get acc =
      encodeCnf (split f (encodeCnf f).length ((encodeCnf f).length+1)) := by
  obtain ⟨ta,ts,tw⟩ := after_scan a f hc
  rw [Cmd.eval_seq, rewriteFormula, Cmd.eval_seq]
  exact finish_formula _ f ta ts tw

theorem machine_result (x : List Bool) :
    (program.eval (certState x)).get acc = encodeCnf (outputCnf x) := by
  rw [program, Cmd.eval_seq]
  exact transform_state _ _ (read_formula x)

theorem registers : program.UsesBelow 37 := by
  have h : SATStr.satStrBuild.UsesBelow 37 :=
    Cmd.UsesBelow_mono (by decide : 25 ≤ 37) SATStr.satStrMfc_usesBelow.1
  refine ⟨⟨by change 1 < 37; decide, h⟩, ?_⟩
  simp only [rewriteFormula, appendLinks, scanInit, scanBack, scanFront, buildWidth, scanOne, onSign, onVar, onSlot, setFlag,
    blockBody, blockFinish, stepEdge, edgeLeft, edgeRight, Cmd.UsesBelow, Op.UsesBelow]
  repeat' apply And.intro
  all_goals decide

theorem in_size (x : List Bool) : State.size (certState x) ≤ encodable.size x := by
  rw [State.size_certState]; exact CookLevin.length_le_size _

theorem machine_budget : ∃ b : Nat → Nat, inOPoly b ∧ monotonic b ∧
    ∀ x, program.cost (certState x) ≤ b (encodable.size x) ∧
      encodable.size (transformBits x) ≤ b (encodable.size x) := by
  obtain ⟨K,D,h⟩ := (Cmd.chk_sound program (2^37-1)).2 program_checked
  let q := fun n : Nat => K * (n+1)^D
  have qp : inOPoly q := inOPoly_mul (inOPoly_const K) (FrontWitness.inOPoly_pow_succ D)
  have qm : monotonic q := fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  refine ⟨fun n => q n * (n+1) + 2*(n+q n),
    inOPoly_add (inOPoly_mul qp (inOPoly_add inOPoly_id (inOPoly_const 1)))
      (inOPoly_mul (inOPoly_const 2) (inOPoly_add inOPoly_id qp)), ?_, ?_⟩
  · intro a b hab
    exact Nat.add_le_add (Nat.mul_le_mul (qm a b hab) (Nat.add_le_add_right hab 1))
      (Nat.mul_le_mul_left _ (Nat.add_le_add hab (qm a b hab)))
  · intro x
    let n := encodable.size x
    have cap : ∀ r, ((certState x).get r).length ≤ n :=
      fun r => (State.get_length_le_size _ r).trans (in_size x)
    obtain ⟨ht,hr,_⟩ := h (certState x) n n (fun r _ => cap r) cap
    have hl := hr acc
    rw [machine_result] at hl
    have hlen : (transformBits x).length = (encodeCnf (outputCnf x)).length := by
      rw [← SATToSATStr.strBits_satToStr, strBits_length]; rfl
    have hs := CookLevin.size_le_two_mul_length (transformBits x)
    rw [hlen] at hs
    exact ⟨ht.trans (Nat.le_add_right _ _), (hs.trans (Nat.mul_le_mul_left 2 hl)).trans
      (Nat.le_add_left _ _)⟩

theorem machine : ∃ (t : Nat → Nat) (M : FlatTM),
    inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧
    CookLevin.computesInTime M transformBits t := by
  obtain ⟨b,bp,bm,hb⟩ := machine_budget
  let W : PolyTimeComputableLang transformBits := {
    c := program
    encodeIn := certState
    decodeOut := fun s => boolsOf (s.get acc)
    cost_bound := b
    cost_bound_poly := bp
    cost_bound_mono := bm
    encBound := id
    encBound_poly := inOPoly_id
    encBound_mono := fun _ _ hab => hab
    encodeIn_size := in_size
    computes := fun x => by rw [machine_result]; rfl
    cost_le := fun x => (hb x).1
    output_size_le := fun x => (hb x).2
    enc_bit := fun x reg hreg v hv => by
      have e : reg = strBits x := List.mem_singleton.mp hreg
      exact strBits_bit x v (e ▸ hv)
    regBound := 37
    usesBelow := registers
    width_le := fun _ => by change 1 ≤ 37; decide
    decode_agree := fun x k => by
      have pad : AgreeBelow 37 (certState x ++ List.replicate k []) (certState x) :=
        fun r _ => State.get_append_replicate_nil _ _ r
      exact congrArg boolsOf (Cmd.eval_agree program 37 registers pad acc (by decide)) }
  exact W.toMachine (fun _ => rfl) (fun _ _ => rfl)

end PvsNP.Units.m3_sat_to_3occ_sat

theorem PvsNP.Units.m3_sat_to_3occ_sat :
    CookLevin.reducesPoly SATStr
  (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
    SAT (SATStr.cnfOf x)) := by
  obtain ⟨t,M,ht,hM,h1,hc⟩ := PvsNP.Units.m3_sat_to_3occ_sat.machine
  exact ⟨PvsNP.Units.m3_sat_to_3occ_sat.transformBits,t,M,ht,hM,h1,hc,
    PvsNP.Units.m3_sat_to_3occ_sat.transform_correct⟩
