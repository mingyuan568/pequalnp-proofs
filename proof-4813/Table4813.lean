import Geometry4813
import Symmetry4813

namespace PEqualNP.Outside.L_meta_4813
open Nine.Extended

abbrev ProofRow := Nat × Nat × Nat × List (Nat × Nat) × Bool
abbrev ProofTable := (Nat → Nat) × (Nat → Nat → ProofRow) × (Nat → Nat → Option Nat)
abbrev Samples := List Signals

def sampleAt (s : Samples) (p : Bool) (j : Fin 7980) : TRow :=
  (BitVec.ofBoolListLE (List.ofFn (fun v : Fin 10 =>
    ((if p then (s.getD v.val (0,0)).1 else (s.getD v.val (0,0)).2)).getLsbD j.val))).toFin.cast
    (by simp [List.length_ofFn])

def rawDecor10 (s : Samples) : List Decor :=
  List.ofFn fun v : Fin 10 => (xr v, s.getD v.val (0,0))

theorem sampleAt_bit (s : Samples) (p : Bool) (j : Fin 7980) (v : Fin 10) :
    bit (sampleAt s p j) (xr v) =
      (if p then (s.getD v.val (0,0)).1 else (s.getD v.val (0,0)).2).getLsbD j.val := by
  rw [coord_raw]
  change (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 10 =>
    (if p then (s.getD i.val (0,0)).1 else (s.getD i.val (0,0)).2).getLsbD j.val))).getLsbD v.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,v.isLt,↓reduceDIte,Option.getD_some]

theorem raw_good (s : Samples) : ∀ a ∈ rawDecor10 s, faithful (sampleAt s true) (sampleAt s false) a := by
  intro a ha
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    exact (sampleAt_bit s true ⟨j,hj⟩ v).symm.trans (ofRows_bit _ _ ⟨j,hj⟩).symm
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    exact (sampleAt_bit s false ⟨j,hj⟩ v).symm.trans (ofRows_bit _ _ ⟨j,hj⟩).symm

def graphBits (b : Fin 10 → Bits) :=
  (b 0 &&& b 1) ||| (b 1 &&& b 2) ||| (b 2 &&& b 3) ||| (b 3 &&& b 4) ||| (b 4 &&& b 0) |||
  (b 0 &&& b 5) ||| (b 1 &&& b 6) ||| (b 2 &&& b 7) ||| (b 3 &&& b 8) ||| (b 4 &&& b 9) |||
  (b 5 &&& b 7) ||| (b 7 &&& b 9) ||| (b 9 &&& b 6) ||| (b 6 &&& b 8) ||| (b 8 &&& b 5)

def sampleOK (s : Samples) :=
  graphBits (fun v => (s.getD v.val (0,0)).1) == BitVec.allOnes 7980 &&
  graphBits (fun v => (s.getD v.val (0,0)).2) == 0

theorem samples_valid {s : Samples} (h : sampleOK s=true) :
    properPairs wordTarget (sampleAt s true) (sampleAt s false) := by
  simp only [sampleOK,Bool.and_eq_true,beq_iff_eq] at h
  have val (p : Bool) (j : Fin 7980) :
      bit (sampleAt s p j) wordTarget =
        (graphBits (fun v => if p then (s.getD v.val (0,0)).1 else (s.getD v.val (0,0)).2)).getLsbD j.val := by
    rw [target_bit]
    change edgeFn (fun i => bit (sampleAt s p j) (xr i)) = _
    simp only [edgeFn,f10,sampleAt_bit,graphBits,BitVec.getLsbD_or,BitVec.getLsbD_and]
  intro j
  rw [val,val]
  change (graphBits (fun v => (s.getD v.val (0,0)).1)).getLsbD j.val = true ∧
    (graphBits (fun v => (s.getD v.val (0,0)).2)).getLsbD j.val = false
  rw [h.1,h.2]
  exact ⟨BitVec.getLsbD_allOnes.trans (decide_eq_true j.isLt),BitVec.getLsbD_zero⟩

def replay (n ops : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | n+1 =>
    let a := ws.getD (ops &&& 31) defaultDecor
    let b := ws.getD ((ops >>> 5) &&& 31) defaultDecor
    replay n (ops >>> 12) (ws ++ [dbin ((ops >>> 10) &&& 3) a b])

theorem replay_good (n ops : Nat) (ws : List Decor) (r s : Fin 7980 → TRow)
    (base : ∀ v ∈ ws, faithful r s v) : ∀ v ∈ replay n ops ws, faithful r s v := by
  induction n generalizing ws ops with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def chosen (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let rest := chosen bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then rest else
      (((ops >>> 10) &&& 3),(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD ((ops >>> 5) &&& 31) defaultDecor).1) :: rest

def rowBank (s : Samples) (r : ProofRow) := replay r.1 r.2.1 (rawDecor10 s)
def rowWires (s : Samples) (r : ProofRow) := Nine.selectLive r.2.2.1 (rowBank s r)
def stateWords (s : Samples) (t : ProofTable) (k i : Nat) :=
  (rowWires s (t.2.1 k i)).map Prod.fst

def rowPools (u : Bool) (gs : List Geometry) (s : Samples) (r : ProofRow) :=
  r.2.2.2.1.filterMap fun (idx,paid) =>
    gs[idx]?.bind fun g => materialize u rawCols (chosen (rowBank s r) r.2.1 paid r.1)
      (geoDomain g.2.1) g.2.2

theorem pools_good (mono9 : Nine.Lower false Nine.inputs Nine.graph 16) {u gs}
    (gh : ∀ g ∈ gs, geomOK u g = true) (s : Samples) (r : ProofRow) :
    ∀ p ∈ rowPools u gs s r, ValidPool u rawCols wordTarget p := by
  intro p hp
  obtain ⟨⟨idx,paid⟩,_,hh⟩ := List.mem_filterMap.mp hp
  obtain ⟨g,hg,hm⟩ := Option.bind_eq_some_iff.mp hh
  exact materialize_sound (geom_sound mono9 _ (gh g (List.mem_of_getElem? hg))) hm

def lookup (s : Samples) (t : ProofTable) (k tag : Nat) : List (List Word) :=
  ((t.2.2 k tag).bind (fun code => if code/4<t.1 k then some (symWords (code%4) (stateWords s t k (code/4))) else none)).toList

def directCut (u : Bool) (k : Nat) (ws : List Word) (b : BoundPool) :=
  ws.all (availableB u b.domain b.wires) &&
    decide (k+b.paid < b.bound+ws.countP (isMaskedConstant b.domain))

theorem direct_good {u k ws b} (v : ValidPool u rawCols wordTarget b)
    (nd : ws.Nodup) (ok : directCut u k ws b=true) : Impossible u wordTarget k ws.toFinset := by
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := v
  simp only [directCut,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro l hl run
  have supply : Nine.supply u bank ((ws.map observe).map (Nine.restrictRows f)) := by
    intro a ha
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (ok.1 w hw)
  have bound := Nine.projected_bound f (list_run run ws nd rfl) nc hp supply lo
  have count := count_constants dom ws
  omega

def checkRow (u : Bool) (gs : List Geometry) (s : Samples) (t : ProofTable) (k i : Nat) :=
  let r := t.2.1 k i
  let ws := rowWires s r
  let words := ws.map Prod.fst
  let pools := rowPools u gs s r
  decide words.Nodup && !(words.contains wordTarget) &&
  (if r.2.2.2.2 then pools.any (directCut u k words)
   else if k=0 then true else testAll (k,ws.length,ws,preCov u ws,pools,lookup s t (k-1)) ws)

theorem check_good (mono9 : Nine.Lower false Nine.inputs Nine.graph 16) {u gs s t k i}
    (geo : ∀ g ∈ gs, geomOK u g=true) (samples : sampleOK s=true)
    (prior : k>0 → ∀ j<t.1 (k-1), Impossible u wordTarget (k-1) (stateWords s t (k-1) j).toFinset)
    (ok : checkRow u gs s t k i=true) : Impossible u wordTarget k (stateWords s t k i).toFinset := by
  simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at ok
  have out : wordTarget ∉ stateWords s t k i := by simpa [stateWords] using ok.1.2
  have good := pools_good mono9 geo s (t.2.1 k i)
  by_cases direct : (t.2.1 k i).2.2.2.2 = true
  · obtain ⟨b,hb,cut⟩ := List.any_eq_true.mp (show _ from by simpa only [direct,if_true] using ok.2)
    exact direct_good (good b hb) ok.1.1 cut
  by_cases hz : k=0
  · subst k
    intro l hl h
    have e : l=0 := by omega
    subst l
    generalize eq : (stateWords s t 0 i).toFinset = S at h
    obtain ⟨hs,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [eq,hs]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=rawCols) (samples_valid samples) _ ok.1.1 out good _
    (by simpa only [if_neg direct,if_neg hz] using ok.2)
  · intro w hw
    apply replay_good _ _ _ _ _ (raw_good s)
    exact (Nine.selectLive_sub _ _).subset hw
  · intro tag xs hx
    have hm : ((t.2.2 (k-1) tag).bind (fun code => if code/4<t.1 (k-1) then some (symWords (code%4) (stateWords s t (k-1) (code/4))) else none)) = some xs := by
      simpa [lookup] using hx
    obtain ⟨j,_,hj⟩ := Option.bind_eq_some_iff.mp hm
    split at hj
    · next h => cases hj; exact symWords_ok (prior (by omega) (j/4) h) _
    · contradiction

end PEqualNP.Outside.L_meta_4813
