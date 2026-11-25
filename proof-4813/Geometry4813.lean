import Coordinates4813

namespace PEqualNP.Outside.L_meta_4813
open Nine
open PEqualNP.CircuitLowerBounds

theorem embed_raw (pack : Nat) (r : Nine.Row) (i : Fin 10) :
    Nine.Extended.bit (embed9 pack r) (xr i) = Nine.bit r (xs9 pack i) := by
  rw [coord_raw]
  change (BitVec.ofBoolListLE (List.ofFn fun v : Fin 10 => Nine.bit r (xs9 pack v))).getLsbD i.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]

def wordAnd (ws : List Word) := ws.foldr (Nine.Extended.prime false) Nine.Extended.one

def geoDomain (pack : Nat) := wordAnd (List.ofFn fun v : Fin 10 =>
  if xs9 pack v = Nine.zero then ~~~(xr v) else Nine.Extended.one)

theorem geo_dom (pack : Nat) (r : Nine.Row) :
    Nine.Extended.bit (embed9 pack r) (geoDomain pack) = true := by
  rw [geoDomain,wordAnd,fold_bits]
  simp only [GateOp.eval,List.all_eq_true]
  intro b hb
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hw
  split_ifs with hz
  · change Nine.Extended.bit (embed9 pack r) (Nine.Extended.neg (xr v)) = true
    rw [Nine.Extended.bit_neg,embed_raw,hz,Nine.bit_zero]
    rfl
  · exact Nine.Extended.bit_one _

def graphWord9 (w : Fin 10 → Nine.Sig) : Nine.Sig :=
  (w 0 &&& w 1) ||| (w 1 &&& w 2) ||| (w 2 &&& w 3) ||| (w 3 &&& w 4) ||| (w 4 &&& w 0) |||
  (w 0 &&& w 5) ||| (w 1 &&& w 6) ||| (w 2 &&& w 7) ||| (w 3 &&& w 8) ||| (w 4 &&& w 9) |||
  (w 5 &&& w 7) ||| (w 7 &&& w 9) ||| (w 9 &&& w 6) ||| (w 6 &&& w 8) ||| (w 8 &&& w 5)

theorem geo_target (pack : Nat) :
    Nine.restrictRows (embed9 pack) (Nine.Extended.observe wordTarget) =
    Nine.observe (graphWord9 (xs9 pack)) := by
  funext r
  change Nine.Extended.bit (embed9 pack r) wordTarget = _
  rw [target_bit]
  have eq : rawBit (embed9 pack r) = fun i => Nine.bit r (xs9 pack i) := funext (embed_raw pack r)
  rw [eq]
  simp only [edgeFn, Nine.Extended.f10, graphWord9, Nine.observe, Nine.bit,
    BitVec.getLsbD_or,BitVec.getLsbD_and]

def floor9 (u : Bool) (q : Nat) : Nat :=
  if q=511 then (if u then 15 else 16) else Nine.boundsBefore Nine.known383 q

theorem floor9_ok (mono9 : Nine.Lower false Nine.inputs Nine.graph 16) (u : Bool) (q : Nat) :
    Nine.Lower u (Nine.varsX q) (Nine.graphGoal q) (floor9 u q) := by
  by_cases he : q=511
  · subst q
    rw [show Nine.varsX 511=Nine.inputs by decide +kernel,
        show Nine.graphGoal 511=Nine.graph by decide +kernel]
    cases u
    · exact mono9
    · exact Nine.nineFloor
  · rw [floor9,if_neg he]
    exact Nine.lower_down (Nine.before_sound Nine.known383 Nine.valid383 q)

def geomOK (u : Bool) (g : Geometry) :=
  let (q,pack,L) := g
  decide (L ≤ floor9 u q) && (graphWord9 (xs9 pack) == Nine.graphGoal q) &&
    Nine.properB (Nine.graphGoal q) &&
    (List.ofFn (xs9 pack)).all (fun c => c == Nine.zero || (Nine.varsX q).contains c)

theorem geom_sound (mono9 : Nine.Lower false Nine.inputs Nine.graph 16) {u}
    (g : Geometry) (h : geomOK u g=true) :
    Nine.Extended.Slice u rawCols wordTarget (geoDomain g.2.1) g.2.2 := by
  obtain ⟨q,pack,L⟩ := g
  simp only [geomOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  have eq := (geo_target pack).trans (congrArg Nine.observe h.1.1.2)
  refine ⟨embed9 pack,Nine.varsX q,geo_dom pack,?_,eq ▸ Nine.observe_proper (Nine.proper_of _ h.1.2),?_⟩
  · have raw : List.ofFn xr = rawCols := rfl
    intro a ha
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp (show a ∈ List.ofFn xr by rwa [raw])
    have val : Nine.restrictRows (embed9 pack) (Nine.Extended.observe (xr v)) =
        Nine.observe (xs9 pack v) := funext (fun r => embed_raw pack r v)
    rw [val]
    have m := List.all_eq_true.mp h.2 _ (List.mem_ofFn.mpr ⟨v,rfl⟩)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem] at m
    rcases m with hz | hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ funext Nine.bit_zero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,of_decide_eq_true hm,rfl⟩)
  · rw [eq]
    intro p bank reach avail
    exact h.1.1.1.trans (floor9_ok mono9 u q p bank reach avail)

end PEqualNP.Outside.L_meta_4813
