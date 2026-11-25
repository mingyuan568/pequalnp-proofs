import Core4813

namespace PEqualNP.Outside.L_meta_4813
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def BusLe (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j, a.getD j false = true → b.getD j false = true

theorem append_bit {a b : List Bool} {x y : Bool} (ab : BusLe a b) (xy : x=true → y=true) :
    BusLe (a++[x]) (b++[y]) := by
  obtain ⟨len,sub⟩ := ab
  refine ⟨by simp [len],?_⟩
  intro j
  by_cases small : j<a.length
  · rw [List.getD_append _ _ _ _ small,
        List.getD_append _ _ _ _ (show j<b.length by omega)]
    exact sub j
  · rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ j), len]
    cases j - b.length with
    | zero => exact xy
    | succ n => simp

theorem and_bus {a b : List Bool} (ab : BusLe a b) (ports : List Nat) :
    GateOp.and.eval (ports.map fun i => a.getD i false) = true →
    GateOp.and.eval (ports.map fun i => b.getD i false) = true := by
  simp only [GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,
    and_imp,forall_apply_eq_imp_iff₂, id_eq]
  intro h i hi
  exact ab.2 i (h i hi)

theorem or_bus {a b : List Bool} (ab : BusLe a b) (ports : List Nat) :
    GateOp.or.eval (ports.map fun i => a.getD i false) = true →
    GateOp.or.eval (ports.map fun i => b.getD i false) = true := by
  simp only [GateOp.eval,List.any_eq_true,List.mem_map, id_eq]
  rintro ⟨v,⟨i,hi,rfl⟩,h⟩
  exact ⟨_,⟨i,hi,rfl⟩,ab.2 i h⟩

theorem monotone_wires (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (a b : List Bool) (ab : BusLe a b) :
    BusLe ((⟨gs,0⟩ : Circuit).wires a) ((⟨gs,0⟩ : Circuit).wires b) := by
  induction gs generalizing a b with
  | nil => exact ab
  | cons g tail ih =>
    apply ih (fun v hv => ops v (List.mem_cons_of_mem _ hv))
    apply append_bit ab
    rcases ops g (by simp) with h|h
    · rw [h]; exact and_bus ab _
    · rw [h]; exact or_bus ab _

theorem smaller_eval {C : Circuit} (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    {a b : List Bool} (ab : BusLe a b) :
    C.eval a = true → C.eval b = true :=
  (monotone_wires C.gates ops a b ab).2 C.output

theorem inputAt_mono {x y : Fin 10 → Bool} {u v : Bool}
    (sub : ∀ i, x i=true → y i=true)
    (s : (u && (x 0 && x 2))=true → (v && (y 0 && y 2))=true)
    (ps : List (Fin 12)) : BusLe (inputAt x u ps) (inputAt y v ps) := by
  have raw : BusLe (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro j
    by_cases h : j < 10
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,↓reduceDIte,
        Option.getD_some]
      exact sub ⟨j,h⟩
    · simp [List.getD_eq_getElem?_getD,h]
  have pres := append_bit raw s
  apply append_bit pres
  simpa only [List.map_map,Function.comp_def] using and_bus pres (ps.map Fin.val)

def subRow (s r : TRow) :=
  rawCols.all (fun w => !(Nine.Extended.bit s w) || Nine.Extended.bit r w)

def edgeRows : List TRow :=
  [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem graph_witnesses : ∀ r : TRow,
    (!(Nine.Extended.bit r wordTarget) || edgeRows.any (fun s =>
      Nine.Extended.bit s wordTarget && !(rawBit s 0 && rawBit s 2) && subRow s r)) = true := by
  decide +kernel

theorem subRow_sound {s r : TRow} (h : subRow s r=true) (i : Fin 10) :
    rawBit s i=true → rawBit r i=true := by
  have hlen : i.val < rawCols.length := i.isLt
  have hm : rawCols.getD i.val Nine.Extended.zero ∈ rawCols := by
    simp [List.getD_eq_getElem?_getD,hlen]
  have hv := List.all_eq_true.mp h _ hm
  change ((!rawBit s i) || rawBit r i)=true at hv
  intro hs
  simpa [hs] using hv

theorem bypass_rows {C : Circuit} (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (ps : List (Fin 12)) (ok : ∀ x, C.eval (inputAt x true ps) = edgeFn x) (r : TRow) :
    C.eval (inputAt (rawBit r) false ps) = edgeFn (rawBit r) := by
  rw [←target_bit]
  cases h : Nine.Extended.bit r wordTarget with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro bad
    have toFull := inputAt_mono (x:=rawBit r) (y:=rawBit r) (u:=false) (v:=true)
      (fun _ z => z) (by simp) ps
    have lit := smaller_eval ops toFull bad
    rw [ok,←target_bit,h] at lit
    contradiction
  | true =>
    have witness := graph_witnesses r
    simp only [h,Bool.not_true,Bool.false_or,List.any_eq_true] at witness
    obtain ⟨s,_,hs⟩ := witness
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hs
    have sub := inputAt_mono (u:=true) (v:=false) (subRow_sound hs.2)
      (by simp [hs.1.2]) ps
    apply smaller_eval ops sub
    rw [ok,←target_bit,hs.1.1]

end PEqualNP.Outside.L_meta_4813
