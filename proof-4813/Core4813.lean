import PNPBase

namespace PEqualNP.Outside.L_meta_4813
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := Nine.Extended.Sig
abbrev TRow := Nine.Extended.Row

def inputAt (x : Fin 10 → Bool) (enable : Bool) (pins : List (Fin 12)) :=
  let pres := List.ofFn x ++ [enable && (x 0 && x 2)]
  pres ++ [GateOp.and.eval (pins.map fun j => pres.getD j.val false)]

def edgeFn (x : Fin 10 → Bool) := Nine.Extended.f10 x

def rawCols : List Word :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
   0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
   0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

def rawBit (r : TRow) (v : Fin 10) : Bool :=
  Nine.Extended.bit r (rawCols.getD v.val Nine.Extended.zero)

def wordTarget : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

theorem target_as_gates : wordTarget = (rawCols.getD 0 Nine.Extended.zero &&& rawCols.getD 1 Nine.Extended.zero) ||| (rawCols.getD 1 Nine.Extended.zero &&& rawCols.getD 2 Nine.Extended.zero) ||| (rawCols.getD 2 Nine.Extended.zero &&& rawCols.getD 3 Nine.Extended.zero) ||| (rawCols.getD 3 Nine.Extended.zero &&& rawCols.getD 4 Nine.Extended.zero) ||| (rawCols.getD 4 Nine.Extended.zero &&& rawCols.getD 0 Nine.Extended.zero) ||| (rawCols.getD 0 Nine.Extended.zero &&& rawCols.getD 5 Nine.Extended.zero) ||| (rawCols.getD 1 Nine.Extended.zero &&& rawCols.getD 6 Nine.Extended.zero) ||| (rawCols.getD 2 Nine.Extended.zero &&& rawCols.getD 7 Nine.Extended.zero) ||| (rawCols.getD 3 Nine.Extended.zero &&& rawCols.getD 8 Nine.Extended.zero) ||| (rawCols.getD 4 Nine.Extended.zero &&& rawCols.getD 9 Nine.Extended.zero) ||| (rawCols.getD 5 Nine.Extended.zero &&& rawCols.getD 7 Nine.Extended.zero) ||| (rawCols.getD 7 Nine.Extended.zero &&& rawCols.getD 9 Nine.Extended.zero) ||| (rawCols.getD 9 Nine.Extended.zero &&& rawCols.getD 6 Nine.Extended.zero) ||| (rawCols.getD 6 Nine.Extended.zero &&& rawCols.getD 8 Nine.Extended.zero) ||| (rawCols.getD 8 Nine.Extended.zero &&& rawCols.getD 5 Nine.Extended.zero) := by decide +kernel

theorem target_bit (r : TRow) : Nine.Extended.bit r wordTarget = edgeFn (rawBit r) := by
  rw [target_as_gates]
  simp only [Nine.Extended.bit,BitVec.getLsbD_or,BitVec.getLsbD_and,edgeFn,
    Nine.Extended.f10,rawBit]
  rfl

def makeBank (enable : Bool) (pins : List (Fin 12)) : List Word :=
  let pres := rawCols ++ [if enable then rawCols.getD 0 0 &&& rawCols.getD 2 0 else 0]
  pres ++ [(pins.map (fun j => pres.getD j.val 0)).foldr (Nine.Extended.prime false) Nine.Extended.one]

theorem fold_bits (r : TRow) (xs : List Word) :
    Nine.Extended.bit r (xs.foldr (Nine.Extended.prime false) Nine.Extended.one) =
      GateOp.and.eval (xs.map (Nine.Extended.bit r)) := by
  induction xs with
  | nil => exact Nine.Extended.bit_one _
  | cons a t ih =>
    change Nine.Extended.bit r (Nine.Extended.prime false a _) = (_ && _)
    rw [Nine.Extended.bit_prime,ih]
    rfl

theorem raw_bits (r : TRow) : rawCols.map (Nine.Extended.bit r) = List.ofFn (rawBit r) := by
  have h : List.ofFn (fun j : Fin 10 => rawCols.getD j.val Nine.Extended.zero) = rawCols := rfl
  conv_lhs => rw [←h,List.map_ofFn]
  rfl

theorem bank_bits (v : Bool) (ps : List (Fin 12)) (r : TRow) :
    (makeBank v ps).map (Nine.Extended.bit r) = inputAt (rawBit r) v ps := by
  let w := if v then rawCols.getD 0 0 &&& rawCols.getD 2 0 else (0 : Word)
  have ew : Nine.Extended.bit r w = (v && (rawBit r 0 && rawBit r 2)) := by
    cases v <;> simp [w,rawBit,Nine.Extended.bit,Nine.Extended.zero,BitVec.getLsbD_and]
  have hp : (rawCols ++ [w]).map (Nine.Extended.bit r) =
      List.ofFn (rawBit r) ++ [v && (rawBit r 0 && rawBit r 2)] := by
    simp only [List.map_append, List.map_cons, List.map_nil,raw_bits,ew]
  change ((rawCols ++ [w]) ++ [_]).map _ = _
  rw [List.map_append,hp]
  simp only [inputAt,List.map_cons,List.map_nil,fold_bits,List.map_map]
  congr 2
  apply congrArg GateOp.and.eval
  apply List.map_congr_left
  intro i _
  change Nine.Extended.bit r ((rawCols ++ [w]).getD i.val Nine.Extended.zero) = _
  rw [←Nine.Extended.b_read, hp]

theorem target_proper : Nine.Extended.proper wordTarget := by
  unfold Nine.Extended.proper
  decide +kernel

theorem live_of_correct (u enable : Bool) (ps : List (Fin 12)) (C : Circuit)
    (legal : FanInTwo C) (mono : u=false → ∀ g ∈ C.gates, Nine.Extended.isNot g=false)
    (correct : ∀ x, C.eval (inputAt x enable ps) = edgeFn x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !Nine.Extended.isNot g) ∧
      Nine.Extended.Live u wordTarget k S ∧
      ∀ a ∈ S, a ∈ (makeBank enable ps).map (Nine.Extended.nrm u) := by
  let w := makeBank enable ps
  have he : (Nine.Extended.execute C.gates w).getD C.output Nine.Extended.zero = wordTarget := by
    apply Nine.Extended.bit_ext
    intro r
    rw [←Nine.Extended.b_read,Nine.Extended.execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (w.map (Nine.Extended.bit r))).getD C.output false = _
    rw [show w.map (Nine.Extended.bit r) = inputAt (rawBit r) enable ps from bank_bits _ _ _,target_bit]
    exact correct _
  have out := Nine.Extended.get_rep (u:=u) (Nine.Extended.execute C.gates w) C.output
  rw [he] at out
  unfold Nine.Extended.Repr at out
  have base : Nine.Extended.bit 0 wordTarget = false := by decide +kernel
  rw [Nine.Extended.nrm_id base] at out
  exact Nine.Extended.extract C.gates w legal mono target_proper
    (out.resolve_right (fun h => h target_proper))

end PEqualNP.Outside.L_meta_4813
