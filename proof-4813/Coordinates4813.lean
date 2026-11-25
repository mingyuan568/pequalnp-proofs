import TenVerifier

namespace PEqualNP.Outside.L_meta_4813
open Nine
open PEqualNP.CircuitLowerBounds

abbrev Geometry := Nat × Nat × Nat
def label9 (pack : Nat) (v : Fin 10) := (pack >>> (4*v.val)) &&& 15
def xs9 (pack : Nat) (v : Fin 10) := Nine.inputs.getD (label9 pack v) Nine.zero
def xr (v : Fin 10) := rawCols.getD v.val Nine.Extended.zero

def embed9 (pack : Nat) (r : Nine.Row) : TRow :=
  (BitVec.ofBoolListLE (List.ofFn fun v : Fin 10 => Nine.bit r (xs9 pack v))).toFin.cast
    (by simp [List.length_ofFn])

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coord_raw : ∀ (i : Fin 10) (r : TRow),
    Nine.Extended.bit r (xr i) = r.val.testBit i.val := by decide +kernel


end PEqualNP.Outside.L_meta_4813
