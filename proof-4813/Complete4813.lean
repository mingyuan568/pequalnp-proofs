import Conditional4813
import RootData4813
import SignedRowsAll
import MonoRows4813
import MonoFloor4813

namespace PEqualNP.Outside.L_meta_4813

def samplesFor (u : Bool) := if u then sgSamples else moSamples
def tableFor (u : Bool) := if u then sgTable else moTable

theorem checkedCases (u : Bool) (i : Nat) (hi : i<(tableFor u).1 (capFor u)) :
    Nine.Extended.Impossible u wordTarget (capFor u)
      (stateWords (samplesFor u) (tableFor u) (capFor u) i).toFinset := by
  cases u
  · exact all_good mono_floor_official moGeoOK moSamplesOK monoChecks _ _ hi
  · exact all_good mono_floor_official sgGeoOK sgSamplesOK signedChecks _ _ hi

theorem checkedRoots (u : Bool) : ∀ b ∈ possibleB u,
    rootChecks u (samplesFor u) (tableFor u) (capFor u) b=true := by
  cases u
  · exact mono_root_data
  · exact signed_root_data

end PEqualNP.Outside.L_meta_4813

open PEqualNP.Outside.L_meta_4813 in
theorem PEqualNP.Outside.L_meta_4813 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  classical
  intro C pins legal size arity
  by_contra! full
  apply exclude_from_tables samplesFor tableFor checkedCases checkedRoots C pins legal size arity
  intro x
  by_contra bad
  apply full x
  simpa only [inputAt,edgeFn,Nine.Extended.f10,Bool.true_and] using bad
