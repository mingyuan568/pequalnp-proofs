import Level4813_11
import Level4813_12
import Level4813_13
import Level4813_14
import Level4813_15
import Level4813_16

namespace PEqualNP.Outside.L_meta_4813

theorem signedChecks (k i : Nat) (hi : i<sgTable.1 k) : sgCheck k i=true := by
  change i<sgCount k at hi
  by_cases he11 : k=11
  · subst k
    exact blockAt signedRows11 i (Nat.zero_le i) hi
  by_cases he12 : k=12
  · subst k
    exact blockAt signedRows12 i (Nat.zero_le i) hi
  by_cases he13 : k=13
  · subst k
    exact blockAt signedRows13 i (Nat.zero_le i) hi
  by_cases he14 : k=14
  · subst k
    exact blockAt signedRows14 i (Nat.zero_le i) hi
  by_cases he15 : k=15
  · subst k
    exact blockAt signedRows15 i (Nat.zero_le i) hi
  by_cases he16 : k=16
  · subst k
    exact blockAt signedRows16 i (Nat.zero_le i) hi
  have empty : sgCount k=0 := by unfold sgCount; split <;> simp_all
  omega

end PEqualNP.Outside.L_meta_4813
