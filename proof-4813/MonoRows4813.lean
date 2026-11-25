import MonoTable

namespace PEqualNP.Outside.L_meta_4813

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoRows17 : tableBlock moCheck 17 0 (moCount 17) = true := by decide +kernel

theorem monoChecks (k i : Nat) (hi : i<moTable.1 k) : moCheck k i=true := by
  change i < moCount k at hi
  by_cases hk : k=17
  · subst k
    exact blockAt monoRows17 i (Nat.zero_le i) hi
  · have empty : moCount k=0 := by unfold moCount; split <;> simp_all
    omega

end PEqualNP.Outside.L_meta_4813
