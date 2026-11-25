import Roots4813
import MonoTable
import SignedTable

namespace PEqualNP.Outside.L_meta_4813

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mono_root_data : ∀ b ∈ possibleB false, rootChecks false moSamples moTable 17 b = true :=
  List.all_eq_true.mp (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signed_root_data : ∀ b ∈ possibleB true, rootChecks true sgSamples sgTable 16 b = true :=
  List.all_eq_true.mp (by decide +kernel)

end PEqualNP.Outside.L_meta_4813
