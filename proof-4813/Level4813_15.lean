import SignedTable
import BlockJoin4813

namespace PEqualNP.Outside.L_meta_4813
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row15_0 : tableBlock sgCheck 15 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row15_8 : tableBlock sgCheck 15 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row15_16 : tableBlock sgCheck 15 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row15_24 : tableBlock sgCheck 15 24 2 = true := by decide +kernel
theorem signedRows15 : tableBlock sgCheck 15 0 26 = true :=
  (@mergeBlock sgCheck 15 0 16 10 (@mergeBlock sgCheck 15 0 8 8 row15_0 row15_8) (@mergeBlock sgCheck 15 16 8 2 row15_16 row15_24))
end PEqualNP.Outside.L_meta_4813
