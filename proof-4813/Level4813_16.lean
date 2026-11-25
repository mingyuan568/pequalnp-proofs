import SignedTable
import BlockJoin4813

namespace PEqualNP.Outside.L_meta_4813
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_0 : tableBlock sgCheck 16 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_8 : tableBlock sgCheck 16 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_16 : tableBlock sgCheck 16 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_24 : tableBlock sgCheck 16 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_32 : tableBlock sgCheck 16 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row16_40 : tableBlock sgCheck 16 40 2 = true := by decide +kernel
theorem signedRows16 : tableBlock sgCheck 16 0 42 = true :=
  (@mergeBlock sgCheck 16 0 24 18 (@mergeBlock sgCheck 16 0 8 16 row16_0 (@mergeBlock sgCheck 16 8 8 8 row16_8 row16_16)) (@mergeBlock sgCheck 16 24 8 10 row16_24 (@mergeBlock sgCheck 16 32 8 2 row16_32 row16_40)))
end PEqualNP.Outside.L_meta_4813
