import SignedTable
import BlockJoin4813

namespace PEqualNP.Outside.L_meta_4813
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_0 : tableBlock sgCheck 14 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_8 : tableBlock sgCheck 14 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_16 : tableBlock sgCheck 14 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_24 : tableBlock sgCheck 14 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_32 : tableBlock sgCheck 14 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_40 : tableBlock sgCheck 14 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_48 : tableBlock sgCheck 14 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_56 : tableBlock sgCheck 14 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_64 : tableBlock sgCheck 14 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_72 : tableBlock sgCheck 14 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_80 : tableBlock sgCheck 14 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_88 : tableBlock sgCheck 14 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_96 : tableBlock sgCheck 14 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_104 : tableBlock sgCheck 14 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_112 : tableBlock sgCheck 14 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_120 : tableBlock sgCheck 14 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row14_128 : tableBlock sgCheck 14 128 3 = true := by decide +kernel
theorem signedRows14 : tableBlock sgCheck 14 0 131 = true :=
  (@mergeBlock sgCheck 14 0 64 67 (@mergeBlock sgCheck 14 0 32 32 (@mergeBlock sgCheck 14 0 16 16 (@mergeBlock sgCheck 14 0 8 8 row14_0 row14_8) (@mergeBlock sgCheck 14 16 8 8 row14_16 row14_24)) (@mergeBlock sgCheck 14 32 16 16 (@mergeBlock sgCheck 14 32 8 8 row14_32 row14_40) (@mergeBlock sgCheck 14 48 8 8 row14_48 row14_56))) (@mergeBlock sgCheck 14 64 32 35 (@mergeBlock sgCheck 14 64 16 16 (@mergeBlock sgCheck 14 64 8 8 row14_64 row14_72) (@mergeBlock sgCheck 14 80 8 8 row14_80 row14_88)) (@mergeBlock sgCheck 14 96 16 19 (@mergeBlock sgCheck 14 96 8 8 row14_96 row14_104) (@mergeBlock sgCheck 14 112 8 11 row14_112 (@mergeBlock sgCheck 14 120 8 3 row14_120 row14_128)))))
end PEqualNP.Outside.L_meta_4813
