import SignedTable
import BlockJoin4813

namespace PEqualNP.Outside.L_meta_4813
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_0 : tableBlock sgCheck 11 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_8 : tableBlock sgCheck 11 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_16 : tableBlock sgCheck 11 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_24 : tableBlock sgCheck 11 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_32 : tableBlock sgCheck 11 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_40 : tableBlock sgCheck 11 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_48 : tableBlock sgCheck 11 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_56 : tableBlock sgCheck 11 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_64 : tableBlock sgCheck 11 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_72 : tableBlock sgCheck 11 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_80 : tableBlock sgCheck 11 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_88 : tableBlock sgCheck 11 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_96 : tableBlock sgCheck 11 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_104 : tableBlock sgCheck 11 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_112 : tableBlock sgCheck 11 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_120 : tableBlock sgCheck 11 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_128 : tableBlock sgCheck 11 128 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_136 : tableBlock sgCheck 11 136 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_144 : tableBlock sgCheck 11 144 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_152 : tableBlock sgCheck 11 152 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_160 : tableBlock sgCheck 11 160 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_168 : tableBlock sgCheck 11 168 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_176 : tableBlock sgCheck 11 176 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_184 : tableBlock sgCheck 11 184 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_192 : tableBlock sgCheck 11 192 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_200 : tableBlock sgCheck 11 200 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_208 : tableBlock sgCheck 11 208 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row11_216 : tableBlock sgCheck 11 216 5 = true := by decide +kernel
theorem signedRows11 : tableBlock sgCheck 11 0 221 = true :=
  (@mergeBlock sgCheck 11 0 112 109 (@mergeBlock sgCheck 11 0 56 56 (@mergeBlock sgCheck 11 0 24 32 (@mergeBlock sgCheck 11 0 8 16 row11_0 (@mergeBlock sgCheck 11 8 8 8 row11_8 row11_16)) (@mergeBlock sgCheck 11 24 16 16 (@mergeBlock sgCheck 11 24 8 8 row11_24 row11_32) (@mergeBlock sgCheck 11 40 8 8 row11_40 row11_48))) (@mergeBlock sgCheck 11 56 24 32 (@mergeBlock sgCheck 11 56 8 16 row11_56 (@mergeBlock sgCheck 11 64 8 8 row11_64 row11_72)) (@mergeBlock sgCheck 11 80 16 16 (@mergeBlock sgCheck 11 80 8 8 row11_80 row11_88) (@mergeBlock sgCheck 11 96 8 8 row11_96 row11_104)))) (@mergeBlock sgCheck 11 112 56 53 (@mergeBlock sgCheck 11 112 24 32 (@mergeBlock sgCheck 11 112 8 16 row11_112 (@mergeBlock sgCheck 11 120 8 8 row11_120 row11_128)) (@mergeBlock sgCheck 11 136 16 16 (@mergeBlock sgCheck 11 136 8 8 row11_136 row11_144) (@mergeBlock sgCheck 11 152 8 8 row11_152 row11_160))) (@mergeBlock sgCheck 11 168 24 29 (@mergeBlock sgCheck 11 168 8 16 row11_168 (@mergeBlock sgCheck 11 176 8 8 row11_176 row11_184)) (@mergeBlock sgCheck 11 192 16 13 (@mergeBlock sgCheck 11 192 8 8 row11_192 row11_200) (@mergeBlock sgCheck 11 208 8 5 row11_208 row11_216)))))
end PEqualNP.Outside.L_meta_4813
