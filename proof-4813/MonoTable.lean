import Pack4813

namespace PEqualNP.Outside.L_meta_4813
open Nine.Extended
def moSamples : Samples := [((-0xe3fa7f1df3ffdbf7573f1),(-0xf3fc7f9fe3ffffff861f9)),((-0xcbf37e5ffefd3d5d77f87),0x300c03800001c1e780038),(0x60180004e0064a20113d0,0x40300000600e1e0001fc0),(0xc0002c00a014004556280,0x8000040180300007fe000),(0xc108420490155902402,0x40180200c01ff800000),(0x80052080869200020804,0xffe00000000),(0x12201011300808200020,0x3ff00000000000),(0x210121c4021080001100,0x1ffc0000000000000),(0x802264000248000444000,0x7fe0000000000000000),(0x3c000111080111000000,0xff8000000000000000000)]
def moGeometry : List Geometry := [(511,0x3782549610,16),(511,0x8936457210,16),(511,0x6789512340,16),(511,0x8253761049,16),(511,0x2873516940,16),(511,0x7825396104,16),(511,0x7392458610,16),(511,0x9876543210,16),(511,0x2537810496,16),(511,0x8765932104,16)]
def moD17 (i : Nat) : Nat := 0x3fff12881087ff8834084fffc48e0421ffe20702137ff0e381083ff861c0841ffc28e0420ffe1070210fff1018108bff860c0841ffc1860421ffe20102117ff0c081097ff84040841ffc1820424ffe0810211fff0208108b14a8241ffe120b2ea29e65089dfe755ac60d5a4c50837cb6234640ec00
def moH17 (i : Nat) : Nat := 0x12a872fd5680000aea820000000004e520f7e1e00000000000000b5781bf8c4458b40c39903524a0e80c065e6acb6a714a811bd14000001d07df6a455bc971dc46dd66390c2b35f800001ae200000208c9b75081796c9e4f1551db461f6814911ad0070f1e53200001d9a537b8c9228dd5d0c0000000003549a8a27b35a76e14c3899bbbf4b368020f0700000082211000100c42020000a48508020
def moCount : Nat → Nat
  | 17 => 18
  | _ => 0
def moEntry : Nat → Nat → ProofRow
  | 17 => fun i => unpackRow 4 moD17 (180+Nine.packedAt moD17 (i*10) 10)
  | _ => fun _ => (0,0,0,[],false)
def moIndex : Nat → Nat → Option Nat
  | 17 => quickLookup 24 59 5 19 7 moH17
  | _ => fun _ => none
def moTable : ProofTable := (moCount,moEntry,moIndex)
def moCheck := checkRow false moGeometry moSamples moTable
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moGeoOK : ∀ g ∈ moGeometry, geomOK false g = true := List.all_eq_true.mp (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moSamplesOK : sampleOK moSamples=true := by decide +kernel
end PEqualNP.Outside.L_meta_4813
