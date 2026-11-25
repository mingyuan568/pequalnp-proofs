import Table4813

namespace PEqualNP.Outside.L_meta_4813

def poolCodes (get : Nat → Nat) (cw depth : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | n+1,pos => (Nine.packedAt get pos cw,Nine.packedAt get (pos+cw) depth) ::
      poolCodes get cw depth n (pos+cw+depth)

def unpackRow (cw : Nat) (get : Nat → Nat) (base : Nat) : ProofRow :=
  let depth := Nine.packedAt get base 5
  let count := Nine.packedAt get (base+5) 7
  let direct := (Nine.packedAt get (base+12) 1 == 1)
  let bits := 12*depth
  let ops := Nine.packedAt get (base+13) bits
  let mask := Nine.packedAt get (base+13+bits) (10+depth)
  (depth,ops,mask,poolCodes get cw depth count (base+23+bits+depth),direct)

def tableBlock (ok : Nat → Nat → Bool) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => tableBlock ok k start n && ok k (start+n)

theorem blockAt {ok k off n} (h : tableBlock ok k off n = true) :
    ∀ (i : Nat), off ≤ i → i < off + n → ok k i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [tableBlock,Bool.and_eq_true] at h
    intro i lo hi
    by_cases e : i = off+n
    · simpa only [e] using h.2
    · exact ih h.1 i lo (by omega)

theorem all_good (mono9 : Nine.Lower false Nine.inputs Nine.graph 16) {u gs s t}
    (geo : ∀ g ∈ gs, geomOK u g=true) (samples : sampleOK s=true)
    (checks : ∀ k (i : Nat), i<t.1 k → checkRow u gs s t k i=true)
    (k i : Nat) (hi : i<t.1 k) :
    Nine.Extended.Impossible u wordTarget k (stateWords s t k i).toFinset := by
  induction k generalizing i with
  | zero => exact check_good mono9 geo samples (by omega) (checks _ _ hi)
  | succ k ih =>
    apply check_good mono9 geo samples _ (checks _ _ hi)
    intro _ j hj
    exact ih j hj

end PEqualNP.Outside.L_meta_4813

namespace PEqualNP.Outside.L_meta_4813

def quickLookup (nb slots sw vw codeWidth : Nat) (data : Nat → Nat) (h : Nat) : Option Nat :=
  let sh := Nine.packedAt data ((h%nb)*sw) sw
  let pos := (h/nb+sh)%slots
  let word := Nine.packedAt data (nb*sw+pos*vw) vw
  if (word >>> codeWidth) == (h/(nb*slots))%4096 then
    some (word &&& ((1 <<< codeWidth)-1))
  else none

end PEqualNP.Outside.L_meta_4813
