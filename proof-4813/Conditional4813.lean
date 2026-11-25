import Roots4813

namespace PEqualNP.Outside.L_meta_4813
open Nine.Extended
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem live_on_rows (u : Bool) (ps : List (Fin 12)) (C : Circuit)
    (legal : FanInTwo C) (mono : u=false → ∀ g ∈ C.gates, isNot g=false)
    (correct : ∀ r, C.eval (inputAt (rawBit r) u ps) = edgeFn (rawBit r)) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u wordTarget k S ∧
      ∀ a ∈ S, a ∈ (makeBank u ps).map (nrm u) := by
  let w := makeBank u ps
  have he : (execute C.gates w).getD C.output zero = wordTarget := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (w.map (bit r))).getD C.output false = _
    rw [show w.map (bit r) = inputAt (rawBit r) u ps from bank_bits _ _ _,target_bit]
    exact correct _
  have out := get_rep (u:=u) (execute C.gates w) C.output
  rw [he] at out
  unfold Nine.Extended.Repr at out
  rw [nrm_id (show bit 0 wordTarget = false by decide +kernel)] at out
  exact extract C.gates w legal mono target_proper (out.resolve_right (fun h => h target_proper))

def capFor (u : Bool) := if u then 16 else 17

theorem exclude_from_tables
    (ss : Bool → Samples) (ts : Bool → ProofTable)
    (cert : ∀ u i, i < (ts u).1 (capFor u) →
      Impossible u wordTarget (capFor u) (stateWords (ss u) (ts u) (capFor u) i).toFinset)
    (roots : ∀ u, ∀ b ∈ possibleB u, rootChecks u (ss u) (ts u) (capFor u) b=true)
    (C : Circuit) (ps : List (Fin 12)) (legal : FanInTwo C) (len : C.size≤17)
    (hlen : ps.length≤2) : ¬∀ x, C.eval (inputAt x true ps) = edgeFn x := by
  intro correct
  by_cases noNot : ∀ g ∈ C.gates, isNot g=false
  · have ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or := by
      intro g hg
      have h := (legal g hg).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · have f := noNot g hg
        simp [isNot,hn] at f
    obtain ⟨k,S,budget,run,sup⟩ := live_on_rows false ps C legal (fun _ => noNot) (bypass_rows ops ps correct)
    have kb : k≤capFor false := budget.trans (List.countP_le_length.trans len)
    exact verdict ps hlen (cert false) (roots false) kb run sup
  · obtain ⟨k,S,budget,run,sup⟩ := live_on_rows true ps C legal (by simp) (fun r => correct (rawBit r))
    have cut : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      by_contra! ge
      have eq := Nat.le_antisymm List.countP_le_length ge
      apply noNot
      intro g hg
      simpa using List.countP_eq_length.mp eq g hg
    have length : C.gates.length≤17 := len
    have kb : k≤capFor true := by change k≤16; omega
    exact verdict ps hlen (cert true) (roots true) kb run sup

end PEqualNP.Outside.L_meta_4813
