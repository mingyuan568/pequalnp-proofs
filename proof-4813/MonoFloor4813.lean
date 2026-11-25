import PNPBase
import PEqualNP.Outside.L_meta_670

namespace PEqualNP.Outside.L_meta_4813
open PEqualNP.Outside.L_meta_670 in
theorem mono_floor_official : Nine.Lower false Nine.inputs Nine.graph 16 := by
  have prior : Impossible false (graphGoal 511) 15 (vars 511).toFinset := by
    rw [show graphGoal 511 = graph by decide +kernel,
        show vars 511 = inputs by decide +kernel]
    exact monoRoot
  have floor := plain_low (m:=511) (hints:=0x321032101) (by decide +kernel) prior
  rw [show vars 511=inputs by decide +kernel,show graphGoal 511=graph by decide +kernel] at floor
  intro k bank hr ha
  apply floor k bank _ ha
  clear ha
  induction k generalizing bank with
  | zero => exact hr
  | succ k ih =>
    obtain ⟨op,bs,a,b,reach,aa,ab,eq⟩ := hr
    exact ⟨op,bs,a,b,ih bs reach,aa,ab,eq⟩

end PEqualNP.Outside.L_meta_4813
