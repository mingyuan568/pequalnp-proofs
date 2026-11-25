import Pack4813

namespace PEqualNP.Outside.L_meta_4813

theorem mergeBlock {ok k start a b}
    (left : tableBlock ok k start a = true)
    (right : tableBlock ok k (start+a) b = true) :
    tableBlock ok k start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [tableBlock,Bool.and_eq_true] at right
    change (tableBlock ok k start (a+b) && ok k (start+(a+b))) = true
    rw [ih right.1]
    simpa [Nat.add_assoc] using right.2

end PEqualNP.Outside.L_meta_4813
