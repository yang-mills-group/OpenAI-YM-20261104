import YangMills.WilsonProof.NativeSupport.WilsonBridge
import YangMills.WilsonProof.NativeSupport.WilsonLatticeData

set_option autoImplicit false

namespace IssuedRuns.GradedTokens

open YangMills YangMills.Wilson Filter
noncomputable section

variable {g : GaugeGroup}

def original (C : YM.Family g.core) (h : C.Makes) :
    YangMills.Wilson.GradedTokens (wilsonFamily C) C.book.conjugate
      (C.book.reflectedToken timeAxis) where
  width d := (C.labels.level d).extra + 1
  token := fun v => ⟨v.1, v.2⟩
  onto := fun v => ⟨v, rfl⟩
  linear N p d x U := by
    constructor
    · intro u v
      exact congrFun ((C.linearO N p d x).map_add u v) U
    · intro c u
      exact congrFun ((C.linearO N p d x).map_smul c u) U
  bar d := C.book.bar d
  os d := C.book.adj d timeAxis
  tokenBar _ _ := rfl
  tokenOS _ _ := rfl
  unit := C.refUnit 4
  unitFinite := by
    filter_upwards [eventually_ge_atTop (C.ref 4)] with N hn
    intro p x U
    exact congrFun (C.constant (p := p) h 4 hn x) U


end
end IssuedRuns.GradedTokens
