import YM.Integration.FullQLocalRequestData
import YM.Integration.QlocalNativeTests

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQCountableRequests
open FullQLocal.RenderedStep

/-- The complete original-Q request update, indexed by a natural rank. -/
def atRank {V : Type} (rank : ℕ) (K : Request V) : Request V :=
  { K with
    vacuumRankCap := max K.vacuumRankCap (K.order + 2)
    inputPacketRankCap := max K.inputPacketRankCap rank
    inheritedConstant := max K.inheritedConstant (2 ^ ((K.order : ℝ) + 1 - K.eta))
    inherited_constant_nonnegative :=
      K.inherited_constant_nonnegative.trans (le_max_left _ _)
    tests := fun i => QlocalNativeTests.orbit (K.tests i).D 0
    test_order := K.test_order }

end YM.Integration.ActualOriginalQCountableRequests
end
