import YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels

/-! Reindex the actual pointwise product before the one joint Wick integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalLabelProduct
open Finset Lattice RG Wilson Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalCensusCopyGraphs
open WilsonReceivedDepositedOrbitalFixedLabels
open scoped Classical BigOperators
theorem original {I α:Type}[DecidableEq I][CommMonoid α]{f F:Side}(h:f.val∣F.val)
    (z:I→Site f)(s:Finset I)(p:s→Fin (Pages f F))(score:I→Site F→α)(t:Finset (graph s p)):
    (∏u∈t,score u.val.1 (page h (z u.val.1) u.val.2).val)=
      ∏i∈t.map (name s p),score i (wrap F (home s h z p i)):=by
  rw [prod_map]
  exact prod_congr rfl (fun u _=>by rw [attached,wrap_lift];rfl)

end YM.Integration.WilsonReceivedDepositedOrbitalLabelProduct
end
