import YM.RG.Masks

/-! The actual directional reanchoring price at a covered support. -/
noncomputable section
namespace YM.Integration.WilsonReportRetainedAnchor
open RG

def reprice (P : BudgetPoint) (h : ℕ) : ℝ :=
  ((1+((h*(4*P.B+2)+2*P.B:ℕ):ℝ))^P.power)^P.order

end YM.Integration.WilsonReportRetainedAnchor
