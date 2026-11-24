import YM.Gaps1020.Local.Align

/-! Native forced addresses and actual hard weights in the regular cover-world
operation, before any Spring, field, cutoff or couplings are substituted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedWorldFields
open Lattice RG Precision AnalyticBridge VerifiedReset Collection
variable {G : Gauge} {n : Side} (A : Activities G n) (X : Listing G n)
    (p : BudgetPoint) (Y : PathData G) (c : Clip) (J : Collection.Source G n) (a : ℝ)

theorem forced : (GapsLocal.Renew.coverWorld A X p Y c J a).forced=A.forced := rfl

theorem charges : (GapsLocal.Renew.coverWorld A X p Y c J a).K=A.K := rfl

end YM.Integration.OriginalMarkedWorldFields
