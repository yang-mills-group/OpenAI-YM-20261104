import YM.Integration.WilsonRootedTwoDateFreshMask
import YM.Integration.QLocalMarkedJoinedFamily

/-! The two proper point-source masks multiply on the original square-free coefficient algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateFreshExponent
open Push.Local Push.AbsoluteSums
open Function Finset Lattice Wilson RG Marker LocalComparison LocalComparison.MarkedPackets
open Comparison.Density.RenderM ManuscriptQLocalOriginalConditionalTail QLocalThermalPacketDivision
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)

variable {q : BudgetPoint} {a : V→Support n} {region : Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {w : V→ℝ} {g width budget : ℝ} {off cov : ℕ}

theorem original (p : BudgetPoint) (H : P.Paid q a region w g width budget off cov) (hg : g≠0)
    (x : IndependentTests D) (U : Config G n) :
    Poly.pass (P.read (testInclusion D x) g U)=Poly.pass (source P p g x 1 U)*Poly.pass (dirty P p (testInclusion D x) g U) := by
  have hc : (clear P p (testInclusion D x) g U).part Γ.quiet=0 :=
    (WilsonPrescribedPacketTail.slice P _).quiet_read _ _ _
  have hd : (dirty P p (testInclusion D x) g U).part Γ.quiet=0 :=
    (WilsonPrescribedPacketTail.slice P _).quiet_read _ _ _
  rw [←(partition P p H hg (testInclusion D x) U).2,Extra.Trajectories.pass_add hc hd,
    WilsonRootedTwoDateFreshMask.clear_source]

end YM.Integration.WilsonRootedTwoDateFreshExponent
