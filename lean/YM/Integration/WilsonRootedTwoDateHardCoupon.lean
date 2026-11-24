import YM.Integration.QLocalThermalJoinedRate
import YM.Integration.WilsonRootedTwoDateHardSource
import YM.Integration.QLocalThermalJoinedInvoice

/-! Charge the gained full signed forcing on the real joined inventory.
The incoming marked spectators and the unmarked K appear in the same
native per-site invoice. The tariff is fixed before every independent
test and every background field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardCoupon
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM
open MergeProof.Accent Push.AbsoluteSums ActualWilsonJoinedCofactor ActualWilsonDirtyPartners
open QLocalThermalPacketDivision QLocalThermalJoinedSource
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {Q:Rep G n}
    (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

variable (oldD : V → ComparisonDensity.Address.Orbit)
local notation "Joint" => TestSpace oldD × TestSpace D
local notation "Unit" => IndependentTests oldD × IndependentTests D

def measured (A : Joint → Bands Γ Q) (i : ℕ) (z : Unit × Config G n) :=
  (A (WilsonRootedTwoDateHardSource.inclusion oldD z.1)).each i z.2

omit [Fintype V] in
theorem coupon (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (s:Γ.Mode) (active:s≠Γ.quiet) (c:ℂ) (hc:‖c‖≤1) (A:Joint→Bands Γ Q) {u:ℝ}
    (old:Towed w (ActualWilsonPacketSplit.scopes Q) (measured oldD A) p.B p.supportExponent u)
    (small:u*blockSites p.B≤(3*p.supportExponent)/2) :
    Nonempty (QLocalMarkedJoinedWeight.Coupon p (fun i (z:Unit×Config G n)=>
      QLocalMarkedJoinedLinear.addition (Y:=plot P) K (A (WilsonRootedTwoDateHardSource.inclusion oldD z.1)) s
        (row P Q.p g c s (testInclusion D z.1.2)) i z.2) w Q
      ((2/(3*p.supportExponent))*(u*blockSites p.B)*
        ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget))) := by
  obtain ⟨b,unit,money⟩:=QLocalThermalTokenTariff.partners P H (ActualWilsonPacketSplit.scopes Q) (measured oldD A) old small s active
  exact QLocalMarkedJoinedWeight.weights H.positive p K (fun x=>A (WilsonRootedTwoDateHardSource.inclusion oldD x)) s
    (fun x=>row P Q.p g c s (testInclusion D x.2)) (QLocalThermalTokenTariff.stem P s w g) b _
    (QLocalThermalTokenTariff.charged P H s) unit (fun r x U => QLocalThermalTokenTariff.field P H Q.p c hc s r x.2 U) money

end YM.Integration.WilsonRootedTwoDateHardCoupon
end
