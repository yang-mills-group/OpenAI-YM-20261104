import YM.Integration.QLocalFixedJoinedFamily
import YM.Integration.QLocalThermalJoinedInvoice

/-! Charge the gained full signed forcing on the real joined inventory.
The incoming marked spectators and the unmarked K appear in the same
native per-site invoice. The tariff is fixed before every independent
test and every background field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardSource
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM
open MergeProof.Accent Push.AbsoluteSums ActualWilsonJoinedCofactor
open QLocalThermalPacketDivision QLocalThermalJoinedSource QLocalMarkedJoinedCatalogue
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {Q:Rep G n}
    (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

variable (oldD : V → ComparisonDensity.Address.Orbit)
local notation "Joint" => TestSpace oldD × TestSpace D
local notation "Unit" => IndependentTests oldD × IndependentTests D

def inclusion (z : Unit) : Joint := (testInclusion oldD z.1,testInclusion D z.2)

def source (H : P.Paid p a region w g width budget off cov) (hg : g≠0) (c : ℂ) :
    Source (W:=Q) (plot P) (fun (z : Joint) U=>c • dirty P Q.p z.2 g U) :=
  let S := QLocalThermalJoinedSource.source (Q:=Q) P H hg c
  { field s z := S.field s z.2
    dirty s z r U := S.dirty s z.2 r U
    purchase s z U := S.purchase s z.2 U }

/-- Both receipts retain literally the same signed packet kernel. -/
theorem same {w' : V→ℝ} {bill : ℝ} (H : P.Paid p a region w g width budget off cov)
    (H' : P.Paid p a region w' g width bill off cov) (hg : g≠0) (c : ℂ) :
    source (Q:=Q) P oldD H hg c = source (Q:=Q) P oldD H' hg c := rfl

end YM.Integration.WilsonRootedTwoDateHardSource
end
