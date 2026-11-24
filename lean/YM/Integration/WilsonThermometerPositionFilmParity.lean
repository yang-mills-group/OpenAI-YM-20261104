import YM.Integration.WilsonThermometerPositionFilmPayout
import YM.Integration.WilsonThermometerPositionOrbitPayout
import YM.Integration.WilsonOriginalThermometerTopGrading
/-! Odd kinetic coefficients vanish in the original normalized position Notebook on every published page. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmParity
open Set OPE OPE.Owl
open Function Filter Finset RG Lattice Tree Wilson Exterior Precision PhysicalNext PhysicalNext.Repeat Legato
open Push Input Org Next.Scheduling Next.Scheduling.Clock ConnectedActivityE6 AnalyticBridge VerifiedReset
open RegulatorIR RegulatorIR.Binding RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open QuadraticLocal.Affinity Source Labels RG.Supply FVA1 Cells
open PertExtension.Series Geometry Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open Comparison.RG02 Comparison.RG02.Symmetry Comparison.RG02.Cumulants
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV
open WilsonPositionProgramVariableCircuit WilsonThermometerProgramSubmittedWords
open WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open scoped Classical Topology BigOperators PowerSeries
variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀ x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀ P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "S" => Stock.census Unit
variable (color:G.ColorIndex) (r:ℕ) (F:Tent j)
  (hF : Notebook (WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks) (Oracle.books C.family.path.levels.clock.kernel) G branch color (Rocket.native j) F r) (live : 0 < r)
local notation "faculty" => WilsonThermometerPositionFilmBank.original C D m j w blocks branch color r F hF live

open RegulatorIR.FVAAlt2.Booth Comparison.RG02.Adjacent

theorem flat {r:ℕ} (live:0<r) (s:Binding.Scale) (clock:UnitCost)
    (known:Seconds s r) (aligned:Ribbon.Align r s clock) : HasDerivAt clock.rating 0 0 := by
  have written:PowerSeries.coeff 1 (Prim.tale (Ribbon.fees clock))=0:=
    (aligned 1 live).symm.trans (known 1 live (by decide))
  have zero:deriv (Ribbon.fees clock) 0=0:=by
    simpa [Prim.tale,Binding.inscription,PertExtension.Series.Radial.jet,iteratedFDeriv_one_apply,fderiv_apply_one_eq_deriv]
      using written
  let a:=deriv clock.rating 0
  have h:HasDerivAt clock.rating a 0:=(clock.smooth.differentiableAt (by simp)).hasDerivAt
  have f:HasDerivAt (Ribbon.fees clock) (-(2*a)) 0:=by
    have k:HasDerivAt ((clock.rating^2)⁻¹) (-(2*a)) 0:=by
      simpa [clock.origin] using (h.pow 2).inv (by simp [clock.origin])
    exact k.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>by simp [Ribbon.fees,Pi.pow_apply]))
  have hz:a=0:=by linarith [f.deriv]
  simpa only [hz] using h

theorem original (p:Page j):
    HasDerivAt ((WilsonThermometerPositionFilmPayout.clock C D m j w blocks branch color r F hF live).cloth p).rating 0 0 :=
  flat live _ _ (hF.clean p).2 ((WilsonThermometerPositionFilmPayout.clock C D m j w blocks branch color r F hF live).holds p)

end YM.Integration.WilsonThermometerPositionFilmParity
