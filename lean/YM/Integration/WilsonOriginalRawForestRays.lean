import YM.Integration.WilsonOriginalJointForestRay
import YM.Integration.WilsonOriginalFoldedUnarySourceEra

/-! Every genuine original freshly issued Q face supplies its full incoming group-field
ray on a nonbare program, even when other seats already have marked history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawForestRays
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Comparison.Density.RenderM NativePaidPacketColors MergeProof MergeProof.Accent
open PertExtension Series Series.Radial Series.Tested RegulatorIR RegulatorIR.FVAAlt2
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open ActualRunCalibrationTests OriginalSourceJetAddresses FundedOriginalMarkedInput
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open Next.SectorChange

variable {G:Gauge}(R:Run G){deck:MS.Local.Physical.Deck G}(N i per:ℕ)(hi:i < N)
  {n:ℕ}{hn:n ≤ i + 1}{V:Type}[DecidableEq V][Fintype V]
  (Q:MS.Land.Prescription deck)(D:ActualRunQlocalNativeTuple.Datum R per (i + 1) n hn V)
  (u:V→MS.Rake.Label deck)(μ:ℝ)(orders:V→ℕ) (x:TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "C" => Stock.census V
local notation "P" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P v₀ x
local notation "S" => step R i per
local notation "K" => model R N i per hi

include hi in
private theorem legal : Bulk.Well Y :=by
  have H:=ActualOriginalQPackets.packets_paid Q D u μ orders N ((levels R).budget (i + 1))
    (fun _=>1) 1 zero_lt_one (fun _=>zero_lt_one)
  have law:=(Bulk.Colors.no_hole G (R.family.side (i + 1) per) C).1
  exact NativePaidPacketColors.colors_well H (ActualRunKernelPackets.regulator_pos R N per (i+1) hi).ne' v₀ law.suppose_vac law.natural law.envelope _

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))


open PhysicalForestMarkedRay
open WilsonOriginalJointForestRay (forward)
open WilsonOriginalFoldedUnarySourceEra (data)

def paper (a:Source D u):Ink (Woods G (fine R i per)):=
  flash ((data (R:=R) (i:=i) (per:=per) Q D u μ orders x a).1 (fine R i per))

include tag in
theorem original (s:Hot (C))(j:ℕ)(z:Precision.Key F G→ℝ):
    readJet ((Y).power s+j) (chartMark S F M K B z Y s)=
      ∑o:Source D u,weight D u N s.val o*(MvPolynomial.eval (Sum.elim z (flatten B))
        (coeff j (forward R N i per hi F (paper (R:=R) (i:=i) (per:=per) Q D u μ orders x o))):ℝ):=by
  have hM:=WilsonOriginalJointForestRay.swept R N i per hi F tag
  have well:Bulk.Well Y:=legal R N i per hi Q D u μ orders x
  have field:Cloud.paint z (kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F Y s) ((Y).power s+j))=
      readJet ((Y).power s+j) (chartMark S F M K B z Y s):=by
    rw [Assembly.reading]
    exact PhysicalForestMarkedRay.coefficient S F M K B z tag Y well s hM _
  rw [←field]
  refine (WilsonOriginalChargedRawJet.kernel Q D u μ orders K F M N hi v₀ x s B z j hM).trans ?_
  rw [same_axes R i per F B z]
  apply Finset.sum_congr rfl
  intro o _
  rw [WilsonOriginalRegisteredRawPage.coefficient R N i per hi Q D u μ orders x F o j]
  rfl

end YM.Integration.WilsonOriginalRawForestRays
