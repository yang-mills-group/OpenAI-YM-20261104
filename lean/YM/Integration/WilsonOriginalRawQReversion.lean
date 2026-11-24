import YM.Integration.WilsonOriginalRawPinnedFinite
import YM.Integration.WilsonOriginalFiniteSignedReversion
import YM.Integration.WilsonOriginalChargedRawReturn
import YM.Integration.WilsonOriginalPrimerCourseTariff

/-! All grades of the originally returned Q row after the very same measured adjacent reset.
The field on the old label is evaluated at its actual upper forest, before any fresh lower
row is introduced, including on the chart of a rough incoming configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawQReversion
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

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonVacuumPreResetDatedDeposit (Issued)
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Rebirth Pressure PhysicalNext.Repeat.Legato
open WilsonOriginalEarnedFoldedUnary (independent)
open WilsonOriginalChargedRawJet (weight)
open WilsonMarkedKineticDefect WilsonVacuumPreResetMeasuredCaliber
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.Wilson (loopReset recastColors germPainter clockPacket forestLog)
open LocalLTE.Weft PertExtension.Series.Tested FormalBulk08 FormalBulk08.Orb FormalBulk08.Wine Comparison.RG02.Adjacent
local notation "P" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "K" => model R N i per hi

def dated {G:Gauge}(R:Run G)(N i:ℕ):Wine.Pence:=
  WilsonCoeffUV.Bank.pitch (WilsonVacuumPreResetStationaryChange.levels R) (WilsonVacuumPreResetStationaryChange.ratio R) N i

def coordinates (G:Gauge)(n:Side):Stationary.Link G n →ₗ[ℝ] (Woods G n→ℝ) where
  toFun B:=flatten (Stationary.arm G n 1 B)
  map_add' A B:=by funext b; simp [Stationary.arm,FreeResolvent.flatten]
  map_smul' t B:=by funext b; simp [Stationary.arm,FreeResolvent.flatten]

theorem on_coordinates {G:Gauge}{n:Side}(B:Stationary.Link G n)(T:Ink (Woods G n))(l:ℕ):
    Complex.ofReal (coeff l (OriginalRadialSeries.observed (flatten (Stationary.arm G n 1 B)) T))=
      WilsonNeutralSignedPolynomialRate.read (coordinates G n) T l B:=by
  rw [OriginalRadialSeries.observed,PowerSeries.coeff_map]
  rfl

private theorem reset {G:Gauge}{I A:Type}[DecidableEq I][Fintype I][Fintype A]{J:Census I}{c f:Side}{S:StepData c f}
    {p:Clip}{P₁:PathData G}{O:ChartRatio G}(ker:Bulk.Kernel S p P₁ O)(F:Forest S.ratio)(tag:S.Choices)
    (Y:Bulk.Colors J G f)(s:Hot J)(r j cap:ℕ)(hj:j≤r)(he:j≤cap)(unit:Adjacent.Caliber)(H₀:Pence)
    (fee:∀l≤cap,∀i q,physicalWeight unit cap l i q=formalWeight H₀ l i q)
    (a:A→ℂ)(W:A→Ink (Woods G c))(x:fieldDir G c 1)
    (paid:∀ l≤r,∀B:Stationary.Link G c,
      (Order.observe J r (Order.logMarked (Bulk.Fk ker F tag Y (Stationary.arm G c 1 B) r)) l).part s.val=
        ∑b,a b*WilsonNeutralSignedPolynomialRate.read (coordinates G c) (W b) l B):
    loopReset ker F tag Y s r (unit.back cap) j x=∑b,a b*WilsonNeutralSignedPolynomialRate.read (coordinates G c)
      (canter (bookH H₀) (bookU H₀) (Woods G c) (W b)) j ((Stationary.arm G c 1).symm x):=by
  let U:Adjacent.Display (Stationary.Link G c):=fun l B=>
    (Order.observe J r (Order.logMarked (Bulk.Fk ker F tag Y (Stationary.arm G c 1 B) r)) l).part s.val
  exact WilsonOriginalFiniteSignedReversion.original («K»:=unit.back cap) (cap:=cap) (H:=H₀) fee U (coordinates G c) W a he hj
    ((Stationary.arm G c 1).symm x) (fun l hl _=>paid l hl _)

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(v:V)
variable {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
variable (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) σ cash)
variable (simple:G.Simple)(k:V→ℕ)(start:Γ i 0=0)
local notation "cost" => (Rebirth.caliber (Γ i) start).back (e+2)
local notation "H" => dated R N i
local notation "L" => coordinates G (coarse R i per)
local notation "T" => fun a:Source D u=>flash (independent R N i per Q D u μ orders x F k a)
local notation "raw" => NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
local notation "s₀" => (⟨(C).fire v,Finset.singleton_nonempty v⟩:Hot (C))
local notation "amp" => fun a:Source D u=>WilsonOriginalChargedRawJet.weight D u N ((C).fire v) a
variable (rate:∀d≤e+2,∀j q,physicalWeight (Rebirth.caliber (Γ i) start) (e+2) d j q=formalWeight (dated R N i) d j q)

include course lo bank simple rate in
theorem original (r:ℕ)(hr:r≤e+2)(j:ℕ)(hj:j≤r)(A:fieldDir G (coarse R i per) 1):
    loopReset K F tag raw s₀ r cost j A =
      ∑a:Source D u,amp a*read L (canter (bookH H) (bookU H) (Woods G (coarse R i per)) (T a)) j
        ((Stationary.arm G (coarse R i per) 1).symm A):=by
  apply reset K F tag raw s₀ r j (e+2) hj (hj.trans hr) (Rebirth.caliber (Γ i) start) H rate amp T A
  intro l hl B
  have heard:=WilsonOriginalRawPinnedFinite.original R N i per hi Q D u μ orders x F tag v simple k course lo bank B r hr l hl
  simp_rw [on_coordinates] at heard
  exact heard

end YM.Integration.WilsonOriginalRawQReversion
