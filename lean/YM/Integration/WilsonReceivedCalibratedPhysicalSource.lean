import YM.Integration.WilsonReceivedCalibratedPlacement
import YM.Integration.WilsonReceivedTwoDateSigned

/-! The complete actual field submitted to the following Wilson block, at a calibrated
upper appointment and a fresh original curvature insertion. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCalibratedPhysicalSource
open Lattice Wilson RG Source Labels Marker LocalComparison LocalComparison.Global RG3.Script.Picnic
open FullQLocal FullQLocal.RenderedStep QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open PhysicalNext PhysicalNext.Repeat
open scoped Classical

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B)
  (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (J₂:Request V) (Q₂:MS.Land.Prescription B) (u₂:V→MS.Rake.Label B)
  (o₂:V→Site (R.family.side d.level d.period)) (ν:ℝ) (orders₂:V→ℕ) (old fresh:Finset V)
local notation "req" => ActualOriginalQPointSetup.request R u J
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "D₂" => ActualOriginalQPointSetup.pointDatum R J₂ d.period d.level o₂
local notation "source" => ActualOriginalQInitialPreparation.input R simple u J A d Q o μ orders
local notation "raw" => ActualOriginalQInput.input Q D u (μ-R.family.S.scale d.cutoff) orders simple d.cutoff d.below
local notation "upper" => WilsonOriginalProjectedCurvatureTableau.actors D
local notation "younger" => WilsonOriginalProjectedCurvatureTableau.actors D₂
local notation "z₀" => WilsonOriginalMixedTestTableau.zero D
local notation "z₂" => WilsonOriginalMixedTestTableau.zero D₂
local notation "left" => WilsonMixedTestTableau.left upper younger old z₀
local notation "right" => WilsonMixedTestTableau.right upper younger fresh z₂
local notation "call" => WilsonReceivedCalibratedTest.submit R simple u J A d Q o μ orders
local notation "sheet" => PhysicalNext.Repeat.Pane.panel R.alloy d.level (R.alloy.B.a.S.oneStep d.level d.period).exact_size
local notation "β" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "tested" => fun t U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun a =>
  ActualRunQlocalNativeTuple.reader D₂ a (testInclusion (ActualRunQlocalNativeTuple.orbit D₂) t a) *
    ActualOriginalCalibratedColumns.weightedObservable R B Q₂ (u₂ a) ν (R.family.side d.level d.period)
      (ActualRunQlocalNativeTuple.root D₂ a) U (orders₂ a)))
local notation "newborn" => fun x U=>tested (right x) U

theorem original (x:Wallet (WilsonMixedTestTableau.actors upper younger))
    {P:Rep G (R.family.side (d.level+1) d.period)}
    (inlet:Taste (TestSpace (req).tests) o P (Stock.census V))
    (physical:P=(ActualOriginalQInitialPreparation.carrier R d).rep) (same:HEq inlet source) :
    ∃ y:Wallet (WilsonMixedTestTableau.actors upper younger),
      left y=call (left x) ∧ right y=right x ∧
      ∀ U:Config G (R.family.side d.level d.period),
        newborn y U * (sheet).push β ((raw).leaf (testInclusion (ActualRunQlocalNativeTuple.orbit D) (left y))).density U =
        newborn x U * (sheet).push β (inlet.leaf (testInclusion (req).tests (left x))).density U := by
  obtain ⟨y,calibrated,unchanged,held⟩:=WilsonReceivedCalibratedPlacement.original R simple u J A d Q o μ orders
    younger z₂ old fresh x inlet physical same
  refine ⟨y,calibrated,unchanged,fun U=>?_⟩
  have newPart:=congrArg (fun t:Wallet younger=>tested t U) unchanged
  have oldPart:=congrFun (congrArg ((sheet).push β) (funext held)) U
  exact congrArg₂ (fun a b:Poly (Stock.census V)=>a*b) newPart oldPart

end YM.Integration.WilsonReceivedCalibratedPhysicalSource
