import YM.Integration.WilsonRootedTwoDateSource
import YM.Integration.WilsonRootedFirstInteriorCarry

/-! The normalized physical higher insertion and the actual lower signed band use the identical push. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct.Seed
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof MergeProof.Accent Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence
open private input_leaf from YM.Integration.ActualOriginalQInitialPreparation
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (old : Seed R B V N p (m+1)) (hG : G.Simple)
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "loRep" => R.family.path.rep N p (m+1)
local notation "upperStep" => R.family.path.levels.clock.op (m+1) p

theorem pushed (U : Config G (R.family.side (m+1) p)) :
    old.response hG (Nat.le_succ (m+1)) U=((loRep).eval U)⁻¹ • (upperStep).push (topRep).beta (old.numerator hG) U := by
  rw [response,actualSignedTransport_eq R.family R.makes old.below,gust_step R.family.path N p (m+2) (old.numerator hG) (Nat.lt_succ_self (m+1)),gust_base]

/-- All original tested high modes are supplied by the old point source itself. The
ordinary and forced lower invoices are on its integrated gauge-dependent numerator. -/
theorem carry {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay) (prev now : ℕ)
    (one : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (two : GapsLocal.Full.target 0 (Fintype.card V) now ≤ R.alloy.B.a.clock.J (m+1))
    (sites : ∀s : ActualOriginalQReaders.Slot old.labels,R.family.ref s.2.size ≤ m+2) :
    WilsonRootedFirstInteriorCarry.Inherited R (N:=N) old.roots (fun _=>1) prev now (old.numerator hG) := by
  let D := ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots
  let x := testInclusion (ActualOriginalQPointSetup.request R old.labels old.request).tests old.test
  let c := ActualOriginalQInitialInput.scales R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
  have native := WilsonRootedFirstInteriorCarry.original R hG spring marks old.below prev now one two D old.prescription old.labels
    (old.scale-R.family.S.scale N) old.degree sites (fun _=>1) (fun _=>zero_lt_one) (VariableScaling.tests c x)
  have same : (ActualOriginalQPackets.positions D old.labels).origin=old.roots := funext fun i=>ActualOriginalQPointDatum.root_eq R _ _ _ _ _ i
  have read := input_leaf R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree x
  have density := congrArg (fun leaf=>leaf.density) read
  have hn : old.numerator hG=((ActualOriginalQInput.input old.prescription D old.labels (old.scale-R.family.S.scale N) old.degree hG N old.below).leaf (VariableScaling.tests c x)).density := density
  have first := congrArg (fun cut=> WilsonRootedFirstInteriorCarry.Inherited R (N:=N) (ActualOriginalQPackets.positions D old.labels).origin (fun _=>1) prev now cut) hn.symm
  have second := congrArg (fun z=>WilsonRootedFirstInteriorCarry.Inherited R (N:=N) z (fun _=>1) prev now (old.numerator hG)) same
  exact second.mp (first.mp native)

end YM.Integration.WilsonRootedTwoDateProduct.Seed
