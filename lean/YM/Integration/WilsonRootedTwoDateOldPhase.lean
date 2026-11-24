import YM.Integration.WilsonRootedTwoDateOldPointInvoice
import YM.Integration.WilsonOriginalPointUnitTest

/-! Exact regulator-clock fees in the normalized genuine previous point source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateOldPhase
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof MergeProof.Accent Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct
open private input_leaf from YM.Integration.ActualOriginalQInitialPreparation
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (old : Seed R B V N p (m+1)) (hG : G.Simple)
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "loRep" => R.family.path.rep N p (m+1)
local notation "upperStep" => R.family.path.levels.clock.op (m+1) p

local notation "Γ" => Stock.census V
local notation "oldG" => Pert.Asymptotics.regulatorRun R.family N p (m+2)
local notation "oneW" => fun _ : V=>(1:ℝ)

open ActualOriginalQReaders
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots
local notation "tests₀" => (ActualOriginalQPointSetup.request R old.labels old.request).tests
local notation "norm₀" => ActualOriginalQInitialInput.normalizer R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
local notation "fee₀" => ActualOriginalQReaders.fee old.prescription old.labels (old.scale-R.family.S.scale N) old.degree

omit [Nonempty V] in
theorem normalized : WilsonRootedTwoDateOldPointInvoice.phase old.point_unit hG=
    (1+∑s : Slot old.labels, ‖(fee₀) s‖/(norm₀))^Fintype.card (Slot old.labels) := by
  have paid : 1≤(norm₀) := le_max_left _ _
  let c := ActualOriginalQInitialInput.scales R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
  let x := testInclusion (tests₀) (WilsonOriginalPointModes.unit (tests₀))
  let X := VariableScaling.tests c x
  change (1+∑s : Slot old.labels, ‖readers old.prescription (D₀) old.labels (old.scale-R.family.S.scale N) old.degree s (X s.1)‖)^_=_
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  change ‖(fee₀) s*ActualRunQlocalNativeTuple.reader (D₀) s.1 (X s.1)‖=_
  have atPoint : ActualRunQlocalNativeTuple.reader (D₀) s.1 (X s.1)=(X s.1).val 0 := ActualOriginalQPointDatum.reader_eq R p (m+2) old.roots (fun i=>(old.request.tests i).D) (fun _=>0) s.1 (X s.1)
  rw [atPoint]
  change ‖(fee₀) s*((((norm₀):ℂ)⁻¹)*(x s.1).val 0)‖=_
  rw [show (x s.1).val 0=1 from WilsonOriginalPointModes.unit_read (tests₀) _,mul_one,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans paid),div_eq_mul_inv]

omit [Nonempty V] in
theorem fixed : WilsonRootedTwoDateOldPointInvoice.phase old.point_unit hG≤WilsonRootedOPEPhase.wallet (fee₀) := by
  rw [normalized]
  unfold WilsonRootedOPEPhase.wallet
  have paid : 1≤(norm₀) := le_max_left _ _
  have sum : (∑i : Slot old.labels,‖(fee₀) i‖/(norm₀))≤∑i,‖(fee₀) i‖ := Finset.sum_le_sum fun i _=>div_le_self (norm_nonneg _) paid
  exact pow_le_pow_left₀ (add_nonneg zero_le_one (Finset.sum_nonneg fun i _=>div_nonneg (norm_nonneg _) (zero_le_one.trans paid))) (add_le_add le_rfl sum) _

end YM.Integration.WilsonRootedTwoDateOldPhase
