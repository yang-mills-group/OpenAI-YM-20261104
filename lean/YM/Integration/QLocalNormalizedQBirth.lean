import YM.Integration.ActualOriginalQInitialPreparation
import YM.Integration.LocalComparisonUniformModelPrice
import YM.Integration.LocalComparisonModelIntegrable
import YM.Integration.NativePaidPacketColors
import YM.Integration.ActualPolynomialContraction

/-! The original pre-test normalization buys the actual frozen Q bank with a
unit bill. This controls its complete normalized Wilson transport before any
coarse field, period, relative source locations, and remaining cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalNormalizedQBirth
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker Precision
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open MergeProof MergeProof.Accent ActualPolynomialContraction
open scoped Classical Topology BigOperators

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
theorem weights {Γ:Census V} {w:V→ℝ} (hw:∀v,0≤w v) (hu:∀v,w v≤1) (Y:Poly Γ) :
    Poly.price w Y≤Poly.price (fun _=>1) Y := by
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _=>hw i) (fun i _=>hu i)) (norm_nonneg _)

variable (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
    (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "M" => ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders
local notation "t₀" => μ-R.family.S.scale d.cutoff
local notation "X" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)

theorem unit (a:ℝ) :
    (M).Paid ((A₀).inputNorm d.level) (ActualOriginalQPackets.positions D u).stub
      (ActualRunQlocalNativeTuple.readerRegion D) (fun _=>1) a ((A₀).inputWidth d.level) 1
      (ActualOriginalQInitialInput.cover R hG u J A d Q o μ orders) 0 := by
  let P:=ActualOriginalQFrozenInput.packets Q D u t₀ orders d.cutoff
  let H:=ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
  have original:=ActualOriginalQFrozenInput.packets_paid Q D u t₀ orders d.cutoff a
    ((A₀).inputNorm d.level) (fun _=>1) ((A₀).inputWidth d.level) ((A₀).input_width_pos _) (fun _=>zero_lt_one)
  have cost:ActualOriginalQPackets.packetCost Q D u t₀ orders d.cutoff (fun _=>1) ((A₀).inputWidth d.level)≤H:=by
    rw [ActualOriginalQCharges.packet_cost D u Q t₀ orders d.cutoff d.below (fun _=>1) ((A₀).inputWidth d.level)]
    exact le_max_right _ _
  exact FixedRadiusScaling.paid_normalized P original H (le_max_left _ _) cost

theorem model (a:ℝ) (w:V→ℝ) (hw:∀v,0≤w v) (hu:∀v,w v≤1)
    (t:IndependentTests (J₀).tests) (U:Config G (R.family.side (d.level+1) d.period)) :
    Poly.price w (Poly.pass ((M).read (testInclusion _ t) a U))≤
      MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1 :=
  (weights hw hu _).trans ((unit R hG u J A d Q o μ orders a).uniform_model _ le_rfl t U)

variable [Nonempty V]
local notation "I" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders

theorem source (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t:TestSpace (J₀).tests) (U:Config G (R.family.side (d.level+1) d.period)) :
    ((I).leaf t).density U=(X).eval U • Poly.pass ((M).read t g U) := by
  rw [ActualOriginalQInitialPreparation.input_density,ActualOriginalQInput.density_full Q D u t₀ orders hG
    d.cutoff d.below (ActualOriginalQLayout.reference_le R u ref)]
  change ((X).eval U:ℂ) • Poly.pass _ = (X).eval U • Poly.pass
    ((VariableScaling.packets _ (ActualOriginalQFrozenInput.packets Q D u t₀ orders d.cutoff)).read t g U)
  rw [VariableScaling.read,ActualOriginalQFrozenInput.packets_read Q D u t₀ orders d.cutoff d.below,
    Complex.coe_smul]

theorem transported (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (w:V→ℝ) (hw:∀v,0<w v) (hu:∀v,w v≤1) (t:IndependentTests (J₀).tests)
    {k:ℕ} (hk:k≤d.level+1) (U:Config G (R.family.side k d.period)) :
    Poly.price w (actualSignedTransport R.family (N:=d.cutoff) ((I).leaf (testInclusion _ t)).density hk U)≤
      MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1 := by
  let v:=testInclusion (J₀).tests t
  let P:=fun U=>Poly.pass ((M).read v g U)
  have hX:Envelope (X).eval:=(X).envelope (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good
  have paid:=unit R hG u J A d Q o μ orders g
  have hP:Envelope P:=paid.multiplier_envelope (fun t U=>NativePaidPacketColors.read_summable paid
    (Currency.g_pos R.makes _ _ _ d.below).ne' t g U) v
  have eq:((I).leaf v).density=fun U=>(X).eval U • P U:=funext (source R hG u J A d Q o μ orders ref v)
  have integrable:Integrable ((I).leaf v).density (prior G _):=by
    rw [eq]
    obtain ⟨C,hC⟩:=hP.cost
    obtain ⟨K,hK⟩:=hX.cost
    refine Integrable.of_bound (hX.meas.smul hP.meas).aestronglyMeasurable (K*C) (ae_of_all _ fun U=>?_ )
    rw [norm_smul]
    exact mul_le_mul (hK U) (hC U) (norm_nonneg _) ((norm_nonneg _).trans (hK U))
  apply signed_price_le R.family R.makes hw d.below integrable _ hk U
  intro W
  have nonnegative : 0 ≤ (X).eval W :=
    (Multi.AxisShift.chosen_positive R.makes.wilson d.below W).le
  rw [eq]
  change Poly.price w ((X).eval W • P W) ≤ (X).eval W * _
  rw [price_real_smul w (P W) nonnegative]
  exact mul_le_mul_of_nonneg_left (model R hG u J A d Q o μ orders g w
    (fun v=>(hw v).le) hu t W) (Multi.AxisShift.chosen_positive R.makes.wilson d.below _).le

end YM.Integration.QLocalNormalizedQBirth
