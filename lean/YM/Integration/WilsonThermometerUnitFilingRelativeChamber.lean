import YM.Integration.WilsonThermometerUnitFilingRelative
import YM.Integration.WilsonThermometerUnitFilingPaidSites

/-! The physical reflected root for the reached relative cells, including a test of zero signed mass. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRelativeChamber
open Function Filter Set MeasureTheory Finset Lattice Wilson Labels RG Source Extra.Histories
open Push Marker PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent FVA1
open OriginalForcedAddresses RG12 RG16 RG16.Literal Trace.Physical.GermGraph
open OPE.Cards Primitives.GCC.Anchor Climb WilsonPositionThermometerCapStation
open WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerCenteredAlgebra WilsonThermometerAlignedCells
open XSpace XSpace.Rose Cells Push.GridApprox WilsonThermometerWeightedCapture
open private sum_triples from YM.Integration.WilsonThermometerAlignedCells
open private admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6)
variable (z:UVIndex) (r:ℝ) (φ:Test 3)
local notation "T!" => Site (R.family.side z.1 z.2)
local notation "J!" => Stock.census (Fin 3)
open WilsonThermometerUnitFilingRelative (Grid)
variable (Q:Grid R z r φ→Poly J!)
local notation "μ!" => mass (R:=R) r z φ
open Next.UVStress OPE OPE.Cards Cells
open WilsonThermometerUnitFilingFeed (report)
local notation "sites!" c:max => (WilsonThermometerRegisteredCells.placement (R:=R) z (c).val).origin
local notation "old!" => WilsonThermometerUnitFilingRelative.source R A z r φ Q
local notation "native!" => WilsonThermometerUnitFilingRelative.table R z r φ Q
local notation "arm!" c:max s:max => placed R A z (s).val (sites! c)
local notation "amount!" c:max s:max => μ! (c).val*wallet (Q c) s

include simple in
theorem original (ready:∀v,R.family.ref (WilsonPositionThermometerGradedSource.grade v).val≤z.1)
    {u b j:ℕ} (ju:j≤u) (ub:u≤b) (bN:b≤z.1) (door:Opened R.family 0 u z.2)
    (fee:Grid R z r φ→(J!).Mode→ℝ)
    (arms:∀ (c:Grid R z r φ) (s:(J!).Mode),amount! c s≠0 → Booked R.family z.1 z.2 0 (arm! c s) u (ub.trans bN) ∧
       PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) (fee c s)
         ((arm! c s) - report R (arm! c s) u • (1:Cut R.family z.1 z.2))):
    let bill:=∑(c:Grid R z r φ)(s:(J!).Mode),‖amount! c s‖*fee c s
    Booked R.family z.1 z.2 0 (old!) u (ub.trans bN) ∧
    PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) bill ((old!)-report R (old!) u • (1:Cut R.family z.1 z.2)) ∧
    ‖WilsonThermometerUnitFilingCylinder.tested R A z r φ (native!)-report R (old!) u‖≤bill:=by
  classical
  intro bill
  let I:=Option ((Grid R z r φ)×(J!).Mode)
  let w:I→ℂ:=fun i=>i.elim 0 (fun a=>amount! a.1 a.2)
  let Y:I→Cut R.family z.1 z.2:=fun i=>i.elim 0 (fun a=>arm! a.1 a.2)
  let f:I→ℝ:=fun i=>i.elim 0 (fun a=>fee a.1 a.2)
  have cont:∀a,Continuous (Y a):=by
    rintro (_|a)
    · exact continuous_const
    · change Continuous (WilsonThermometerCourseIntake.placed R A z a.2.val _)
      unfold WilsonThermometerCourseIntake.placed;apply continuous_finsetProd;intro i _;exact R.family.continuousO ..
  obtain ⟨book,pay⟩:=WilsonThermometerUnitFilingPaidBlend.original R simple w Y ju ub bN door cont f (by
    rintro (_|a) ha
    · exact (ha rfl).elim
    · exact arms a.1 a.2 ha)
  have same:(∑i,w i • Y i)=(old!):=by
    rw [Fintype.sum_option,Fintype.sum_prod_type]
    simp only [w,Y,Option.elim_none,Option.elim_some,zero_smul,zero_add,
      WilsonThermometerUnitFilingRelative.source,WilsonThermometerUnitFilingCylinder.source,
      Finset.smul_sum,smul_smul]
  have total:(∑i,‖w i‖*f i)=bill:=by
    rw [Fintype.sum_option,Fintype.sum_prod_type]
    simp only [w,f,Option.elim_none,Option.elim_some,norm_zero,zero_mul,zero_add,bill,Finset.sum_product]
  rw [same] at book pay
  rw [total] at pay
  refine ⟨book,pay,?_⟩
  let T:=center R.family.S z.2 (ju.trans (ub.trans bN)) 0
  have norm:=(OPE.Strobe.atone T (R.family.beta z.1 z.2) (seamless R.makes z.1 z.2) pay.ticket).trans pay.mark
  change ‖R.family.omega z.1 z.2 ((old!)-report R (old!) u • (1:Cut R.family z.1 z.2))‖ ≤ _ at norm
  have law:R.family.omega z.1 z.2 ((old!)-report R (old!) u • (1:Cut R.family z.1 z.2)) =
      R.family.omega z.1 z.2 (old!) -report R (old!) u:=by
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact (WilsonThermometerUnitFilingRelative.continuous_source R A z r φ Q).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  have named:WilsonThermometerUnitFilingCylinder.tested R A z r φ (native!) =
      R.family.omega z.1 z.2 (old!):=by
    rw [←WilsonThermometerUnitFilingCylinder.literal R A z r φ (native!),
      WilsonCapturedPrimaryShiftedCylinder.original R A z ready r φ (native!) (fun _=>some (0:Fin 3)),
      ←WilsonThermometerUnitFilingRelative.folded R A z r φ Q]
    rfl
  rw [named]
  rwa [law] at norm

end YM.Integration.WilsonThermometerUnitFilingRelativeChamber
