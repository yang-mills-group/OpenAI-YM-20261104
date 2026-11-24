import YM.Integration.WilsonThermometerUnitFilingAveraged
import YM.Integration.WilsonThermometerUnitFilingPaidSites
import YM.Integration.WilsonThermometerSupportedCells
import YM.Integration.WilsonThermometerRegisteredCells

/-! The registered shape has an exact original fixed-u filing on the two relative offsets
left by center integration. The same filed source is used by the actual ancestral receipt. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRelative
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
abbrev Grid:=WilsonThermometerSupportedCells.Occupied (N:=z.1) (per:=z.2) R r φ
variable (Q:Grid R z r φ→Poly (Stock.census (Fin 3)))
local notation "μ!" => mass (R:=R) r z φ
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
def filled (v:T!×T!):Poly J!:=if pv:μ! v≠0 then Q ⟨v,pv⟩ else 1
def table (x:Sites R z):Poly J!:=filled R z r φ Q (offsets x)
local notation "loc!" t:max => WilsonThermometerRegisteredCells.placement (R:=R) z t
def source :Cut R.family z.1 z.2:=∑c:Grid R z r φ, μ! c.val • WilsonThermometerUnitFilingCylinder.source R A z (loc! c.val).origin (Q c)
local notation "Y!" => source R A z r φ Q

theorem folded :
    WilsonThermometerUnitFilingRegistered.submitted R A z r φ (table R z r φ Q)
      (fun x=>WilsonCapturedPrimaryPhysicalArray.registered x (some 0))=Y!:=by
  unfold WilsonThermometerUnitFilingRegistered.submitted source
  rw [sum_triples]
  let datum (t:T!×T!):=WilsonThermometerUnitFilingCylinder.source R A z (atOrigin t) (filled R z r φ Q t)
  calc
    _=∑t,μ! t • datum t:=by
      apply Finset.sum_congr rfl;intro t _
      unfold WilsonThermometerAlignedCells.mass;rw [Finset.sum_smul];apply Finset.sum_congr rfl;intro c _
      have loc : WilsonCapturedPrimaryPhysicalArray.registered (placedAt t c) (some (0:Fin 3))=atOrigin t:=by
        funext j;simp [WilsonCapturedPrimaryPhysicalArray.registered,placedAt,atOrigin]
      have off:offsets (placedAt t c)=t:=by simp [offsets,placedAt,atOrigin]
      dsimp only [];rw [loc];simp only [table,off,datum]
    _=_:=by
      rw [←WilsonThermometerSupportedCells.restricted (fun t:T!×T!=>μ! t≠0)
        (fun t=>μ! t • datum t) (by intro t h;simp [not_not.mp h])]
      apply Finset.sum_congr rfl;intro c _;simp only [datum,filled,dif_pos c.property]
      rfl

theorem continuous_source:Continuous (Y!):=by
  unfold source;rw [show (∑c:Grid R z r φ, μ! c.val • WilsonThermometerUnitFilingCylinder.source R A z (loc! c.val).origin (Q c))=_ from
    funext (fun U=>Finset.sum_apply U _ _)]
  exact continuous_finsetSum _ fun c _=>(admitted R A z (loc! c.val).origin (Q c)).const_smul _

include simple in
theorem deposited (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z) {b:ℕ} (live:b≤z.1) :
    credit R.family z.1 z.2 0 (Y!) b live =
      fun U=>∑c:Grid R z r φ,μ! c.val * (total (incoming R A simple live (loc! c.val) U) (Q c)).part full:=by
  unfold source;rw [IntrinsicProductLinearity.credit_sum R.family z.1 z.2 0 b live (fun c:Grid R z r φ=>μ! c.val)
    (fun c:Grid R z r φ=>WilsonThermometerUnitFilingCylinder.source R A z (loc! c.val).origin (Q c))
    (fun c:Grid R z r φ=>admitted R A z (loc! c.val).origin (Q c))]
  funext U
  rw [Finset.sum_apply U Finset.univ (fun c:Grid R z r φ=>μ! c.val •
    credit R.family z.1 z.2 0 (WilsonThermometerUnitFilingCylinder.source R A z (loc! c.val).origin (Q c)) b live)]
  apply Finset.sum_congr rfl;intro c _
  simp only [Pi.smul_apply,smul_eq_mul];apply congrArg (_*·)
  exact congrFun (WilsonThermometerUnitFilingInvoice.deposited R simple live A (Q c) qual (loc! c.val)) U

include simple in
theorem filed (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z) {u b:ℕ} (live:b≤z.1) (ub:u≤b)
    (door:Opened R.family 0 u z.2) (book:Booked R.family z.1 z.2 0 (Y!) u (ub.trans live)):
    report R (Y!) u=WilsonThermometerUnitFilingCoarse.reading R (N:=z.1)
      (fun U=>∑c:Grid R z r φ,μ! c.val*(total (incoming R A simple live (loc! c.val) U) (Q c)).part full) u ub:=by
  rw [WilsonThermometerUnitFilingCourse.filed R simple _ door (ub.trans live) book,
    ←deposited R simple A z r φ Q qual live]
  unfold WilsonThermometerUnitFilingCoarse.reading
  rw [WilsonThermometerUnitFilingCoarse.cutoff R live ub (Y!) (continuous_source R A z r φ Q)]

end YM.Integration.WilsonThermometerUnitFilingRelative
