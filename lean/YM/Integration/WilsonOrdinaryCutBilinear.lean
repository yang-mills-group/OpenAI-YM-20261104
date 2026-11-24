import YM.Integration.WilsonOrdinaryFiledPivot

/-! Numerical complex bilinearity under the normalized original Wilson
measure, with both measured microscopic source grades and original dates. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryCutBilinear
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryFiledGlyphs WilsonOrdinaryUltravioletPair
open WilsonOrdinaryPositionDecoder WilsonOrdinaryHomogeneousDetectors
variable {F : Final R.family f S} (L : Layout F) (d : ℕ)
variable {B : Deck G}


open MeasureTheory
open scoped ComplexConjugate

variable (R) (h : ℕ) (z : UVIndex) (x y : Site (R.family.side z.1 z.2))

/-- The complete normalized two-field finite Gibbs integral, without a
perturbative replacement and without an identically graded source assumption. -/
def integral (v : R.family.label h) (w : R.family.label d) : ℂ :=
  Wilson.moment (R.family.beta z.1 z.2) (fun U=>R.family.O z.1 z.2 v x U*R.family.O z.1 z.2 w y U)

private theorem add_left (a b : R.family.label h) (w : R.family.label d) :
    integral R d h z x y (a+b) w=integral R d h z x y a w+integral R d h z x y b w := by
  let μ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let K (v : R.family.label h) := fun U=>R.family.O z.1 z.2 v x U*R.family.O z.1 z.2 w y U
  have live v : Integrable (K v) μ := Wilson.continuous_integrable _ ((R.family.continuousO _ _ _ _ _).mul (R.family.continuousO _ _ _ _ _))
  change (∫ U,K (a+b) U ∂μ)=(∫ U,K a U ∂μ)+(∫ U,K b U ∂μ)
  rw [←integral_add (live a) (live b)]
  apply integral_congr_ae
  filter_upwards [] with U
  exact ((congrArg (fun t : ℂ=>t*(R.family.O z.1 z.2 w y U)) (congrFun ((R.family.linearO z.1 z.2 h x).map_add a b) U))).trans (add_mul _ _ _)

private theorem add_right (a : R.family.label h) (b c : R.family.label d) :
    integral R d h z x y a (b+c)=integral R d h z x y a b+integral R d h z x y a c := by
  let μ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let K (w : R.family.label d) := fun U=>R.family.O z.1 z.2 a x U*R.family.O z.1 z.2 w y U
  have live w : Integrable (K w) μ := Wilson.continuous_integrable _ ((R.family.continuousO _ _ _ _ _).mul (R.family.continuousO _ _ _ _ _))
  change (∫ U,K (b+c) U ∂μ)=(∫ U,K b U ∂μ)+(∫ U,K c U ∂μ)
  rw [←integral_add (live b) (live c)]
  apply integral_congr_ae
  filter_upwards [] with U
  exact ((congrArg (fun t : ℂ=>R.family.O z.1 z.2 a x U*t) (congrFun ((R.family.linearO z.1 z.2 d y).map_add b c) U))).trans (mul_add _ _ _)

private theorem smul_left (c : ℂ) (a : R.family.label h) (b : R.family.label d) :
    integral R d h z x y (c • a) b=c • integral R d h z x y a b := by
  let μ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let K (v : R.family.label h) := fun U=>R.family.O z.1 z.2 v x U*R.family.O z.1 z.2 b y U
  change (∫ U,K (c • a) U ∂μ)=c*(∫ U,K a U ∂μ)
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with U
  exact ((congrArg (fun t : ℂ=>t*(R.family.O z.1 z.2 b y U)) (congrFun ((R.family.linearO z.1 z.2 h x).map_smul c a) U))).trans (mul_assoc _ _ _)

private theorem smul_right (c : ℂ) (a : R.family.label h) (b : R.family.label d) :
    integral R d h z x y a (c • b)=c • integral R d h z x y a b := by
  let μ := Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)
  let K (w : R.family.label d) := fun U=>R.family.O z.1 z.2 a x U*R.family.O z.1 z.2 w y U
  change (∫ U,K (c • b) U ∂μ)=c*(∫ U,K b U ∂μ)
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with U
  exact ((congrArg (fun t : ℂ=>R.family.O z.1 z.2 a x U*t) (congrFun ((R.family.linearO z.1 z.2 d y).map_smul c b) U))).trans (mul_left_comm _ _ _)

/-- One original complex bilinear register for all signed counterterms, two
actual labels at their separate grades and all priory chosen physical sites. -/
def pairing : R.family.label h →ₗ[ℂ] R.family.label d →ₗ[ℂ] ℂ where
  toFun a := { toFun := integral R d h z x y a
               map_add' := add_right R d h z x y a
               map_smul' := fun c b=>smul_right R d h z x y c a b }
  map_add' a b := LinearMap.ext fun w=>add_left R d h z x y a b w
  map_smul' c a := LinearMap.ext fun w=>smul_left R d h z x y c a w

/-- The held right leg at its true reporting date remains a complex linear
function of its honest pre-reflection raw coefficient. -/
def transport (r : ℝ) (z : UVIndex) : R.family.label d→ₗ[ℂ]R.family.label d :=
  ((R.family.S.a (L.level r)^d : ℝ):ℂ) • (RG12.atK R.family F.room.cutoff d (L.level r) z).toLinearMap.comp (L.shift d r).toLinearMap

theorem transport_apply (r : ℝ) (z : UVIndex) (a : R.family.label d) :
    transport R L d r z a=RG17.atRef L d r z a := rfl

end YM.Integration.WilsonOrdinaryCutBilinear
