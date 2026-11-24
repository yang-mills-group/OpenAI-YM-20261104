import YM.Integration.WilsonOrdinaryPositionDecoder

/-! Both quadratures of one independently supplied complex mixed slot are
recovered on the *same* original physical Gram. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryPhaseRecovery
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


open WilsonOrdinaryPositionDecoder
variable {U W E : Type*}
variable [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable (K : U→ₗ[ℂ]W→ₗ[ℂ]ℂ) (T : E→ₛₗ[starRingEnd ℂ]W)

/-- One real continuous mixed row, including the actual conjugate scaling
of the second (reflected) leg. -/
def ear (a : U) : E→L[ℝ]ℝ :=
  let v : E→ₗ[ℝ]ℝ := {
    toFun := fun y=>(K a (T y)).re
    map_add' x y := by simp
    map_smul' c y := by
      change (K a (T (c • y))).re=c*(K a (T y)).re
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),LinearMap.map_smulₛₗ]
      simp }
  v.toContinuousLinearMap

theorem adds (a b : U) : ear K T (a+b)=ear K T a+ear K T b := by
  ext y
  change (K (a+b) (T y)).re=(K a (T y)).re+(K b (T y)).re
  simp

theorem rotates (c : ℂ) (a : U) (y : E) :
    ear K T (c • a) y=ear K T a (star c • y) := by
  change (K (c • a) (T y)).re=(K a (T (star c • y))).re
  rw [map_smul,LinearMap.smul_apply,LinearMap.map_smulₛₗ,map_smul]
  simp

variable (F : Final R.family f S) (J : ℝ→tower S) (d : ℕ)
local notation "D!" => RG17.Free R.family d

/-- Complex multiplication in the genuine continuum first field moves,
conjugated, to the second input of the very same physical Gram. -/
theorem physical (r : ℝ) (c : ℂ) (v w : D!) :
    mixed F J d r r (c • v) w=mixed F J d r r v (star c • w) := by
  let Z := linear₂ (S.classMoment S (fun _ : Fin 2=>d) (r • detectors))
  let A := S.adj F.room.kernel.spin d timeAxis
  change (Z ((J r d) (c • v)) (A ((J r d) w))).re=(Z ((J r d) v) (A ((J r d) (star c • w)))).re
  simp [LinearMap.map_smulₛₗ]

/-- Complex-linear recovery is forced by the genuine original mixed bank
and its uniqueness. In particular the second quadrature uses the very same
physical field, which is necessary before summing complex signed fees. -/
theorem recover (r : ℝ) (D : (D!→L[ℝ]ℝ)→ₗ[ℝ]S.Field d)
    (read : ∀ p y,mixed F J d r r ((J r d).symm (D p)) y=p y)
    (unique : ∀ p x,(∀ y,mixed F J d r r ((J r d).symm x) y=p y) → x=D p)
    (P : D!→ₛₗ[starRingEnd ℂ]W) :
    ∃ X : U→ₗ[ℂ] S.Field d,∀ a,X a=D (ear K P a) := by
  refine ⟨{toFun := fun a=>D (ear K P a)
           map_add' := fun a b=>by rw [adds,map_add]
           map_smul' := ?_},fun _=>rfl⟩
  intro c a
  symm
  apply unique
  intro y
  rw [map_smul,physical,read]
  exact (rotates K P c a y).symm

end YM.Integration.WilsonOrdinaryPhaseRecovery
