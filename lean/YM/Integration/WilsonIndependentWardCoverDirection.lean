import YM.Integration.WilsonIndependentWardSingleSlope
import YM.Integration.WilsonIndependentWardLocalStamp

/-! The local real trace of a covariant vector at one directed link.
It is the trace of its actual derivative, before pivot projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardCoverDirection
open Finset Function Lattice Wilson RG Source WardBin FormalOPE.RG10.InversionWard
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
  {S:Finset Cover}{n:Side}

theorem regular (f:CoverConfig G→E)(loc:LocalOn S f)(o:Site n)(fit:FitsIn S n)
    (paid:Proxy (places o f))(e:Edge Cover)(U:CoverConfig G) :
    ContDiff ℝ ∞ (fun y=>f (WardBin.slide e U y)) := by
  obtain ⟨A,hA,eq⟩:=paid
  have val:f=fun U=>A (image (above o U)) := by
    funext U
    rw [←fromAbove loc fit o U,eq]
    rfl
  rw [val]
  apply hA.comp
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ ∞ (fun y:G.Color=>G.mat (WardBin.slide e U y (Lattice.lift (i.1-o),i.2)))
  by_cases h:(Lattice.lift (i.1-o),i.2)=e
  · simp only [h,WardBin.slide,Function.update_self,G.mat_mul]
    exact (G.exp_jet.of_le le_top).mul contDiff_const
  · simp only [WardBin.slide,Function.update_of_ne h]
    exact contDiff_const

variable (e:Edge Cover)(X:CoverConfig G→G.Color)
def derivative (U:CoverConfig G) := fderiv ℝ (fun y=>X (WardBin.slide e U y)) 0
def emission (U:CoverConfig G) : ℝ := ∑ i, slope e (dirs G i) (fun v=>⟪dirs G i,X v⟫_ℝ) U

variable (line:∀U,ContDiff ℝ ∞ (fun y=>X (WardBin.slide e U y)))
  (covar:∀(t:Cover→G.El)(U:CoverConfig G),X (Lattice.gauge t U)=G.adjoint (t e.1) (X U))

include line in
theorem along (U:CoverConfig G)(a:G.Color) : HasDerivAt (fun t:ℝ=>X (WardBin.slide e U (t • a)))
    (derivative e X U a) 0 := by
  have he:HasDerivAt (fun t:ℝ=>t • a) a 0:=by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a
  exact (((line U).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0 he (by simp)

include line covar in
theorem rotate (t:Cover→G.El)(U:CoverConfig G)(a:G.Color) :
    derivative e X (Lattice.gauge t U) (G.adjoint (t e.1) a)=
      G.adjoint (t e.1) (derivative e X U a) := by
  let L:=LinearMap.toContinuousLinearMap (G.adjoint (t e.1))
  apply (along e X line (Lattice.gauge t U) (G.adjoint (t e.1) a)).unique
  simp_rw [←map_smul,WardBin.slide_gauge,covar]
  exact L.hasFDerivAt.comp_hasDerivAt 0 (along e X line U a)

include line in
theorem trace_on (U:CoverConfig G)(B:OrthonormalBasis G.ColorIndex ℝ G.Color) :
    emission e X U=∑ i, ⟪B i,derivative e X U (B i)⟫_ℝ := by
  have he(i:G.ColorIndex):slope e (dirs G i) (fun v=>⟪dirs G i,X v⟫_ℝ) U =
      ⟪dirs G i,derivative e X U (dirs G i)⟫_ℝ :=
    ((innerSL ℝ (dirs G i)).hasFDerivAt.comp_hasDerivAt 0 (along e X line U (dirs G i))).deriv
  unfold emission
  simp_rw [he]
  change (∑ i:G.ColorIndex,Inner.inner ℝ ((dirs G) i) ((derivative e X U).toLinearMap ((dirs G) i))) =
    ∑ i:G.ColorIndex,Inner.inner ℝ (B i) ((derivative e X U).toLinearMap (B i))
  rw [←LinearMap.trace_eq_sum_inner,←LinearMap.trace_eq_sum_inner]

include line covar in
theorem invariant : GaugeInvariant (emission e X) := by
  intro t U
  let L:=WardBin.adjointGauge (t e.1)
  let B:=(dirs G).map L
  rw [trace_on e X line (Lattice.gauge t U) B,trace_on e X line U (dirs G)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show B i=G.adjoint (t e.1) (dirs G i) from by unfold B; rw [OrthonormalBasis.map_apply]; rfl,
    rotate e X line covar]
  exact L.inner_map_map ..

end YM.Integration.WilsonIndependentWardCoverDirection
