import YM.AllOrder.Floe.Crest
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Crest
/-! Choose curvature book through all orders *before* L restriction. Takes peak.T.Purchase implied basis via canon. Keep regulator link unmasked & Symm actions. -/
open WilsonStartup WilsonStartup.Design WilsonStartup.Padded Work Tensor
variable (p:Clip)
/-! residual at arbitrary order of top, flat & regular. -/
abbrev fill (m:ℕ)(u:G.El):=∑ k∈range m,channel (k+5) u
def short (m:ℕ)(u:G.El):= surplus u-fill m u
lemma fill_succ (m:ℕ)(u:G.El): fill (m+1) u=fill m u+channel (m+5) u:= Finset.sum_range_succ ..
lemma tally (m:ℕ)(u:G.El) : G05.blockTaylor (m+4) (inK G) (G.curvature u)=G05.blockTaylor 4 (inK G) (G.curvature u)+fill m u:= by induction m with
 | zero=> simp [fill]
 | succ k ih=> rw [show G05.blockTaylor (k+1+4) (inK G) (G.curvature u)=G05.blockTaylor (k+4) (inK G) (G.curvature u)+channel (k+5) u by unfold G05.blockTaylor; rw [Finset.sum_range_succ]; rfl,fill_succ,ih,add_assoc]
theorem collation {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](U:Y→G.El) (h:U 0=1) (hM:ContDiffAt ℝ ω (fun x=>G.mat (U x)) 0)(m:ℕ): FlatAt (m+5) (short m ∘ U) 0:= by
 have hc : ContinuousAt U 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hM.continuousAt
 let k:=fun x=>G.curvature (U x); have hz:k 0=0:=by simp only [k,h,G.curvature_unit]
 apply FlatAt.congr (g:=short m ∘ U) (FlatAt.comp (f:=inK G-G05.blockTaylor (m+4) (inK G)) (u:=k) (hz.symm ▸ flat_sub_taylor _ (m+4) (inK_diff.of_le le_top)) (by rw [hz]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff .. |>.contDiffAt)) ((curvature_diff_mat U 0 hM).of_le le_top));
 filter_upwards [(show Tendsto U (𝓝 0) (𝓝 1) from h ▸ hc.tendsto).eventually (recover_left G)] with i hi; simp only [Function.comp_apply,Pi.sub_apply, k]; rw [tally,convert_taylor,inK,hi,short,surplus]; ring
-- definition for comparing true radii; no mask derivatives invoked
namespace PhaseK
def ambient (m:ℕ)(X:G.Mat):= Quad.surplusMat X- ∑ k∈range m,Tensor.diagonal (Tensor.coeff (inK G) (k+5) 0) (Quad.kMat X)
lemma ambient_actual (u:G.El)(m:ℕ): ambient m (G.mat u)=short m u := by unfold ambient short fill; simp only [Quad.surplus_actual,Quad.k_actual]
lemma diff (m:ℕ): ContDiff ℝ ω (ambient (G:=G) m):= Quad.surplusMat_diff.sub (ContDiff.sum fun i _=> ((diag_smooth _ _).comp Quad.kMat_diff))
end PhaseK
end Crest
end YM.AllOrder.Floe
