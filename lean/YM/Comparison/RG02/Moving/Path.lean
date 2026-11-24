import YM.Comparison.RG02.Moving.Fibres
import YM.PertExtension.PTBills
/-! # `ℝ`-germ transformations at fixed period through finite order -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree YM.Next.Rank
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I J : Type} {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Path
variable {Z : Zone X} {W : X → ℝ} {f : ℝ→X→E} {p : ℝ→X}
omit [NormedSpace ℝ X] [NormedSpace ℝ E] in
lemma encounter (hw : ContinuousAt W (p 0)) (hz : ContinuousAt Z.w (p 0)) (hp : ContinuousAt p 0)
    {k : ℕ} (h : Z.Fits W k f) : Bill k (fun t=>f t (p t)):= by
   obtain ⟨δ,C,m,hδ,hC,H⟩:=h.cost
   let q t := C*Z.w (p t)^m * W (p t)
   have hq : ContinuousAt q 0 := (continuousAt_const.mul ((hz.comp hp).pow _)).mul (hw.comp hp)
   have he : 0 ≤ q 0:= mul_nonneg (mul_nonneg hC (pow_nonneg (zero_le_one.trans (Z.high _)) _)) (zero_le_one.trans (h.envelope _))
   refine ⟨q 0+1,by positivity,?_⟩; have hh : along≤𝓝 0:= nhdsWithin_le_nhds
   filter_upwards [hh (hq.eventually (gt_mem_nhds (by simp : q 0 < q 0 +1))), hh ((show ContinuousAt (fun x:ℝ=>x*Z.w (p x)) 0 from continuousAt_id.mul (hz.comp hp)).eventually
       (gt_mem_nhds (show 0*Z.w (p 0) < δ by rw [zero_mul]; exact hδ))),Tested.eventually_pos] with t hx hy hs
   exact (H _ _ hs hy.le).trans (mul_le_mul_of_nonneg_right hx.le (pow_nonneg hs.le _))
variable [FiniteDimensional ℝ X]
lemma examined {f:X→ℂ} (hx : ContDiffAt ℝ ∞ f 0) (x : X) : Aspiration (fun t:ℝ=>f (t • x)) (fun n=>Assembly.jet f n x):=
   fun n=> encounter (Z:=Radial.zone (E:=X)) (W:=1) (by exact continuousAt_const) (by exact continuousAt_const.add continuous_norm.continuousAt) (show ContinuousAt (fun t:ℝ=>x) 0 from continuousAt_const) ((Assembly.built_jet hx).fits n)

abbrev motion (f:ℝ→ℂ) (k:ℕ) := Assembly.jet f k 1
lemma ordinary {f:ℝ→ℂ} (h : ContDiffAt ℝ ∞ f 0) : Aspiration f (motion f) := by
   convert! examined h (1:ℝ) using 1; simp only [smul_eq_mul,mul_one]

lemma effort {I : Type} [Fintype I] [DecidableEq I] (C : Field X I) (x : X) : ContinuousAt (C.link x) 0 := by
   have he : ContinuousAt C.B (0, (0:ℝ) • x) := by rw [zero_smul]; exact C.B_smooth.continuousAt
   refine he.comp (f:=fun t:ℝ=> (t,t•x)) ?_
   · exact continuousAt_id.prodMk (continuousAt_id.smul continuousAt_const)

end Path
end YM.Comparison.RG02.Moving
