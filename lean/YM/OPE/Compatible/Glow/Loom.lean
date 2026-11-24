import YM.OPE.Compatible.Glyph.Ivory
/-!
# Spatial density row for the analytic Path series. Budget Hilbert proof-free. Stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}
namespace Script
open Page
-- paths power via one dimensional t Taylor on matrix paths, exponential. For any E power in picture and finite extension path. Goal derivative IN jets along any t, allow exp(length). prove using induction length & coefficient analyt radius global t ≤1. 
structure Street (σ:ℝ)(v:E→G.El)(Y:(ℕ→ℝ)) [NormedAddCommGroup E][NormedSpace ℝ E] (n:ℕ) :Prop where
   smooth : ContDiff ℝ n (G.mat∘ v)
-- contour test on ℝ family only
lemma runner (v:G.Color) : ContDiff ℝ ⊤ (fun t:ℝ=> G.mat (G.lieExp (t • v))):=by
   simp_rw [G.mat_lieExp,map_smul]; -- norm
   fun_prop
abbrev horse (t:G.Color)(x:ℝ):= G.mat (G.lieExp (x • t))
lemma horse_step (v:G.Color)(t:ℝ): deriv (horse v) t= horse v t*G.colorMat v:=by
   simp only [show horse v=fun t:ℝ=> NormedSpace.exp (t • G.colorMat v) from funext fun t=>by rw [horse,G.mat_lieExp,map_smul]]; rw [horse,G.mat_lieExp,map_smul]; exact (hasDerivAt_exp_smul_const (G.colorMat v) t).deriv -- polarity
lemma horseBound (v:G.Color)(t:ℝ): ‖horse v t‖=G.colorScale:= Gauge.unitary_frob (r:=G.repDim) (G.mat_mul_star _)
lemma riding (v:G.Color)(t:ℝ)(j): iteratedDeriv j (horse v) t=horse v t*G.colorMat v^j:=by
   induction j generalizing t with
   | zero=> simp only [iteratedDeriv_zero,pow_zero,mul_one]
   | succ j ih=>
      rw [iteratedDeriv_succ,funext (show ∀ t:ℝ,_ from ih),deriv_mul_const]; erw [horse_step v t,_root_.mul_assoc,pow_succ']; -- names
      exact (runner v).differentiable (by simp) t
lemma race (v:G.Color)(t:ℝ)(j): ‖iteratedDeriv j (horse v) t‖ ≤ max 1 G.colorScale*(G.colorScale*‖v‖)^j:=by
    cases j with
    | zero=> rw [iteratedDeriv_zero,pow_zero,mul_one,horseBound]; exact le_max_right ..
    | succ j=>
      rw [riding,Gauge.mul_frob_eq (A:=horse v t),← G.colorMat_norm]; apply le_trans (norm_pow_le' ..) (le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) (le_max_left ..)); omega
      exact G.mat_star_mul _ -- names
end Script
end YM.OPE.Flume
