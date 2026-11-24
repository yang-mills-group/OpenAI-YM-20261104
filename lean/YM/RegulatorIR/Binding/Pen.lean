import YM.RegulatorIR.Binding.Gauges

/-! Quadratic path stencil at the actual penalty. Step ratios are all expressed
in a common coupling t; baking multiplies *both* Wilson and prior block
noise with independently stated weights at each step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision Work Series.Radial
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {f c: Side} {G:Gauge}
variable (S:StepData c f) (H:S.patch.Branches S.kernel G)

def burn (x:Horizon G f)(y:Horizon G c):ℝ:=bond S (climb x) (climb y)
def feeO (x:Horizon G f)(y:Horizon G c):ℝ:= S.kernel.penalty*∑ i:OEdge c, ‖(y-rod G S x) i‖^2/2
include H
lemma burn_at_zero : burn S (0:Horizon G f) 0=0:=by rw [burn,show climb (0:Horizon G f)=1 from expOrigin .., show climb (0:Horizon G c)=1 from expOrigin ..]; exact null_here S H
lemma burn_smooth : ContDiffAt ℝ ω (fun z: Horizon G f × Horizon G c=> burn S z.1 z.2) 0:=by
 unfold burn bond trouble; apply ContDiffAt.mul contDiffAt_const; apply ContDiffAt.sum;intro x _;apply F03.price_smooth
 simp only [G.mat_mul,G.mat_inv]; apply ContDiffAt.mul
 · exact G.exp_jet.contDiffAt.comp _ ((contDiffAt_apply ℝ G.Color x (0:Horizon G c)).comp (f:=Prod.snd) (0:Horizon G f × Horizon G c) contDiffAt_snd)
 have hp:= (mast S H x).comp (f:=Prod.fst) (0:Horizon G f × Horizon G c) contDiffAt_fst
 exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ hp)
lemma smoke (x:Horizon G f)(y:Horizon G c): Tendsto (fun t:ℝ=> burn S (t • x) (t • y)/t^2) (𝓝[≠] 0) (𝓝 (feeO S x y)):=by
 let V (t:ℝ)(i: OEdge c):= climb (t • y) i*(predictor S (climb (t • x)) i)⁻¹
 have hx : climb ((0:ℝ) • x)=1:= by rw [zero_smul];exact expOrigin ..
 have hh : climb ((0:ℝ) • y)=1:=by rw [zero_smul];exact expOrigin ..
 have hz(i: OEdge c): V 0 i=1:=by unfold V; rw [hh,hx,predict_zero S H];simp
 have ht(i: OEdge c) : HasDerivAt (fun t:ℝ=>G.mat (V t i)) (G.colorMat ((y-rod G S x) i)) 0:= by
    unfold V
    have hu: HasDerivAt (fun t:ℝ=>G.mat (climb (t • y) i)) (G.colorMat (y i)) 0:= vertical_deriv _
    simp_rw [G.mat_mul,G.mat_inv]; apply (hu.mul (bend S H x i).star).congr_deriv
    rw [hh,hx,predict_zero S H]; simp only [Pi.one_apply,G.mat_one,star_one,one_mul,mul_one,Pi.sub_apply,map_sub,colorMat_skew]; abel
 unfold burn bond trouble; simp_rw [mul_div_assoc, Finset.sum_div]; exact Tendsto.const_mul _ (f:=fun t=> ∑ i:OEdge c,G.price (V t i)/t^2) (tendsto_finsetSum _ (fun i _=> F03.price_limit (hz i) (ht i)))
omit H in
lemma feeO_nonneg (x:Horizon G f)(y:Horizon G c) : 0≤ feeO S x y:= mul_nonneg S.kernel.penalty_pos.le (by positivity)
omit H in
lemma feeO_eq (x:Horizon G f)(y:Horizon G c)(h:feeO S x y=0): y= rod G S x:=by
 ext1 i
 have hP := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=> show 0 ≤ ‖(y-rod G S x) i‖^2/2 by positivity)).mp ((mul_eq_zero.mp h).resolve_left S.kernel.penalty_pos.ne') i (Finset.mem_univ _)
 rw [← sub_eq_zero];exact norm_eq_zero.mp (le_antisymm (by change ‖(y-rod G S x) i‖≤0;nlinarith) (norm_nonneg _))
end YM.RegulatorIR.Binding
