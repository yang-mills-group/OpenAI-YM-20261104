import YM.MS.Landau

set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect.Mark
open Function Filter Set Finset Plane Koszul Real Momentum LogTime
open scoped Topology ContDiff
open Complex (I)
lemma kernel_zero (p:Momentum Axis) (a:Axis): ∑ k:Axis, precision k a p * p k=0:= by
   unfold precision delta; simp_rw [sub_mul,ite_mul]; simp [Finset.sum_sub_distrib]; unfold Momentum.sq; rw [Finset.sum_mul]; exact sub_eq_zero.mpr (Finset.sum_congr rfl (fun i _=>by ring))
lemma czero (p:Momentum Axis) (a:Axis) : ∑ k:Axis, (precision k a p:ℂ)*(p k:ℂ)=0:=by exact_mod_cast kernel_zero p a
end YM.MS.Landau.Detect.Mark
