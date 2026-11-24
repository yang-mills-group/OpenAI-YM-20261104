import YM.MS.Bare.Shadows
import YM.MS.Color.Components
import YM.MS.Wilson.LieWords

set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Paint
open Function Set Filter Finset Plane Koszul Bare Focus Landau
open scoped Topology ContDiff
variable {G:Gauge} (u:G.El)
local notation "T"=> weight u
local notation "C"=> CI G
lemma paletteC (i:C) : ∑ k, T i k • baseC k= G.adjoint u (baseC i):= color_sum _
lemma acts_all (x:G.Color)(i:C): G.adjoint u x i=∑ j:C, T j i*x j:= by
    nth_rw 1 [← color_sum x]; rw [map_sum,WithLp.ofLp_sum,Finset.sum_apply]; simp only [map_smul,PiLp.smul_apply,smul_eq_mul]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma weight_ad (x y:G.Color) : G.ad (G.adjoint u x) (G.adjoint u y)=G.adjoint u (G.ad x y):= by
   apply G.colorMat_injective; simp_rw [Gauge.colorMat_ad,Gauge.mat_adjoint, Gauge.colorMat_ad]
   -- use runmat
   have he (z:G.Mat): G.conjugate u z=Maurer.runmat u z := by simp [Gauge.conjugate,Maurer.runmat]; rfl
   simp only [he,map_sub,Maurer.runprod]
lemma tensorT (a b c:C): ∑ i:C,∑ j:C,T a i*T b j*letterLie i j c = ∑ k:C,letterLie a b k*T k c:= by
   have he := congr_arg (fun x:G.Color=> x c) (weight_ad u (baseC a) (baseC b)); dsimp only at he; nth_rw 1 [← paletteC u a,← paletteC u b] at he
   simp only [map_sum,map_smul,LinearMap.sum_apply, LinearMap.smul_apply,Finset.smul_sum, smul_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul] at he; rw [acts_all] at he
   rw [Finset.sum_comm]; simp_rw [mul_comm (T a _) (T b _)]; exact Eq.trans he (Finset.sum_congr rfl fun i _=> mul_comm ..)
end YM.MS.Native.Paint
