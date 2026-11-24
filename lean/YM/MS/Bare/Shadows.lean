import YM.Gauge.MatrixGroup

noncomputable section
namespace YM.MS.Bare.Maurer
open scoped Matrix.Norms.Frobenius
variable {G : Gauge}

def runmat (u:G.El): G.Mat→L[ℝ] G.Mat:= ((ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat u⁻¹)) ∘L ((ContinuousLinearMap.mul ℝ G.Mat) (G.mat u))
lemma runprod (u:G.El)(a b:G.Mat): runmat u (a*b)=runmat u a * runmat u b:= by
    change G.mat u*(a*b)*G.mat u⁻¹=G.mat u*a*G.mat u⁻¹*(G.mat u*b*G.mat u⁻¹); simp_rw [mul_assoc,G.mat_inv u, ← mul_assoc (star _),G.mat_star_mul]; simp
end YM.MS.Bare.Maurer
