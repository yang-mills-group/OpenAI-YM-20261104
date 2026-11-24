import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NegativePupil

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleColors
open YM YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position
open scoped InnerProductSpace BigOperators
variable (g:YangMills.GaugeGroup)

theorem original : Cubic.colorNorm (IssuedMaxwell.Reference.issued g)=S_color g.core:=by
  unfold Cubic.colorNorm S_color
  refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>?_
  apply congrArg (fun a:ℝ=>a^2)
  let basis (a:g.core.ColorIndex):g.core.Color := EuclideanSpace.single a 1
  change -((g.core.colorMat (basis i) * (g.core.colorMat (basis j) * g.core.colorMat (basis k) -
    g.core.colorMat (basis k) * g.core.colorMat (basis j))).trace.re) /
    (g.core.repDim:ℝ) = br (G:=g.core) i j k
  rw [← g.core.colorMat_ad,g.core.trace_color,← inB]
  have hn : (g.core.repDim:ℝ) ≠ 0 :=by change ((g.n+1:ℕ):ℝ)≠0;positivity
  have field (a:g.core.ColorIndex) : basis a=Chart2.basisC g.core a:=by
    ext c
    simp [basis,Chart2.basisC,EuclideanSpace.basisFun_apply]
  rw [field i,field j,field k]
  field_simp
end IssuedMaxwell.TriangleColors
end
