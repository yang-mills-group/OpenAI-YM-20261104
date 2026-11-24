import YM.Comparison.RG02.Adjacent.Sale
import YM.Comparison.RG02.Assembly.Shift
import YM.Work.G05.Taylor

/-! Taylor expansion of the original projected group germ under a marked clock. -/
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedTaylor
open YM RG Lattice Comparison.RG02 Assembly Moving Moving.Path Adjacent Work.G05
open scoped Topology BigOperators Classical ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem remainder (F:E→ℂ) (N:ℕ) (smooth:ContDiffAt ℝ ω F 0):
    GradeAt (N+1) (F-blockTaylor N F):=by
  constructor
  · exact smooth.sub (blockTaylor_contDiff N F ω).contDiffAt
  · intro i hi
    rw [iteratedFDeriv_sub_apply (smooth.of_le le_top) (blockTaylor_contDiff N F i).contDiffAt,
      blockTaylor_jets (smooth.of_le (show (N:WithTop ℕ∞)≤ω from le_top)) i (by omega),sub_self]

theorem sum (F:E→ℂ) (m r:ℕ) (grade:GradeAt m F) (x:E):
    blockTaylor (m+r) F x=∑ i∈Finset.range (r+1),jet F (m+i) x:=by
  change (∑ j∈Finset.range (m+r+1),Tensor.diagonal (Tensor.coeff F j 0)) x=_
  simp only [Finset.sum_apply]
  change ∑ j∈Finset.range (m+r+1),jet F j x=_
  rw [show m+r+1=m+(r+1) by omega,Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun i hi=>grade.jet_z x (Finset.mem_range.mp hi)),zero_add]

theorem ages (F:ℝ×E→ℂ) (m r:ℕ) (grade:GradeAt m F) (B:E) (t u:ℝ) (unit:u≠0):
    (↑(u^m)⁻¹:ℂ)*blockTaylor (m+r) F (t*u,t • B)=
      (t:ℂ)^m*Adjacent.ages (fun i x=>jet F (m+i) (1,x)) 0 r t u B:=by
  have point : ((t*u,t • B):ℝ×E)=(t*u) • ((1:ℝ),u⁻¹ • B):=by
    ext <;> simp [smul_smul,unit]
  rw [sum F m r grade,point]
  simp only [Clipper.weight,Complex.real_smul,Adjacent.ages,Adjacent.cover,zpow_zero,
    Complex.ofReal_one,one_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  have cu : (u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr unit
  simp only [pow_add,mul_pow]
  field_simp [cu]

end YM.Integration.WilsonOriginalProjectedTaylor
end
