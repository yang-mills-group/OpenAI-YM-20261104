import YM.Integration.WilsonMeasuredSignedActionPhysical
import YM.Integration.WilsonMeasuredPublicEntranceActionLimit
/-! The finite relative matrix comparison can be absorbed against the
bounded measured vector. The input vote and its scalar can be unbounded. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionReported
open Function Filter Finset Labels Extra.Histories
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open scoped Topology BigOperators Classical
variable {G:Gauge}(F:Frame G 4)

theorem continuous_pool:Continuous (pool F):=by
  unfold pool
  apply continuous_finsetSum
  intro s _
  exact (F.act s.ortho).continuous_of_finiteDimensional.comp (continuous_id.add continuous_star)

private theorem size_zero:F.coeffSize 0=0:=by simp [Frame.coeffSize]

theorem relative {I:Type*}{l:Filter I}{x b:I→F.Coeff}{η:I→ℝ}{D:ℝ}
    (rate:Tendsto η l (𝓝 0))(pos:∀ᶠ i in l,0 ≤ η i)
    (bounded:∀ᶠ i in l,F.coeffSize (b i)≤D)
    (paid:∀ᶠ i in l,F.coeffSize (x i-b i)≤η i*F.coeffSize (x i)):
    Tendsto (fun i=>x i-b i) l (𝓝 0):=by
  have gross:Tendsto (fun i=>η i*D/(1-η i)) l (𝓝 0):=by
    simpa [Pi.div_def] using (rate.mul_const D).div (tendsto_const_nhds.sub rate) (by norm_num:(1:ℝ)-0≠0)
  apply squeeze_zero_norm' _ gross
  filter_upwards [rate.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),pos,bounded,paid] with i small nonneg size earnings
  have zero:F.coeffSize (b i-b i)≤0:=by rw [sub_self,size_zero]
  have price:=WilsonMeasuredSignedActionDebits.relative F (x i) (b i) (b i) nonneg small zero earnings
  rw [zero_add] at price
  exact ((Push.Local.norm_le_size F _).trans price).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left size nonneg) (sub_nonneg.mpr small.le))

theorem converges {I:Type*}{l:Filter I}[NeBot l]{w b:I→F.Coeff}{a:I→ℝ}{y:F.Coeff}
    (positive:∀ᶠ i in l,0 ≤ a i)
    (enrolled:∀ᶠ i in l,∃k:ℝ,0 ≤ k ∧ F.core (pool F (w i))=(k:ℂ) • axis F)
    (pretest:Tendsto b l (𝓝 y))
    (error:Tendsto (fun i=>(a i:ℂ) • F.core (w i)-F.core (b i)) l (𝓝 0)):
    ∃s:ℝ,0 ≤ s ∧ F.core (pool F y)=(s:ℂ) • axis F:=by
  let z:=fun i=>(a i:ℂ) • F.core (w i)
  have through:Tendsto (fun i=>F.core (b i)) l (𝓝 (F.core y)):=
    F.core.continuous_of_finiteDimensional.continuousAt.tendsto.comp pretest
  have shift:Tendsto z l (𝓝 (F.core y)):=by simpa only [z,sub_add_cancel,zero_add] using error.add through
  have weighed:∀ᶠ i in l,∃k:ℝ,0 ≤ k ∧ ∃c:ℂ,pool F (z i)=k • axis F+c • (0:F.Coeff):=by
    filter_upwards [positive,enrolled] with i fi inc
    obtain ⟨k,hk,paid⟩:=inc
    refine ⟨a i*k,mul_nonneg fi hk,0,?_⟩
    change pool F ((a i:ℂ) • F.core (w i))=_
    rw [WilsonMeasuredSignedActionWindow.scale,←WilsonMeasuredSignedActionAverage.core,paid,smul_smul,
      ←Complex.ofReal_mul,Complex.coe_smul,smul_zero,add_zero]
  obtain ⟨s,hs,c,eq⟩:=WilsonMeasuredPublicEntranceActionLimit.original
    ((continuous_pool F).continuousAt.tendsto.comp shift) weighed
  refine ⟨s,hs,?_⟩
  rw [WilsonMeasuredSignedActionAverage.core,Complex.coe_smul]
  simpa only [smul_zero,add_zero] using eq

end YM.Integration.WilsonMeasuredSignedActionReported
end
