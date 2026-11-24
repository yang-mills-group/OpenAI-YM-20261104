import YM.Integration.WilsonPositionScaleLawMeasuredIFT
import YM.Integration.WilsonPositionScaleLawMeasuredAxes
import YM.Integration.WilsonPositionScaleLawMeasuredIntegral
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredContour
open Filter Function Set MeasureTheory Metric
open scoped Topology Interval ContDiff Classical
open WilsonPositionScaleLawMeasuredIntegral (line)
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
def matrix (D:E→E) (x:E) : E≃L[ℝ]E :=
  if h:∃A:E≃L[ℝ]E,A.toContinuousLinearMap=fderiv ℝ D x then h.choose else ContinuousLinearEquiv.refl ℝ E
omit [CompleteSpace E] in
theorem actual (D:E→E) (x:E) (A:E≃L[ℝ]E) (eqn:A.toContinuousLinearMap=fderiv ℝ D x) :
    matrix D x=A := by
  have haveA:∃B:E≃L[ℝ]E,B.toContinuousLinearMap=fderiv ℝ D x:=⟨A,eqn⟩
  rw [matrix,dif_pos haveA]
  apply ContinuousLinearEquiv.ext
  funext v
  exact congrArg (fun L:E→L[ℝ]E=>L v) (haveA.choose_spec.trans eqn.symm)
variable (D:E→E)(s:ContDiff ℝ ω D)(b:E)(ground:fderiv ℝ D b=1)
include s ground in
theorem regular : ∀ᶠx in 𝓝 b,
    (matrix D x).toContinuousLinearMap=fderiv ℝ D x ∧ ‖(matrix D x).symm.toContinuousLinearMap‖≤2 := by
  filter_upwards [WilsonPositionScaleLawMeasuredAxes.quantitative D s b ground] with x h
  obtain ⟨A,ha,fee⟩:=h
  rw [actual D x A ha]
  exact ⟨ha,fee⟩
def contrast (H:E→V)(rev:E→E)(z w:E)(cash:V) : V :=
  cash-H z-(∫u in (0:ℝ)..1, let x:=rev (line (D z) w u)
    fderiv ℝ H x ((matrix D x).symm (w-D z)))
def inverse (D:E→E)(s:ContDiff ℝ ω D)(b:E)(ground:fderiv ℝ D b=1) : E→E :=
  WilsonPositionScaleLawMeasuredIFT.elected D s b (by rw [ground];exact ContinuousLinearMap.isInvertible_equiv (f:=ContinuousLinearEquiv.refl ℝ E))
theorem radius :
    ∃R:ℝ,0<R ∧ ∀y∈ball (D b) R, let rev:=inverse D s b ground
      ContDiffAt ℝ ω rev y ∧ D ∘ rev =ᶠ[𝓝 y] id ∧
      (matrix D (rev y)).toContinuousLinearMap=fderiv ℝ D (rev y) ∧
      ‖(matrix D (rev y)).symm.toContinuousLinearMap‖≤2 := by
  let rev:=inverse D s b ground
  have first:rev (D b)=b:=WilsonPositionScaleLawMeasuredIFT.base ..
  have smooth:ContDiffAt ℝ ω rev (D b):=WilsonPositionScaleLawMeasuredIFT.smooth ..
  have back:=smooth.continuousAt.tendsto
  rw [first] at back
  have law:D ∘ rev =ᶠ[𝓝 (D b)] id:=WilsonPositionScaleLawMeasuredIFT.near ..
  obtain ⟨R,pos,ok⟩:=Metric.mem_nhds_iff.mp ((smooth.eventually (by simp)).and
    ((eventually_eventually_nhds.mpr law).and (back.eventually (regular D s b ground))))
  exact ⟨R,pos,fun _ h=>ok h⟩
theorem localized (valid:E→Prop)(earned:∀ᶠx in 𝓝 b,valid x) :
    ∃R:ℝ,0<R ∧ ∀ᶠz in 𝓝 b, D z∈ball (D b) R ∧
      ∀w∈ball (D b) R,∀H:E→V,(∀x,valid x→ContDiffAt ℝ ω H x)→∀cash:V,
        contrast D H (inverse D s b ground) z w cash=cash-H (inverse D s b ground w) := by
  let rev:=inverse D s b ground
  obtain ⟨Q,qp,inside⟩:=radius D s b ground
  have center:rev (D b)=b:=WilsonPositionScaleLawMeasuredIFT.base ..
  have cont:ContinuousAt rev (D b):=(WilsonPositionScaleLawMeasuredIFT.smooth ..).continuousAt
  have coming:=cont.tendsto
  rw [center] at coming
  have there:∀ᶠy in 𝓝 (D b),y∈ball (D b) Q:=Metric.ball_mem_nhds _ qp
  have both:{y:E|y∈ball (D b) Q ∧ valid (rev y)}∈𝓝 (D b):=there.and (coming.eventually earned)
  obtain ⟨R,pos,cover⟩:=Metric.mem_nhds_iff.mp both
  have restricted (y:E)(hy:y∈ball (D b) R):y∈ball (D b) Q ∧ valid (rev y):=cover hy
  have localData (y:E)(hy:y∈ball (D b) R):=inside y (restricted y hy).1
  have holds (y:E)(hy:y∈ball (D b) R):valid (rev y):=(restricted y hy).2
  refine ⟨R,pos,?_⟩
  have prior:∀ᶠz in 𝓝 b,rev (D z)=z:=WilsonPositionScaleLawMeasuredIFT.recovers ..
  filter_upwards [s.continuous.continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ pos),prior] with z start back
  refine ⟨start,?_⟩
  intro w cap H smooth cash
  let path:=line (D z) w
  have along (u:ℝ)(hu:u∈uIcc (0:ℝ) 1):path u∈ball (D b) R := by
    have interval:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hu
    exact (convex_ball (D b) R).add_smul_sub_mem start cap interval
  have target (u:ℝ)(hu:u∈uIcc (0:ℝ) 1):DifferentiableAt ℝ H (rev (path u)):=
    (smooth _ (holds _ (along u hu))).differentiableAt (by simp)
  have left (u:ℝ)(hu:u∈uIcc (0:ℝ) 1):HasFDerivAt D (matrix D (rev (path u))).toContinuousLinearMap (rev (path u)) := by
    rw [(localData _ (along u hu)).2.2.1]
    exact (s.differentiable (by simp) _).hasFDerivAt
  have chain (u:ℝ)(hu:u∈uIcc (0:ℝ) 1):HasFDerivAt rev (matrix D (rev (path u))).symm.toContinuousLinearMap (path u) :=
    WilsonPositionScaleLawMeasuredIntegral.inverse D rev _ _ (left u hu)
      ((localData _ (along u hu)).1.differentiableAt (by simp)) (localData _ (along u hu)).2.1
  have liquid : IntervalIntegrable (fun u=>let x:=rev (path u);fderiv ℝ H x ((matrix D x).symm (w-D z))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    have through : Continuous path := by unfold path line;fun_prop
    apply (show ContinuousOn (fun u=>fderiv ℝ (H ∘ rev) (path u) (w-D z)) (uIcc (0:ℝ) 1) from ?_).congr
    · intro u hu
      have eqn:=((target u hu).hasFDerivAt.comp (path u) (chain u hu)).fderiv
      exact (congrArg (fun L:E→L[ℝ]V=>L (w-D z)) eqn).symm
    intro u hu
    exact ((((smooth _ (holds _ (along u hu))).comp _ (localData _ (along u hu)).1).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
      |>.comp through.continuousAt).continuousWithinAt
  exact WilsonPositionScaleLawMeasuredIntegral.exactContrast D H rev (matrix D) z w cash back left
    (fun u hu=>(localData _ (along u hu)).1.differentiableAt (by simp))
    (fun u hu=>(localData _ (along u hu)).2.1) target liquid
theorem original :
    ∃R:ℝ,0<R ∧ ∀ᶠz in 𝓝 b, D z∈ball (D b) R ∧
      ∀w∈ball (D b) R,∀H:E→V,ContDiff ℝ ω H→∀cash:V,
        contrast D H (inverse D s b ground) z w cash=cash-H (inverse D s b ground w) := by
  obtain ⟨R,pos,ready⟩:=localized (V:=V) D s b ground (fun _=>True) (Eventually.of_forall fun _=>trivial)
  refine ⟨R,pos,?_⟩
  filter_upwards [ready] with z measured
  exact ⟨measured.1,fun w hw H smooth cash=>measured.2 w hw H (fun _ _=>smooth.contDiffAt) cash⟩
end YM.Integration.WilsonPositionScaleLawMeasuredContour
