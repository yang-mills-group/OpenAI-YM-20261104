import YM.Pert.Triangle.Price
/-! Auxiliary nonperturbative-in-geometry step to find some separated locations with nonzero integral of the *symmetric* contracted pair of potential lines. Uses a temporary spatial average and its positivity, not a numerical value of the fundamental-solution constant. The proof concerns only free Green integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical ENNReal
local notation "I3" => Fin 3

def stub := closedBall (0:E4) 1
def outerBall := closedBall (0:E4) 5
def birth := Metric.ball ((3:ℝ) • along) 1
@[simp] lemma stubCompact : IsCompact stub := isCompact_closedBall ..
@[simp] lemma outerBallCompact : IsCompact outerBall := isCompact_closedBall ..
lemma birthPositive : volume birth ≠ 0 := (measure_ball_pos _ ((3:ℝ) • along) (by norm_num : (0:ℝ)<1)).ne' -- outZ unavailable
lemma stubPositive : volume stub ≠ 0 := (lt_of_lt_of_le (measure_ball_pos _ (0:E4) (by norm_num : (0:ℝ)<1)) (measure_mono ball_subset_closedBall)).ne'
variable (a : Axis)
def rock (s : E4 × E4) : ℝ := if s.fst ∈ stub then flow a (s.snd-s.fst) else 0
def circle (w : E4) : ℝ := ∫ x, ‖rock a (x,w)‖
def mean (w : E4) : ℝ := ∫ x, rock a (x,w)
lemma rockMeasurable : Measurable (rock a) := Measurable.ite (measurable_fst (isClosed_closedBall.measurableSet)) ((rayMeasurable (flow_rays a)).comp (f:=fun s:E4 × E4=>s.2-s.1) (measurable_snd.sub measurable_fst)) measurable_const
lemma basePay : Integrable (outerBall.indicator (flow a)) := by
  apply IntegrableOn.integrable_indicator _ (isClosed_closedBall.measurableSet)
  convert! (flowLocal (0:E4) a).integrableOn_isCompact outerBallCompact using 2 <;> simp
lemma rockPay (w : E4) : Integrable fun x:E4=>rock a (x,w) := by
  change Integrable (stub.indicator (fun x:E4=>flow a (w-x))) volume
  apply IntegrableOn.integrable_indicator _ (isClosed_closedBall.measurableSet)
  -- actually flow argument x-w, use odd
  suffices h : IntegrableOn (fun x:E4=> -(flow a (x-w))) stub volume by
    convert! h using 2
    rename_i x; exact (congrArg _ (neg_sub x w)).symm.trans (flow_odd (x-w) a)
  exact (flowLocal w a |>.integrableOn_isCompact stubCompact).neg
lemma circleNonnegative (w : E4) : 0 ≤ circle a w := integral_nonneg (fun _=>norm_nonneg _)
lemma circleBdd : ∃ B ≥ 0, ∀ w ∈ closedBall (0:E4) 3, circle a w ≤ B := by
  let q v := ‖outerBall.indicator (flow a) v‖
  refine ⟨∫ v:E4,q v,integral_nonneg (fun _=>norm_nonneg _),?_⟩
  intro w hw
  rw [← MeasureTheory.integral_sub_left_eq_self q volume w, circle]
  refine integral_mono (rockPay _ _ |>.norm) ?_ ?_
  · simpa only [sub_eq_add_neg] using (((basePay a).norm.comp_add_left w).comp_neg)
  intro v
  change ‖ite _ _ _‖ ≤ _
  by_cases h : v∈stub
  · have he : w-v ∈ outerBall := by
       rw [stub,mem_closedBall_iff_norm,sub_zero] at h
       rw [mem_closedBall_iff_norm,sub_zero] at hw
       exact mem_closedBall_iff_norm.mpr (by rw [sub_zero]; exact (norm_sub_le ..).trans (by linarith))
    unfold q; rw [if_pos h]; exact le_of_eq (congrArg norm (indicator_of_mem he _).symm)
  rw [if_neg h,norm_zero]
  exact norm_nonneg _
lemma circleDecay : ∃ B ≥ 0, ∀ w : E4, 3 < ‖w‖ → circle a w ≤ B / (1+‖w‖)^3 := by
  obtain ⟨C,hC,he⟩ := price (flow_rays a)
  let V := volume.real stub
  refine ⟨V*(C*64), by dsimp only [V]; positivity,?_⟩
  intro w hw
  have h (x:E4) (hx:x∈stub): ‖rock a (x,w)‖ ≤ C*64 / (1+‖w‖)^3 := by
    rw [rock,if_pos hx]
    have := norm_sub_norm_le w x
    have hc := (mem_closedBall_iff_norm.mp hx)
    rw [sub_zero] at hc
    have hh : 0 < ‖w-x‖ := by linarith
    apply (he _ (norm_pos_iff.mp hh)).trans
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C*(1+‖w‖)^3 ≤ C*(4*‖w-x‖)^3 := by gcongr; linarith
         _ = C*64*‖w-x‖^3 := by ring
  let g := stub.indicator (fun _=> C*64 / (1+‖w‖)^3)
  have hg : Integrable g volume := (integrableOn_const stubCompact.measure_lt_top.ne).integrable_indicator stubCompact.measurableSet
  refine (integral_mono (rockPay _ _ |>.norm) hg (fun i=>?_)).trans (show (∫ i,g i) ≤ _ from le_of_eq ?_)
  · by_cases hi : i∈stub
    · exact (h i hi).trans_eq ((indicator_of_mem hi (fun _=> C*64 / (1+‖w‖)^3)).symm)
    exact le_of_eq (by rw [rock,if_neg hi,norm_zero]; exact (indicator_of_notMem hi _).symm)
  rw [integral_indicator stubCompact.measurableSet,setIntegral_const,smul_eq_mul]
  unfold V;ring
lemma circleAuto : AEStronglyMeasurable (circle a) volume :=
  (((rockMeasurable a).norm.comp measurable_swap).aestronglyMeasurable (μ:=volume.prod volume)).integral_prod_right'
lemma integralSquared : Integrable (fun w=> (circle a w)^2) := by
  obtain ⟨B,hB,he⟩ := circleBdd a
  obtain ⟨D,hD,hf⟩ := circleDecay a
  have hm := (circleAuto a).pow (2:ℕ)
  let A := closedBall (0:E4) 3
  have hA : MeasurableSet A := isClosed_closedBall.measurableSet
  refine integrableOn_univ.mp ?_
  rw [← union_compl_self A]
  refine IntegrableOn.union ?_ ?_
  · exact (show IntegrableOn (fun _=>B^2) A volume from integrableOn_const (isCompact_closedBall .. |>.measure_lt_top.ne)).mono' hm.restrict (ae_restrict_of_forall_mem hA (fun w hw=>by rw [Real.norm_of_nonneg (sq_nonneg _)]; gcongr <;> first | exact circleNonnegative _ _ | exact he w hw))
  refine (pay_outer (D^2)).integrableOn.mono' hm.restrict ?_
  apply ae_restrict_of_forall_mem hA.compl
  intro w hw
  have h := hf w (lt_of_not_ge (by simpa only [mem_compl_iff,A,mem_closedBall_iff_norm,sub_zero] using hw))
  rw [Real.norm_of_nonneg (sq_nonneg _),←sq_le_sq₀ (circleNonnegative a w) (by positivity)] at *
  rwa [div_pow,←pow_mul] at h
-- use explicitly product measures
def squaredIntegrand (s : (E4 × E4) × E4) := rock a (s.1.1,s.2) * rock a (s.1.2,s.2)
lemma innerSquare (w:E4) : ∫ s : E4 × E4, ‖squaredIntegrand a (s,w)‖ ∂volume.prod volume = (circle a w)^2 := by
  exact integral_congr_ae (ae_of_all _ (fun _=>norm_mul ..)) |>.trans ((integral_prod_mul (fun x=>‖rock a (x,w)‖) _).trans (sq (circle a w)).symm)
lemma outerSquare (w:E4) : ∫ s : E4 × E4, squaredIntegrand a (s,w) ∂volume.prod volume = (mean a w)^2 :=
  (integral_prod_mul (fun x=>rock a (x,w)) _).trans (sq (mean a w)).symm
lemma squarePay : Integrable (squaredIntegrand a) ((volume.prod volume).prod volume) := by
  have h : Measurable (squaredIntegrand a) := (show Measurable (fun s : (E4 × E4) × E4=>rock a (s.1.1,s.2)) from Measurable.comp (g:=rock a) (f:=fun s : (E4 × E4) × E4=>(s.1.1,s.2)) (rockMeasurable a) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul (Measurable.comp (g:=rock a) (f:=fun s : (E4 × E4) × E4=>(s.1.2,s.2)) (rockMeasurable a) ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  refine (integrable_prod_iff' (μ:=volume.prod volume) (ν:=volume) h.aestronglyMeasurable).mpr ⟨Eventually.of_forall (fun w=> (rockPay a w).mul_prod (rockPay a w)), (show Integrable (fun w:E4 => _) volume by simpa only [innerSquare] using integralSquared a)⟩
lemma orbitIntegral : (∫ xy : E4 × E4, (∫ w : E4, rock a (xy.1,w)*rock a (xy.2,w)) ∂(volume.prod volume)) = ∫ w,(mean a w)^2 := by
  have h := integral_integral_swap (f:=fun xy w=>squaredIntegrand a (xy,w)) (squarePay a)
  simp only [outerSquare] at h
  convert! h using 1
end YM.Pert.Triangle
