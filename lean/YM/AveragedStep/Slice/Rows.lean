import YM.AveragedStep.Slice.Twist
/-! Sliced paired expectation in the actual vacuum law, holding V.
The fully normalized S.density β does not divide out any source's stencil.
This uses ordinary tree recoil then V's lift at the roots, with the braces
and chamber bodies exactly above. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG Loops Tree MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ENNReal
lemma env_marginal {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y](m:Measure X) [IsProbabilityMeasure m]
    {F:X × Y→ℝ}(h:Envelope F): Envelope (fun y:Y=>∫ x,F (x,y)∂m):=by
 obtain ⟨C,H⟩:=h.cost
 refine ⟨h.meas.stronglyMeasurable.integral_prod_left'.measurable, C, fun y=>?_⟩
 exact (norm_integral_le_of_norm_le (μ:=m) (f:=fun x=>F (x,y)) (g:=fun _=>C) (integrable_const _)
    (Eventually.of_forall fun x=>H (x,y))).trans_eq (by simp)
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio) {β:ℝ}
def dr(D:TopologyQ F G):Config G f:=F.drape D.1
-- price reader on chart. unnormalized in V (normalized by physical partition).
def assay (β:ℝ)(b:Site c)(z:TopologyQ F G):ℝ:=
   S.density β (dr F z) (Loops.setGauge b z.2) * bare β (dr F z)
def report (β:ℝ)(b:Site c)(q:TopologyQ F G→ℝ):ℝ:= (partition G f β)⁻¹*(∫ z,assay F β b z*q z ∂(F.order G).prod (prior G c))
variable (b:Site c)
private lemma law_back (H:Config G f → ℝ): (∫ U,H U ∂law G f β)= (partition G f β)⁻¹*∫ U,bare β U*H U ∂prior G f:=by
 rw [law,integral_withDensity_eq_integral_toReal_smul (weight_meas _)]
 · rw [← integral_const_mul]
   apply integral_congr_ae; filter_upwards with U
   rw [Wilson.weight,ENNReal.toReal_ofReal (div_pos (bare_pos _ _) (partition_pos _)).le, smul_eq_mul]; ring
 exact Eventually.of_forall fun _=> ENNReal.ofReal_lt_top
lemma reverse_read (q: Query S G)(hS:S.patch.Branches S.kernel G)(h:Admits q) :
    readQ S β q= (partition G f β)⁻¹*∫ V, ∫ U,∑ k, weightQ S β k (U,V)*bare β U*q k (U,V) ∂prior G f ∂prior G c:=by
  let X(k:S.Choices)(u:Board G c f):=weightQ S β k u*q k u
  have he(k): Envelope (X k):=(weight_env S β hS k).mul (h k)
  have hb: Envelope fun z: Board G c f=> bare β z.1:= env_continuous ((bare_cont β).comp continuous_fst)
  let Y(k:S.Choices)(u:Board G c f):=weightQ S β k u*bare β u.1*q k u
  have hy(k):Envelope (Y k):=((weight_env S β hS k).mul hb).mul (h k)
  set I:=fun U:Config G f=> bare β U
  set m:=law G f β
  have hm k : Integrable (X k) (m.prod (prior G c)):=read_safe S _ hS h k
  let t:= (partition G f β)⁻¹
  change (∑ k,∫ x,X k x∂ (m.prod (prior G c)))=t*∫ V,∫ U,∑ k,Y k (U,V) ∂prior G f ∂prior G c
  -- reverse to *V outer*. prefer integral_prod_symm
  have ht k: (∫ x, X k x∂m.prod (prior G c))= t*∫ V,∫ U,Y k (U,V)∂prior G f ∂prior G c:=by
    rw [integral_prod_symm _ (hm k),←integral_const_mul]
    apply integral_congr_ae; filter_upwards with V
    unfold m; rw [law_back]; congr 1
    apply integral_congr_ae; filter_upwards with U; unfold X Y; ring
  simp_rw [ht,← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun i _=>(env_marginal (prior G f) (hy i)).integrable (prior G c))]
  apply congr_arg (t*·); apply integral_congr_ae; filter_upwards with V
  exact (integral_finsetSum (μ:=prior G f) _ fun k _=>
    (env_comp (hy k) (g:=fun x:Config G f => (x,V)) (measurable_id.prodMk measurable_const)).integrable _).symm

variable (hS:S.patch.Branches S.kernel G)
include hS
lemma joint_env (β:ℝ): Envelope fun z:Board G c f=> S.density β z.1 z.2:= Envelope.sum _ _ (weight_env S β hS)
lemma assay_env (β:ℝ) : Envelope (assay F (G:=G) β b):=(env_comp (joint_env hS β)
    (g:=fun z:TopologyQ F G=> (dr F z,Loops.setGauge b z.2))
    (show Measurable _ from by
      have hh: Measurable fun z:TopologyQ F G=>dr F z:= (F.continuous_drape.measurable.comp measurable_fst)
      exact hh.prodMk ((Loops.gauge_cont b).measurable.comp measurable_snd))).mul
        (env_continuous ((bare_cont _).comp (F.continuous_drape.comp continuous_fst)))
lemma report_as (β:ℝ){q:TopologyQ F G→ℝ}(h:Envelope q):report F β b q=
    (partition G f β)⁻¹ * ∫ V,∫ U,assay F β b (U,V)*q (U,V)∂F.order G∂prior G c:= by
 rw [report, integral_prod_symm _ (((assay_env F b hS β).mul h).integrable _)]
lemma twist_order (q:TopologyQ F G→ℝ)(h:Envelope q):
    readQ S β (fun _ x=> q (chamber F b x)) = report F β b q:=by
  rw [report_as F b hS β h, reverse_read (hS:=hS)]
  · congr 1; apply integral_congr_ae; filter_upwards with V
    simp_rw [← Finset.sum_mul]
    let Y(U:Config G f):=S.density β U V * bare β U*q (chamber F b (U,V))
    let k:=strung b V
    let κ:=sweep F k
    change (∫ U,Y U∂prior G f)=_
    rw [(packed F b V q h hS).2]
    let f0(u:F.Slice G):=assay F β b (u,V)*q (u,V)
    have hp(w:F.Slice G):Y (F.drape w)= f0 (κ w):=by
      unfold Y f0 assay dr
      rw [chamber_drape]; dsimp only
      have e: (k ∘ S.ratio.parent) ∘ S.ratio.embed = k:=funext fun i=>by simp [S.ratio.embed_parent]
      change S.density _ _ _*_*q (κ w,V)=S.density β (F.drape (sweep F k w)) (Lattice.gauge k V)*bare β _*q (κ w,V)
      rw [← drape_sweep, bare_gauge]
      have ht := S.covary hS (k ∘ S.ratio.parent) β (F.drape w) V
      rw [e] at ht; rw [ht]
    change (∫ w,Y (F.drape w)∂F.order G)=∫ w,f0 w∂F.order G
    simp_rw [hp]; exact (sweep_measure F k).integral_comp' _
  exact fun _=> env_comp h (chamber_meas F b)

def aboard (p:TopologyQ F G): Rim c f→G.El:=Sum.elim (dr F p) (Loops.setGauge b p.2)
omit hS in
@[fun_prop] lemma aboard_cont : Continuous (aboard (G:=G) F b):=by
  apply continuous_pi; rintro (e|e)
  · exact (continuous_apply e).comp (F.continuous_drape.comp continuous_fst)
  exact (continuous_apply e).comp ((gauge_cont b).comp continuous_snd)
omit hS in
lemma ride (z:Board G c f):aboard F b (chamber F b z)=roll F b z:=by
  unfold aboard dr roll; rw [drape_chamber]; rfl
end YM.AveragedStep
