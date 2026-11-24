import YM.OPE.Compatible.Arch.Acre
/-!
# One integration using arbitrary measurable collar inside footprint. No equal Euclidean balls assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "Lf" => Tested.germ
open Zone Radial ScriptJ Metric
local notation "R" => Radial.zone (E:=E)
abbrev KernFit (k:E→ℝ)(c:ℝ) := ∀ x:E, 0 ≤ k x ∧ k x≤ Real.exp (-c*‖x‖^2)
def Suber (s:Set E)(t:ℝ): Set E:= (fun x:E=>t • x) ⁻¹' s
def gemLift (μ:Measure E)(k:E→ℝ)(p: ScriptJ E): JetS ℝ:=⟨∫ x,(p x).s*k x ∂μ,∫ x,(p x).l*k x ∂μ,∫ x,(p x).h*k x ∂μ⟩
variable (μ:Measure E)[μ.HasTemperateGrowth] {c:ℝ}{A:ℝ→E→ℝ}{p:ScriptJ E}{k:E→ℝ}
lemma integ (hr:KernFit k c)(h:Measurable k)(he:0<c){u:E→ℝ}(hb:Bond u): Integrable (u*k) μ:=by
      obtain ⟨C,d,hC,hp⟩:= hb.cost; apply ((bill_integrable μ _ he).const_mul C).mono' (hb.smooth.continuous.measurable.mul h|>.aestronglyMeasurable)
      refine Eventually.of_forall fun x=>?_
      rw [Pi.mul_apply,norm_mul,Real.norm_eq_abs (k x),abs_of_nonneg (hr x).1]; apply le_trans (mul_le_mul (hp x) (hr x).2 (hr x).1 ((norm_nonneg _).trans (hp x))); unfold bill; rw [mul_assoc]
lemma paying (hr:KernFit k c)(h:Measurable k)(he:0<c)(hb:p.B)(t:ℝ): Integrable (quitt p t*k) μ :=
      integ μ hr h he (by obtain ⟨a,b,d⟩:= bondX hb; exact (a.add ((Bond.keep t).mul b)).add ((Bond.keep (t^2)).mul d))
lemma costing (hr:KernFit k c)(h:Measurable k)(he:0<c)(hb:p.B)(t:ℝ): ∫ x,quitt p t x*k x ∂μ=(gemLift μ k p).atK t:=by
      obtain ⟨a,b,d⟩:= bondX hb; unfold quitt JetS.atK gemLift; simp only [smul_eq_mul]; simp_rw [add_mul]; simp_rw [mul_assoc]
      rw [integral_add _ ((show Integrable (fun x=>(p x).h*k x) _ from integ μ hr h he d).const_mul _), integral_add (show Integrable (fun x=>(p x).s*k x) _ from integ μ hr h he a) ((show Integrable (fun x=>(p x).l*k x) _ from integ μ hr h he b).const_mul _), integral_const_mul,integral_const_mul]; exact (integ μ hr h he a).add ((integ μ hr h he b).const_mul _)
-- proof geometric estimates
lemma billCap {u:E→ℝ}{d:ℕ}{r:ℝ}{s:Set E}(hr:0 ≤ r)(hc:0<c)(h:∀ᵐ x ∂μ.restrict s,‖u x‖ ≤ r*bill d c x): ‖∫ x in s,u x ∂μ‖ ≤ r*∫ x:E,bill d c x ∂μ:=by
     have hi:=(bill_integrable μ d hc).const_mul r; exact (norm_integral_le_of_norm_le hi.integrableOn h).trans ((setIntegral_le_integral hi (Eventually.of_forall fun x=>mul_nonneg hr (bill_nonneg ..))).trans_eq (integral_const_mul ..))
omit [MeasurableSpace E] [BorelSpace E] in lemma quitPay {r: ScriptJ E}(hb:r.B) : ∃ d C,0≤C∧∀ t∈Icc (0:ℝ) 1,∀ x, |quitt r t x| ≤ C*((R).w x)^d:=by
     obtain ⟨h1,h2,h3⟩:= bondX hb; obtain ⟨C,d,hC,H⟩:= h1.cost.norm.add (h2.cost.norm)|>.add h3.cost.norm
     refine ⟨d,C,hC,fun t ht x=>?_⟩; obtain ⟨ha,he⟩:= ht; have hx : |quitt r t x| ≤ ‖(r x).s‖+ ‖(r x).l‖+ ‖(r x).h‖:=by
          rw [← Real.norm_eq_abs]; unfold quitt JetS.atK; apply le_trans (norm_add_le ..); refine add_le_add (le_trans (norm_add_le ..) (add_le_add_right ?_ _)) ?_
          · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]; exact mul_le_of_le_one_left (norm_nonneg _) he
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ha _)]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ha he)
     apply hx.trans; specialize H x; simp only [Pi.add_apply,Real.norm_eq_abs] at *; rwa [abs_of_nonneg (by positivity)] at H
lemma quit_collapsed (hr:KernFit k c)(he:0<c){s:Set E}(hb:p.B)(hc:s∈𝓝 0)(hs:MeasurableSet s): ((fun t=>∫ x in (Suber s t)ᶜ,quitt p t x*k x ∂μ):ℝ→ℝ)=O[Lf](gradeP 3) :=by
     obtain ⟨δ,hδ,hq⟩:= Metric.mem_nhds_iff.mp hc
     obtain ⟨d,C,hC,hx⟩:= quitPay hb; let D:=C*(δ⁻¹)^3; have hd:0≤D:=by unfold D; positivity
     rw [Reads.isTariff]; refine ⟨D*∫ x:E,bill (d+3) c x ∂μ, mul_nonneg hd (integral_nonneg fun x=>bill_nonneg ..),?_⟩; filter_upwards [Tested.eventually_small one_pos] with t (hv:0<t ∧ t<1)
     obtain ⟨hk,hk'⟩:=hv; apply le_trans (b:=D*t^3*∫ x:E,bill (d+3) c x ∂μ) _ (le_of_eq (by ring)); apply billCap μ (by positivity) he
     filter_upwards [ae_restrict_mem (μ:=μ) ((hs.preimage (show Measurable (fun x:E=>t • x) by fun_prop)).compl)] with x (ha:x∈(Suber s t)ᶜ)
     let w:= (R).w x; have hw:0<w:=lt_of_lt_of_le zero_lt_one ((R).high _); have hp: δ ≤ t*w:=by
         have hj:t•x ∉ ball 0 δ := fun hx=> ha (hq hx); rw [mem_ball_zero_iff,norm_smul] at hj -- fix syntax
         have h:‖x‖ ≤ w:=by simp [w,Radial.zone]
         exact (le_of_not_gt (by simpa [abs_of_pos hk] using hj)).trans (mul_le_mul_of_nonneg_left h hk.le)
     rw [norm_mul,Real.norm_eq_abs _, Real.norm_eq_abs _,abs_of_nonneg (hr x).1]
     calc
         _ ≤ C*w^d*Real.exp (-c*‖x‖^2):=mul_le_mul (hx t ⟨hk.le,hk'.le⟩ x) (hr x).2 (hr x).1 (by positivity)
         _ ≤ _ * (t*w*δ⁻¹)^3:=le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by rw [←div_eq_mul_inv]; exact (one_le_div hδ).mpr hp))
         _ = _:=by unfold bill D w; rw [pow_add];ring
end YM.OPE.Libra
