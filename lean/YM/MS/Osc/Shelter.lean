import YM.MS.Osc.Snap
/-!
# Averaged quadrature in weighted norms. Point step Δ kills smooth periodic rate function to all orders. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Osc.Snap
open Set Filter Function Finset Metric MeasureTheory Real ENNReal Plane
open Momentum Tone Landau Native
open scoped Topology ContDiff NNReal
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
  {p:Scale I}{h:I→ℝ}{K T:ℝ}{b x:I→ℝ}{j:ℕ}{i:I}
local notation "B"=>Metric.closedBall
lemma stud (p:Scale I){E:Type}[NormedAddCommGroup E](i:I)(j:ℕ) : Continuous ( fun u:E=> p.dust j i u ):= by unfold Scale.dust; exact Continuous.inv₀ (show Continuous (fun u:E=> p.weight i u ^ j) by unfold Scale.weight; fun_prop) (fun i=> (pow_ne_zero j (p.weight_pos _ _).ne'))
section
variable (hp:∀ i,0<b i) (hc:0≤K)(hK:∀ i,p.length i*b i≤ K)
include hp hc hK
lemma budget (q:QP) (j i): p.dust j i (Tick (b i) q) ≤ (1+K)^j*p.dust j i q := by
    have he:Captain p K q (Tick (b i) q) i := by unfold Captain; rw [norm_sub_rev]; exact (mul_le_mul_of_nonneg_left (maxS (hp i) _) (p.pos i).le).trans (hK i)
    simpa only [Scale.dust,mul_one,one_div] using windy_pay he hc j zero_le_one zero_le_one
omit hp hc hK in
lemma world (p:Scale I)(j:ℕ)(i:I){b:ℝ}: (∫ q,p.dust j i q ∂rail b)=∫ q,p.dust j i (Tick b q)∂planeF:= integral_map tick_m.aemeasurable (stud p i j|>.aestronglyMeasurable)
omit hp hc hK in
lemma Tall (p:Scale I)(j:ℕ)(H:j>4): glob p (fun _=>planeF) j := Reserve.cover j (by simpa [QP,Momentum,Axis])
lemma local_p (H:j>4) : glob p (fun i=>rail (b i)) j:= by
    refine ⟨fun _=> Filter.Eventually.of_forall fun _=> trivial,fun i=>?_⟩; apply ( integrable_map_measure ((stud p i j).aestronglyMeasurable (μ:=rail (b i))) tick_m.aemeasurable ).mpr; refine ((Tall p j H).integrable i|>.const_mul ( (1+K)^j :ℝ)).mono' (((stud p i j).measurable.comp tick_m).aestronglyMeasurable) ?_ -- replace
    exact Filter.Eventually.of_forall fun x=> (by rw [comp_apply,norm_of_nonneg]; exact budget hp hc hK x j i; exact (p.dust_pos ..).le )
omit [NormedSpace ℝ E] in
lemma spending (H:j>4): p.full.Le (fun i (_:E)=>∫ q,p.dust j i q ∂rail (b i)) (fun i _=>(p.length i ^ 4)⁻¹):= by
    have he : p.full.Le (fun i (_:E)=>∫ q,p.dust j i q ∂planeF) (fun i _=> (p.length i^4)⁻¹):= by convert Reserve.cutoff_mass (S:=p) (μ:=planeF) (F:=E) (D:=fun _=> Set.univ) j (by simpa [QP,Momentum,Axis]) using 1; ext; simp; ext; simp [QP,Momentum,Axis] -- syntax indentation issues
    have h':= Cost.Le.const_mul he ( (1+K)^j :ℝ ) (by positivity) (by intro i _ _; change 0 ≤ (p.length i ^ 4 )⁻¹; exact inv_nonneg.mpr (pow_nonneg (p.pos i).le _))
    refine Cost.Le.left h' (fun i x _=>?_ ); rw [world,← integral_const_mul]; refine integral_mono ?_ ((Tall p j H|>.integrable i).const_mul _ ) (fun q=> budget hp hc hK q j i); exact ( show MeasurePreserving (Tick (b i)) planeF (rail (b i)) from ⟨tick_m,rfl⟩ ).integrable_comp_of_integrable ( (local_p (p:=p) hp hc hK H).integrable i )
end
-- generic avg algebra.F.Field valued.C.G. Universe E complete
variable [CompleteSpace E] {F:QP→E}
abbrev TreeSum (F:QP→E)(b:ℝ) := (∫ i,F i ∂rail b) - ∫ i,F i ∂planeF
lemma rounding (h:0<T) : ∀ᵐ p ∂region T, ‖p‖ ≤ T:= Eventually.filter_mono ( Measure.ae_mono' (Measure.smul_absolutelyContinuous ..) ) ( ( ae_restrict_mem ( box_m (b:=T) 0)).mono fun x H=> by have hz:= maxS h x; rw [Tick, Function.comp_apply,show back T x=0 from H,map_zero,zero_sub,norm_neg] at hz; exact hz ) -- e∈∀π
omit [CompleteSpace E] in
lemma tick_avg (h:0<T)(hf: Integrable F planeF) : Integrable (fun z=>∫ q,F (q+ z) ∂rail T) (region T) ∧ ∫ z,(∫ q,F (q+z)∂rail T) ∂region T=∫ i,F i ∂ planeF:= by
    haveI: IsProbabilityMeasure (region T):= μprob h; have hu := (average_b h).integrable_comp_of_integrable hf; exact ⟨ hu.integral_prod_right, ( integral_prod_symm _ hu ).symm.trans (show _ from (by rw [← (average_b h).map_eq, integral_map (average_b h).measurable.aemeasurable ((average_b h).map_eq.symm ▸ hf.1) ]; rfl)) ⟩ -- names. integral_comp' requires equiv
lemma tree_avg (h:0<T)(hF: Integrable F planeF)(H:Integrable F (rail T)) : TreeSum (F:=F) T= ∫ z,TreeSum (fun i=> F i-F (i+z)) T ∂region T:= by
    haveI: IsProbabilityMeasure (region T):= μprob h; let G z:=∫ q,F (q+z) ∂rail T; obtain ⟨hg,hG⟩:= tick_avg h hF; have ht: ∀ᵐ z ∂region T, TreeSum (fun i=> F i-F (i+z)) T=( ∫ i,F i ∂rail T)-G z:= by
       filter_upwards [( (average_b h).integrable_comp_of_integrable hF ).prod_left_ae ] with z hz; rw [TreeSum,integral_sub H (show Integrable (fun i=> F (i+z)) (rail T) from hz), integral_sub hF _ , integral_add_right_eq_self (μ:=planeF)]; simp [G]; exact (measurePreserving_add_right planeF z).integrable_comp_of_integrable hF -- bad sub self
    unfold TreeSum at *; rw [integral_congr_ae ht,integral_sub (integrable_const ..) hg,hG, integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul ]
end YM.MS.Osc.Snap
