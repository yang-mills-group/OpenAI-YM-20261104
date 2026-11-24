import YM.SchemeRG11.Wisp.Away
import YM.Pert.Rig.Linked
/-! E4 step-cell integration. For regulating singular limits.
Differentiability of test not assumed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.World
open Function Filter Asymptotics Topology MeasureTheory Set Metric
open Extraction Flock Lattice Pert Align Full Maxwell Haze Pile Catch
open scoped Classical
variable {a:ℝ}{s:Finset Cover}{T:Align.Itinerary}
def stake (a:ℝ)(x:E4):Cover:=fun i=>⌈x i/a⌉
def land (a:ℝ)(p:Cover):Set E4:={x|stake a x=p}
lemma restrPath(ha:a>0)(p:Cover):land a p= WithLp.ofLp ⁻¹' Set.pi univ (fun i:Axis=> tile a (p i)):=by
 ext x; constructor
 · intro h i _; exact (tile_bounds ha _ _).mp (congrFun h i) 
 intro h; exact funext fun i=>(tile_bounds ha _ _).mpr (h i (Set.mem_univ _))
lemma measures (ha:a>0)(p:Cover): MeasurableSet (land a p):=by rw [restrPath ha]; exact (PiLp.volume_preserving_ofLp _).measurable (MeasurableSet.pi countable_univ fun i _=> measurableSet_Ioc)
lemma parcel (ha:a>0)(p:Cover): volume (land a p)= ENNReal.ofReal (a^4):=by
 rw [restrPath ha, (PiLp.volume_preserving_ofLp _).measure_preimage]
 · change Measure.pi (fun _:Axis=>volume) _=_; rw [Measure.pi_pi]; have he (i:Axis): volume (tile a (p i))=ENNReal.ofReal a:=by unfold tile; rw [Real.volume_Ioc]; congr 1; ring
   simp_rw [he]; rw [Finset.prod_const, ← ENNReal.ofReal_pow (by positivity)];rfl
 exact (MeasurableSet.pi countable_univ fun _ _=>measurableSet_Ioc).nullMeasurableSet
lemma gap_lo (ha:a>0)(x:E4):dist (incVec a (stake a x)) x ≤ 4*a :=by
 apply le_trans _ (approximate (n:=1) ha (points (fun (_:Fin 1)=>x)) |>.trans_eq (by push_cast; ring))
 let p:= points fun (_:Fin 1)=>x
 rw [dist_eq_norm,dist_eq_norm]
 exact PiLp.norm_apply_le (tag a (address a p)-p) 0

def Along (T:Align.Itinerary)(p:ℕ → Cover)(x:E4):Prop:=Tendsto (fun l=> incVec (T.gap l) (p l)) atTop (𝓝 x)
lemma follows(x:E4):Along T (fun i=>stake (T.gap i) x) x:=by
 unfold Along; rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero (fun _=>dist_nonneg) (fun i=>gap_lo (T.positive i) x) (by simpa using T.cutoff.const_mul 4)
lemma growing {w:ℕ → Cover}{x:E4}(hx:x≠0)(h:Along T w x): Tendsto (fun i=>(diam (w i):ℝ)) atTop atTop:=by
 rw [Filter.tendsto_atTop]; intro b; filter_upwards [T.cutoff.eventually (gt_mem_nhds (show 0< ‖x‖/(4*(1+|b|)) by have hh:=norm_pos_iff.mpr hx; positivity)),Tendsto.norm h|>.eventually (lt_mem_nhds (show ‖x‖/2 < ‖x‖ by have hh:=norm_pos_iff.mpr hx; linarith))] with i hi hh
 have ha:=T.positive i
 rw [norm_span _ ha] at hh
 rw [lt_div_iff₀ (by positivity)] at hi
 apply le_of_mul_le_mul_left (a:=T.gap i*2) _ (by positivity)
 calc _ ≤ T.gap i *2*|b| :=by gcongr; exact le_abs_self _
      _ ≤ T.gap i*‖incVec 1 _‖ := by linarith only [hh,ha,hi]
      _ ≤ _ := by rw [mul_assoc (T.gap _ ) 2]; apply mul_le_mul_of_nonneg_left (chart_le _) ha.le
lemma roof (ha:a>0)(z:Cover): ‖incVec a z‖ ≤ 2*a*(diam z:ℝ):=by rw [norm_span _ ha]; exact (mul_le_mul_of_nonneg_left (chart_le _) ha.le).trans_eq (by ring)
lemma rock (ha:a>0)(x:E4): ‖x‖ ≤ 4*a*(diam (stake a x)+1:ℝ):=by
 let z:= stake a x; have hp:= norm_sub_norm_le x (incVec a z); have hb:= gap_lo ha x
 rw [dist_comm,dist_eq_norm] at hb
 linarith [roof ha z, mul_nonneg ha.le (show 0 ≤ (diam z:ℝ) by positivity)]

variable (a)
def pot(g:Cover→ℝ) := g ∘ stake a
def plot1(g:Cover→ℝ)(p:Cover):= (World.land a p).indicator (fun _:E4=>g p)
variable {a}
lemma budget1 (ha:a>0)(g:Cover→ℝ)(p:Cover): Integrable (plot1 a g p) volume ∧ (∫x:E4, plot1 a g p x)= a^4*g p:=by
 have ht:= parcel ha p; unfold plot1
 refine ⟨(integrable_indicator_iff (measures ha _)).mpr (integrableOn_const (ht ▸ ENNReal.ofReal_ne_top)),?_⟩;rw [integral_indicator (measures ha _),setIntegral_const,Measure.real,ht, ENNReal.toReal_ofReal (by positivity)];rfl
lemma gridP {s:Finset Cover} (ha:a>0)(g:Cover→ℝ)(hs:∀p∉s,g p=0): Integrable (pot a g) volume ∧ ∫ x, pot a g x = a^4 * ∑i∈s,g i:=by
 have he: pot a g=∑ p∈s,plot1 a g p:=by
   funext x; rw [Finset.sum_apply]; unfold pot plot1 comp; by_cases h:stake a x∈s
   · rw [Finset.sum_eq_single_of_mem _ h]; exact (indicator_of_mem (show x∈World.land a (stake a x) from rfl) (fun _:E4=>g (stake a x))).symm
     intro i _ e; exact indicator_of_notMem (fun (w:x∈World.land a i)=> e (by unfold World.land at w; exact Eq.symm w)) _
   rw [hs _ h]; apply Eq.symm; apply Finset.sum_eq_zero; intro p hp; exact indicator_of_notMem (fun (w:x∈World.land a p)=> h ((show stake a x=p from w) ▸ hp)) _
 rw [he]; constructor
 · exact integrable_finsetSum' _ fun p _=> (budget1 ha g p).1 -- check
 simp_rw [Finset.sum_apply]; rw [integral_finsetSum _ fun p _=> (budget1 ha g p).1]; simp_rw [(budget1 ha g _).2,Finset.mul_sum]
lemma inv_cube (R C:ℝ): Integrable ( (closedBall (0:E4) R).indicator (fun x:E4=> C / ‖x‖^3)) volume:=by
 apply (integrable_indicator_iff measurableSet_closedBall).mpr
 let f:E4→ℝ:=fun x=> C/‖x‖^3; have hx (v:E4)(hv:v≠0): ‖f v‖≤|C| *‖v‖^(-(3:ℕ):ℝ):=by
   unfold f; rw [Triangle.inv_power] -- check namespace
   simp [div_eq_mul_inv,Real.norm_eq_abs]
 exact (locallyIntegrable_of_norm_le_rpow (α:=(3:ℕ)) (μ:=volume) (f:=f) (C:=|C|) (by rw [Triangle.four_rank];decide) (by rw [Triangle.four_rank];norm_num) ((volume.ae_ne 0).mono hx) ((by unfold f; fun_prop):Measurable f).aestronglyMeasurable).integrableOn_isCompact (isCompact_closedBall ..)
end YM.SchemeRG11.World
