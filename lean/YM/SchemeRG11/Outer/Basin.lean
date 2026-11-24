import YM.SchemeRG11.Sew.Ding
import YM.Contact.TailScale
import YM.SchemeRG11.Wilson.Patch
/-! Infinite tile cost to ℝ-grid limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew
open scoped Classical Pointwise
variable {G:Gauge} {T:Align.Itinerary}
lemma floorSum {f:Cover→ℝ}(h:Summable f){p:ℝ}(hp:0<p):
 ∫ x:E4,pot p f x=p^4* ∑' i:Cover,f i:=by
 have he(x:E4): pot p f x= ∑' i,plot1 p f i x:=by
    rw [tsum_eq_single (stake p x)]; exact (Set.indicator_of_mem (show x∈World.land p (stake p x) from rfl) _).symm
    exact fun i hi=> Set.indicator_of_notMem (fun (w:x∈World.land p i)=>hi (Eq.symm w)) _
 simp_rw [he]; rw [← integral_tsum_of_summable_integral_norm (fun i=> (budget1 hp f i).1)]
 · simp_rw [(budget1 hp f _).2,tsum_mul_left]
 have H(i:Cover): (∫ (x:E4), ‖plot1 p f i x‖) = p^4* ‖f i‖:=by rw [←(budget1 hp (fun z=> ‖f z‖) i).2]; simp only [plot1]; apply integral_congr_ae; filter_upwards with x; by_cases h:x∈World.land p i<;> simp [*,Set.indicator]
 simp_rw [H]; exact Summable.mul_left _ h.norm
lemma floorLab{f:Cover→ℝ}{p:ℝ}(_hp:0<p): AEStronglyMeasurable (pot p f) volume:=by
 have h(i:Axis):Measurable (fun x:E4=>stake p x i):= Measurable.ceil ((EuclideanSpace.proj i).continuous.measurable.div_const p)
 apply Measurable.aestronglyMeasurable; exact (measurable_of_countable f).comp (measurable_pi_lambda _ h)
lemma tail (C:ℝ): Integrable (fun x:E4=> C*((‖x‖+1)^6)⁻¹) volume:=by
 apply Integrable.const_mul (f:=fun x:E4=> ((‖x‖+1)^6)⁻¹)
 let K:=closedBall (0:E4) 1; let u:E4→ℝ:=fun x=> ((‖x‖+1)^6)⁻¹
 have hc:Continuous u:= Continuous.inv₀ ((continuous_norm.add_const _).pow _) (fun x=>by positivity)
 let w:=fun x:E4=> (Set.Ioi (1:ℝ)).indicator (fun r=>r^(-(6:ℕ):ℝ)) ‖x‖
 have he:Integrable w volume:=Contacts.Patch.exterior_power zero_lt_one (by norm_num [Contacts.normal,E4,Axis]) (by norm_num [Contacts.normal,E4,Axis])
 change Integrable u
 have hk:MeasurableSet K:=measurableSet_closedBall
 have hh:Integrable (Kᶜ.indicator u):=(Integrable.mono' he (Measurable.aestronglyMeasurable (Measurable.indicator hc.measurable hk.compl)) (Eventually.of_forall (fun x=>by
     by_cases hx:x∈K
     · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx),norm_zero]; rw [show w x=0 from Set.indicator_of_notMem (show ‖x‖∉Set.Ioi 1 from not_lt.mpr (mem_closedBall_zero_iff.mp hx)) _]
     rw [Set.indicator_of_mem (show x∈Kᶜ from hx)]; have hf : ‖x‖ > 1:= not_le.mp (fun q=>hx (mem_closedBall_zero_iff.mpr q)); unfold w; rw [Set.indicator_of_mem (show ‖x‖∈Set.Ioi _ from hf), Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]; unfold u; rw [Real.norm_of_nonneg (by positivity)]; gcongr; linarith)))
 exact integrableOn_univ.mp (by simpa using (hc.continuousOn.integrableOn_compact (K:=K) (isCompact_closedBall ..)).union ((integrable_indicator_iff hk.compl).mp hh))
lemma seaCost {f:Slate}(hp:∀ i,Summable (f i))(h:∃ C>0,∀ᶠ i in atTop,∀ p:Cover, |f i p| * (baseU T i p+1)^6≤C)(hx:∀ x:E4,Finishes (fun i=>f i (stake (T.gap i) x))): Finishes (fun i=>T.gap i^4* ∑' p:Cover,f i p):=by
 obtain ⟨C,hC,H⟩:=h
 let u(y:E4):= C*4^6*((‖y‖+1)^6)⁻¹
 let f' (i:ℕ)(y:E4):= pot (T.gap i) (f i) y
 have hf:∀ᶠ i in atTop,∀ᵐ x:E4, ‖f' i x‖ ≤ u x:=H.mono (fun i hi=>Eventually.of_forall (fun x=>by
   let p:=stake (T.gap i) x
   have h: ‖x‖+1≤4*(baseU T i p+1):=by unfold baseU; rw [mul_add,←mul_assoc]; have hv:=rock (T.positive i) x; unfold p World.d; linarith
   change ‖f i p‖ ≤ _; apply (le_div_iff₀ (by positivity)).mpr -- need unfold u
   change |f i p| * (‖x‖+1)^6≤ C*4^6; calc _≤|f i p| * (4*(baseU T i p+1))^6 := by gcongr
                                              _ ≤ _:=by rw [mul_pow,mul_comm (4^6:ℝ),←mul_assoc]; gcongr; exact hi _))
 choose g h using hx
 have hv:= tendsto_integral_filter_of_dominated_convergence u (Eventually.of_forall fun i=>floorLab (f:=f i) (T.positive _)) hf (tail (C*4^6)) (Eventually.of_forall h) -- h applied?
 refine ⟨_,hv.congr (fun i=>floorSum (hp i) (T.positive _))⟩
end YM.SchemeRG11.Dock
