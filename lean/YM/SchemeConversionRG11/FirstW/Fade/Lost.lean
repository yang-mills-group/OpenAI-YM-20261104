import YM.SchemeConversionRG11.FirstW.Fade.Last
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell Next.Rank.Radian
open scoped BigOperators Classical
variable {T:Itinerary} {c:ℕ→Side} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f:Hall T E} {F:E4→E} {C:ℝ}
lemma outlast (hp: ∀ᶠ i in atTop,∀ x:Site (T.period i), HeadR T i x ^6*‖f i x‖ ≤ C)(h: ∀ᵐ v∂volume, ∀ p:StepPath T,sails T p v → Tendsto (fun i=>f i (p i)) atTop (𝓝 (F v)))(he:0≤C)(hc:MarkGrid T c) : Integrable F ∧ Tendsto (fun i=> (T.gap i)^4 • ∑ x,f i x) atTop (𝓝 (∫ x,F x)):= by
 let K(i:ℕ):= chunk (c i) (f i); let g(v:E4):= (6^6*C)/(1+‖v‖)^6
 have hm i: Integrable (K i):= chunk_birth ..
 have hv:= h.mono fun v hz=> chunk_land (F:=f) hc hz
 have hx:∀ᶠ i in atTop,∀ᵐ v∂volume,‖K i v‖≤g v := hp.mono fun i hi=> Eventually.of_forall fun v=> by
   dsimp only [K]; rw [chunk_coord]; split
   next he' =>
     let x:=wrap (T.period i) (mark (c i) v); have hl:=chunk_side (c i) v x rfl he'; change ‖f i x‖ ≤ g v
     have hh: 1+‖v‖≤6 * HeadR T i x:= by rw [← hc i] at hl; unfold HeadR Gulf; linarith
     unfold g; rw [le_div_iff₀ (by positivity)]; refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 6) (norm_nonneg _)) ?_; rw [mul_pow, mul_comm, mul_assoc]; gcongr; exact hi x
   next => rw [norm_zero]; unfold g; positivity
 have hg : Integrable g:= Pert.Triangle.pay_outer (6^6*C)
 have hh:= tendsto_integral_filter_of_dominated_convergence (F:=K) g (Eventually.of_forall fun i=>(hm i).aestronglyMeasurable) hx hg hv
 exact ⟨freeborn K hg (fun i=>(hm i).aestronglyMeasurable) hx hv,hh.congr (fun i=>by unfold K; rw [chunk_value,hc i])⟩
-- assembly independent sea ext direct only
variable {G:Gauge}{Q:Wash} {o p r:StepPath T}{A B C:Sight T G}{S:Set E4}{P:Hall T ℝ}{y x z:E4}{a b c':ℕ}
lemma priceP (h:HatP T S A)(e:HatP T S B)(p: HatP T S C)(i j:Step): Pleased T S (SeatD T A B C i j) := by
 rw [rateD]; have h1 : Pleased T S (Dra T A B C i j):= (seesP h i j).map₂ (spireP e p _) (innerSL ℝ)
 have h2 : Pleased T S (Dra T B C A i j):= (seesP e i j).map₂ (spireP p h _) (innerSL ℝ)
 have h3 : Pleased T S (Dra T C A B i j):= (seesP p i j).map₂ (spireP h e _) (innerSL ℝ)
 exact ((h1.enclose h2).enclose h3).scale _
lemma outmask (fu:Pleased T S P)(u:S∈ae (volume:Measure E4))(H:Gloam T P 0 P)(hc:MarkGrid T c)
   (h1:HatP T S A)(h2:HatP T S B)(h3:HatP T S C)(f1:sails T o x)(f2:sails T p y)(f3:sails T r z)(l1:Leeway T o P)(l2:Leeway T p P)(l3:Leeway T r P)(s1:Shore T o a A)(s2:Shore T p b B)(s3:Shore T r c' C)(ha:2≤a)(hb:2≤b)(he:2≤c')(i j:Step) : Helen (fun k=> T.gap k ^ 4 * ∑ v:Site (T.period k), P k v * SeatD T A B C i j k v) := by
 let f(k:ℕ)(v:Site (T.period k)):= P k v*SeatD T A B C i j k v
 obtain ⟨Z,hZ⟩:= (show Pleased T S f from fu.map₂ (priceP h1 h2 h3 i j) (ContinuousLinearMap.mul ℝ ℝ)); obtain ⟨D,hD,B⟩:= (show Gloam T P 6 f from H.map₂ (seat_high f1 f2 f3 l1 l2 l3 s1 s2 s3 ha hb he i j) (ContinuousLinearMap.mul ℝ ℝ))
 have hm: ∀ᵐ x∂volume,x∈S:=u
 have he : ∀ᶠ i in atTop,∀ x, HeadR T i x ^6*‖f i x‖ ≤ D:= B.mono fun i hi x=>by
   by_cases h:P i x=0; · simp [f,h,hD.le]
   exact hi x h
 exact ⟨_,(outlast (f:=f) he (hm.mono fun v hv p h=> hZ.identity id tendsto_id v hv _ h) hD.le hc).2⟩
end YM.RG11.FirstW
