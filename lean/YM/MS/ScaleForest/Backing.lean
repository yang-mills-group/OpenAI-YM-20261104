import YM.MS.ScaleForest.Coast
/-!
# Vertical integration is past integration under the common analytic prescription

Keep log time s an honest finite IR scale. For pins gluing, this past integral
needs *no local ambiguity* (limit we prove); take it in the dimensional
integral before physical specialization. This includes momentum contraction
with evanescent terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {F:Curtain G I} {N : ℝ} {p : ℤ} {a b R:ℝ}
   {z:ℂ}

section
variable (s:ℝ) (x:I)
-- formula on actual momentum tests
omit [TopologicalSpace I] in
theorem backingVert : backing 0 (vertical F) z s x=mend (fun t=> backing 0 F z t x) s := by
   funext m l; unfold backing mend vertical;
   change amount _ s * (∫ t in Iic (0:ℝ),velocity F z x s t m (sr s l))=_
   rw [← integral_const_mul]; change (∫ t in Iic (0:ℝ),plow 0 s (velocity F z x s t) m l)=_
   simp_rw [velocity,snow]; obtain h:= (measurePreserving_add_left (MeasureTheory.volume:Measure ℝ) s).setIntegral_preimage_emb (Homeomorph.addLeft s|>.measurableEmbedding) (fun t=> plow 0 t (F z t x) m l) (Iic s);
   have ht : (fun x:ℝ=>s+x) ⁻¹' (Iic s)= Iic 0:=by ext; simp
   simpa only [ht] using h

variable (hv:Waves R p F) (he:Envelope R a b F) (ha:0<a) (hb:0 ≤ a+b)
include hv he ha hb

local notation "LeftV"=> Iic (0:ℝ)

theorem funded (h:z∈disc R) : Gather (fun t=> backing 0 F z t x) s := by
   intro m l; let f(t:ℝ):= backing 0 F z t x m l; let g(t:ℝ):= velocity F z x s t
   have hx(t : ℝ) : f (s+t)= plow 0 s (g t) m l:= by unfold f g backing velocity; rw [snow]
   have ht:= (measurePreserving_add_left (MeasureTheory.volume:Measure ℝ) s).integrableOn_comp_preimage (f:=f) (s:=Iic s) (Homeomorph.addLeft s|>.measurableEmbedding);
   apply ht.mp; have hs: (fun x:ℝ=>s+x) ⁻¹' (Iic s)= Iic 0:=by ext; simp
   simp_rw [ hs,Function.comp_def,hx ];
   exact (vertical_gather s x he hv ha hb ⟨z,h⟩ m (sr s l)).const_mul _

theorem cut_away (h:z∈disc R) : Shine.Wind (fun a:ℝ=> fun m w=> ∫ t in a..s, backing 0 F z t x m w) atBot
      (backing 0 (vertical F) z s x) := by
   rw [backingVert]; exact fun m w=> intervalIntegral_tendsto_integral_Iic s (funded s x hv he ha hb h m w) tendsto_id

theorem VertRank (hc : z∈disc R): Goods p (vertical F z s x) := by
   refine need_rank.runner _ _ (vertical_gather s x he hv ha hb ⟨ z,by assumption ⟩) (fun t=>need_rank.walk _ _ (hv.funds z hc (s+t) x))
end

variable (hv:Waves R p F) (he:Envelope R a b F) (ha:0<a) (hb:0 ≤ a+b)
include he hb
abbrev τtest (i:Atlas I R) :ℝ := i.2.1
omit hv ha [TopologicalSpace I] in
-- uniform cap, over q,y env
private theorem readBound (m:ℕ)(w:Legs (Shore G m))(v:J→Atlas I R): ∃ C:ℝ,0<C∧
   ∀ (y:J) (s:ℝ), s≤0 → ‖relayAt R F (v y,s) m w‖≤ C*exp (a*τtest (v y))*exp (a*s):= by
   let S:= Iic (0:ℝ); obtain ⟨C,hC,k,hk⟩:= Arc.ride (priceUVvel he hb (fun i:J×S=>i.2.property) (fun i=>τtest (v i.1))
      (fun i=>(v i.1).1) (fun i=> (v i.1).2.2) m ℝ (ray w)) 0;
   simp only [norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul] at hk
   refine ⟨ C*(1+‖(1:ℝ)‖)^k,by positivity,fun i s hs=>?_⟩; specialize hk (i,(⟨s,hs⟩:S)) 1; unfold fieldVal at hk; rw [ray_sail] at hk; rw [mul_assoc (C*_) (exp _)]; exact hk
include hv ha

theorem vertical_hol (s : ℝ)(x : I) : Hol (disc R) (fun z=> vertical F z s x) := by
   constructor; ·
      intro c T ht h; let W:= closedBall c T; have hP := verticalU he hv ha hb (fun i:W=>(⟨ i.val,h i.property⟩:disc R)) (fun _=>s) (fun _=>x)
      exact pay_price hP (exp_pos (a*s)) (b:=fun _=>1) (by intro i; rw [mul_one])
   intro m w c hc; let f(z:ℂ)(t:ℝ):= velocity F z x s t m w;
   obtain ⟨T,hT,hm⟩:= Arc.radius_pay isOpen_ball hc; let V:= closedBall c (2*T); have ht:=integrableOn_exp_mul_Iic ha 0; obtain ⟨C,hC,hP⟩:= readBound he hb m w (fun v : V=> (⟨ v.val,hm v.property⟩,s,x));
   refine (middle (f:=f) (μ:=μ0) isOpen_ball ?_ ?_ hT hm (ht.const_mul (C* exp (a*s))) ?_).differentiableAt
   · exact Eventually.of_forall fun t=> (velocity_hol _ _ hv t).top m w
   · exact fun i hi=> (vertical_gather s x he hv ha hb ⟨i,hi⟩ m w).1
   filter_upwards [show ∀ᵐ t ∂ μ0, t≤0 from ae_restrict_mem measurableSet_Iic ] with t ht v hx; exact hP (⟨ v,hx⟩:V) t ht

variable [FirstCountableTopology I]
theorem vertical_cont : Sway (probe (vertical F) R) := by
   intro m w; let V(z: Atlas I R) (s:ℝ):= relayAt R F (z,s) m w
   have hp:Continuous (uncurry V):= relay_sways he hv m w; apply continuous_iff_continuousAt.mpr; intro i
   obtain ⟨C,hC,hP⟩:= readBound (I:=I) he hb m w (fun x: Atlas I R=>x); let Y:= exp (a*i.2.1); let T(t:ℝ):= C*(1+Y)*exp (a*t)
   change ContinuousAt (fun i:Atlas I R=> ∫ t,V i t ∂ μ0) i
   refine MeasureTheory.continuousAt_of_dominated (bound:=T)
      (Eventually.of_forall fun i=> (vertical_gather i.2.1 i.2.2 he hv ha hb i.1 m w).1) ?_ ((integrableOn_exp_mul_Iic ha 0).const_mul _) (Eventually.of_forall fun a=> (hp.comp ( show Continuous (fun i:Atlas I R=> (i,a)) by fun_prop)).continuousAt)
   filter_upwards [ (show Continuous (fun p:Atlas I R=> exp (a*p.2.1)) by fun_prop).continuousAt (x:=i)|>.eventually (gt_mem_nhds (show Y<1+Y by simp)) ] with t ht
   filter_upwards [show ∀ᵐ t ∂ μ0,t≤0 from ae_restrict_mem measurableSet_Iic] with u hu; refine (hP t u hu).trans ?_; unfold T; gcongr

theorem vertical_waves : Waves R p (vertical F) where
   hol := vertical_hol hv he ha hb
   sway:= vertical_cont hv he ha hb
   token z hZ t x := need_true.runner _ _ (vertical_gather t x he hv ha hb ⟨z,hZ⟩) (fun i=> (Stays (hv.token z hZ (t+i) x) 0 i))
   funds _ h s x:= VertRank s x hv he ha hb h
end YM.MS.ScaleForest
