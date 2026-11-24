import YM.MS.ScaleForest.PriceVertical
/-!
# Costed integration, IR upper endpoint retained

Uniform parameter statements needed by the recurrence. In particular measure
transforms in the proof put *negative* relative time on `velocity` operations, keeping
the UV direction (remember definitions in co-moving momentum units). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J E:Type} [TopologicalSpace I] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
   {F:Curtain G I} {z:ℂ} {a b c d R : ℝ} {p : ℤ} (t : ℝ) (x:I) {m:ℕ}
   (h : Envelope R a b F) (ht : Waves R p F)
include h ht

-- Sway with BOTH time shifts
def relayAt (R:ℝ)(F:Curtain G I)(i:(Atlas I R)×ℝ):=velocity F i.1.1 i.1.2.2 i.1.2.1 i.2

theorem relay_sways : Sway (relayAt R F) := by
   let D:= (Atlas I R)×ℝ; let q : (Atlas I R)×ℝ→ Atlas I R:= fun i=> (i.1.1,i.1.2.1+i.2,i.1.2.2); have he : Continuous q:= by unfold q; fun_prop
   exact repaintPlow (repaint ht.sway q he) (h.vicinity (s:=Prod.fst ∘ Prod.snd ∘ q) (by unfold q; fun_prop) (Prod.fst ∘ q) (Prod.snd ∘ Prod.snd ∘ q) ) 0 continuous_snd

theorem velocity_sways (z:disc R) : Sway (velocity F z x t) := repaint (relay_sways h ht) (fun s:ℝ=> ((z,t,x),s)) (continuous_const.prodMk continuous_id)

variable (ha : 0<a) (hb : 0 ≤ a+b)
local notation "𝔰"=> Iic (0:ℝ)
include ha hb

theorem vertical_major (W:Touch G m E)(z:disc R) : Majorant μ0 (fun s=> fieldVal (velocity F z x t s m) W):= by
   let f (s:ℝ):= fieldVal (velocity F z x t s m) W
   let U:= velocity F z x t
   have he := (ht.token _ z.property)
   refine lawn (g:=fun _:Unit=> f) (integrableOn_exp_mul_Iic ha 0) ?_ ?_ ?_ ()
   · exact fun _=> Eventually.of_forall fun s:ℝ=> ((fseed (ht.forms _ z.property _ x) 0 s).price m E W).smooth ()
   · exact fun _ p=> (velocity_sways _ x h ht z m (sail W p)).aestronglyMeasurable
   intro j; obtain ⟨C,hC,k,hk⟩:= Arc.ride (priceUVvel h hb (fun i:𝔰=>i.property) (fun _=> t) (fun _=> z) (fun _=> x) m E W) j
   refine ⟨ C*exp (a*t),by positivity,k,fun i=>?_⟩; filter_upwards [show ∀ᵐ s∂μ0, s∈𝔰 from ae_restrict_mem measurableSet_Iic] with s hs p
   specialize hk (⟨s,hs⟩:𝔰) p; simp only [ Pi.zero_apply,abs_zero,add_zero,one_mul ] at hk
   refine le_trans (show ‖iteratedFDeriv ℝ j (f s) p‖ ≤ C*(1+‖p‖)^k* (exp (a*t)*exp (a*s)) from hk) (le_of_eq (by ring))

theorem vertical_gather (z:disc R) : Gather (velocity F z x t) 0:= by intro m l; simpa only [IntegrableOn,Mell.μ0,fieldVal,ray_sail] using (vertical_major t x h ht ha hb (ray l) z).values 1

-- chartwise uniform cost of integration

theorem normCoast {v : J→ℝ} (s:J→ℝ) (Z:J→disc R) (q:J→I) {c : ℝ} (hc:0<c)
   (hv : fell 0 (fun i:J×𝔰=> v i.1*exp (c*i.2))
     (fun i:J× 𝔰=> velocity F (Z i.1) (q i.1) (s i.1) i.2)) : OnTest (vertical F) v Z s q := by
   intro m E _ _ _ w; let T (j:J) (t:ℝ):= velocity F (Z j) (q j) (s j) t
   have hm (j:J) : Majorant μ0 (fun t=> fieldVal (T j t m) w):= vertical_major (s j) (q j) h ht ha hb w _
   apply Arc.hike (fun i=> (hm i).contDiff); intro j; let A:= max 1 (∫ t, exp (c*t) ∂μ0); obtain ⟨C,hC,k,hk⟩:= Arc.ride (hv m E w) j
   simp only [ Pi.zero_apply,abs_zero,add_zero,one_mul ] at hk
   refine ⟨ C*A,mul_pos hC (lt_max_of_lt_left zero_lt_one),k,fun i p=>?_⟩; let L:= C*(1+‖p‖)^k*v i; simp only [ Pi.zero_apply,abs_zero,add_zero,one_mul ]; rw [(hm i).identity]
   change ‖∫ t, iteratedFDeriv ℝ j _ p ∂ μ0‖ ≤ C*A*_ *_; have h_L : 0 ≤ L:= by
     unfold L; have hv : 0≤v i:= by have he:= znon hv (i,(⟨(0:ℝ),mem_Iic.mpr le_rfl⟩:𝔰)); simp at he; exact he
     positivity
   refine (norm_integral_le_of_norm_le ((integrableOn_exp_mul_Iic hc 0).const_mul L) ?_).trans ?_
   · filter_upwards [show ∀ᵐ t ∂ μ0,t∈𝔰 from ae_restrict_mem measurableSet_Iic] with t ht; specialize hk (i,(⟨t,ht⟩:𝔰)) p; unfold L; rw [mul_assoc (C*_) (v i) ]; exact hk
   rw [integral_const_mul, show C*A*(1+‖p‖)^k*v i=L*A from by unfold L; ring]; exact mul_le_mul_of_nonneg_left (le_max_right ..) h_L

-- UV and IR applications of the previous global estimate. IR of rank zero is different.
theorem verticalU (z:J→disc R)(s:J→ℝ)(q:J→I) : OnTest (vertical F) (fun i=> exp (a*s i)) z s q :=
   normCoast h ht ha hb s z q ha (priceUVvel h hb (fun i:J×𝔰=>i.2.property) (fun i=> s i.1) (fun i=> z i.1) (fun i=>q i.1))
theorem verticalI (hc:b<1)(he:p≠0)(z:J→disc R)(s:J→ℝ)(q:J→I) : OnTest (vertical F) (fun i=> exp (-b*s i)) z s q :=
   normCoast h ht ha hb s z q (by linarith:0<1-b) (priceIRvel h hb ht he (fun i:J×𝔰=> s i.1) (fun i=>i.2.property) (fun i=> z i.1) (fun i=>q i.1))

omit h ha hb in
theorem velocity_hol (s:ℝ) : Hol (disc R) (fun z=> velocity F z x t s) := (ht.hol _ _).grazes s 0

end YM.MS.ScaleForest
