import YM.QuadraticLocal.Startup.Market
import YM.AllOrder.Transit.Crown
/-!
# Calendar.Wall needed for Startup Mark high. Obligation on Stage.i menu before selecting ℓ boost.

 `Warm` can augment post-block list for future applications without changing claimant types; construct
 by every.Near. Here need quota sticker for actual TOP Quay.drum extra Room on Birth. Demand
 at any admitted scale with any period. Hera.Time.choose.Price.Width.B POT Station.date prior Cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open PhysicalNext PhysicalNext.Repeat Pressure Precision Next.Scheduling Input Org Roost
open Progress.DirectedRecipe Payments AnalyticBridge VerifiedReset Collection Quotes
open Function Filter Finset Wilson Lattice RG RG.Supply Marker MeasureTheory Push Push.AbsoluteSums
open ConnectedActivityE6 Coat WilsonStartup WilsonStartup.Start AllOrder.Quay AllOrder.Burn
open QuadraticLocal QuadraticLocal.Spes
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
open Real (exp log)
variable {G:Gauge} (S:RG.Stage)
-- demand only Startup M.T.e. Another fixed dim Burn o.operator order if needed estimated separately.Eventually every k≥1.
def Slack (G:Gauge)(S:RG.Stage)(x:ℝ):Prop:= ∀ p : BudgetPoint, Spes.Market.tuning S p x → Decent S.clip p → ∀ β, x/2 ≤ β→ β ≤2*x → ∃ s κ γ:ℝ, Loan p (x/2) s κ γ ∧ Payments.Rates p.B (Timing.normK (Real.log x)) (coupon κ γ) (wad p (|Start.weight S.clip β| *item G p)+QuadraticLocal.Willow.haloSlack p.B) (κ-1)
lemma billing (G:Gauge):∀ᶠ x:ℝ in atTop, Slack G S x:=by
 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually (nearly), Real.tendsto_log_atTop.eventually (Timing.growing.eventually_ge_atTop 1), Real.tendsto_log_atTop.eventually (Timing.loan S.supportExponent), (cartwork (G:=G) S).below (by norm_num) (1/8) (by norm_num)] with i hi he hv hl hw p h hd β hb hb'
 obtain ⟨ht,hB,hp⟩:=h
 let k':= Timing.M (log i); let γ:=Timing.quota (log i); have hA:Start.Loan p (i/2) k' k' γ:=by rw [← Real.exp_log hi]; simpa only [Real.exp_log hi] using (show Loan p (Real.exp (log i)/2) k' k' γ from hl p (ht.trans (tempS hi)) hB hp.2.2|>.1)
 let d₀ := |Start.weight S.clip β|; have h₁:0≤β:=le_trans (by positivity : 0 ≤ i/2) hb; have hj: d₀ ≤ 2*i:=by rw [←Real.norm_of_nonneg h₁] at hb'; exact (Start.weight_le β hd.direct).trans hb'
 have hh:0≤ d₀:=abs_nonneg _; let f:= d₀*item G p; let c:= wad p f; have hF:0≤ f:=mul_nonneg hh (item_pos _ _).le; have h0:0≤ c:=by unfold c wad costFace; positivity
 let t:= Willow.area p.B; have ht0 :0<t:= zero_lt_one.trans_le (Willow.area_ge_one p.B); let s:=Willow.haloSlack p.B
 have hT : t*c ≤ 1/8:=by
    unfold c f d₀ t Willow.area; refine le_trans ?_ ((le_abs_self _).trans hw); let r:=item G p; have htc: r≥0:= (item_pos _ _).le; apply le_trans (mul_le_mul_of_nonneg_left (slotW p _ _ (mul_le_mul_of_nonneg_right hj htc)) (by positivity)); unfold wad scarfE crownE countH scarf r item; rw [hB,ht,hp.1,hp.2.1,hp.2.2]
 have hz:t*s=1/16:=by change t*(1/(16*t))=_; field_simp
 exact ⟨k',k',γ,hA, kernel_currency p (log i) he hv hA rfl (add_nonneg h0 (Willow.spare_pos _).le) (show t*(c+s)≤1/4 from by linarith only [hT,hz])⟩
end YM.AllOrder.Quay
namespace YM.QuadraticLocal.Spes
open Function Filter Finset Wilson Lattice RG RG.Supply Marker MeasureTheory Push Push.AbsoluteSums Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat Pressure Next.Scheduling Input ThroughLaunch Org Roost Legato
open Progress.DirectedRecipe Payments AnalyticBridge VerifiedReset Collection Quotes
open ConnectedActivityE6 Coat WilsonStartup AllOrder AllOrder.Quay AllOrder.Burn AllOrder.Plateau
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge} {n:Side}{s:Sheet G}{L:Rolls s}{Q:Protection L}
namespace Market
structure Till (G:Gauge)(S:RG.Stage)(i:ℕ)(x:ℝ):Prop where
    bearings : Slack G S x
    portions : ∀ o ≤ i, ∀ k ≤ i, ∀ K ≤ i, ∀ d ≤ i, ∀ r ≤ i, ∀ u ≤ i, Tray G S x o k K d r u
lemma onTime (S:RG.Stage)(i:ℕ):∀ᶠ x in atTop,Till G S i x:=by
 let V:=Finset.Iic i
 filter_upwards [billing S G,(eventually_all_finset V).2 fun o ho=> (eventually_all_finset V).2 fun k _=>(eventually_all_finset V).2 fun K _=> (eventually_all_finset V).2 fun d _=> (eventually_all_finset V).2 fun r _=>(eventually_all_finset V).2 fun u _=> offers G S d o k r K u] with x hx hp
 exact ⟨hx,fun o ho k hk K hK d hd r hr u hu=> hp o (mem_Iic.mpr ho) k (mem_Iic.mpr hk) K (mem_Iic.mpr hK) d (mem_Iic.mpr hd) r (mem_Iic.mpr hr) u (mem_Iic.mpr hu)⟩
-- reusable post schedule.Warm.P (replace estimates by new quarry clocks.Protect)
def Warm (t:Delays Q):Prop:=∀ j i,StepStages j i→∀ x,t.betaEntry j≤x→Market.Till G (s.profile i) i x
lemma accrue (V:Delays Q):∃ Y:Delays Q, DelayLe V Y ∧ ∀ W:Delays Q, DelayLe Y W→ Warm W:= by
 obtain ⟨t',-,hx,hy⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ fun i hi=> onTime (G:=G) (s.profile i) i); exact ⟨{V with betaEntry:=t'},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ he j i h x hk=> hy _ _ ((he.beta j).trans hk) i h⟩
end Market
end YM.QuadraticLocal.Spes
