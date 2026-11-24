import YM.Contacts.Junction.Canopy
/-! # dual real/log lift commute: germ apparatus. Hold polynomial roots at full rank. 
 Exact analytic transport & occurrence costs plated. Recover relative exponent with only paintSupply.
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} (P : ChartRatio G) {Λ σ C M A v b:ℝ}{n k:ℕ}
namespace Cove
open Ion
variable (F:Forest S.ratio)(T: Tube G S)(j:S.Choices)
local notation "Y" => Truck G F
local notation "E" => Anchor G c
local notation "Ξ" => (ℝ×E)×Y
local notation "α" => cap G f
def spinner {E0 Y0:Type}[NormedAddCommGroup E0][NormedSpace ℝ E0][NormedAddCommGroup Y0][NormedSpace ℝ Y0] : (ℝ×E0)×Y0 →L[ℝ] ℝ × (E0 × Y0):=(ContinuousLinearEquiv.prodAssoc ℝ ℝ E0 Y0).toContinuousLinearMap -- mathlib?
def pul (w:E×Y):Config G f := F.drape (om F w)
lemma pulley : pul F (G:=G)= (fine G F)∘combineH F := rfl
lemma pulH : Continuous (pul F (G:=G)):= F.continuous_drape.comp (sumH F)
lemma pul0 : pul F (0:E×Y)=1:= by unfold pul; rw [sum_0,Kale.curtain_one]
def lane (w:E×Y):= Kale.bevel f (pul F w)
lemma laneH : Continuous (lane F (G:=G)):= (Kale.bevel_cont _).comp (pulH F)
lemma lane0 : lane F (0:E×Y)=0:= by unfold lane; rw [pul0]; rw [(Kale.summit f (G:=G)).eq_of_nhds]; exact content_one
lemma lane_price (hp: PaintSupply G k A)(z:E×Y) (h:‖z‖≤1)(he:∀ e,G.chord (pul F z e)< Kale.charHeight G): Allows k (lane F (G:=G)) z (composeCost k (Logprice G k) (composeCost k (fineCost G k A) 1)):= by
    have hP := fine_supply F hp; let L:=(combineH (G:=G) F).toContinuousLinearMap; have hx:= feesComb (G:=G) F; have hv : ‖L z‖ ≤ 1 := (L.le_of_opNorm_le hx z).trans ((one_mul ‖z‖).trans_le h); apply revive (U:=pul F) _ he; intro e; rw [pulley]; exact (hP.2.2 _ _ hv).comp (f:=L) (allows_linear hx hv)
lemma lane_analytic : AnalyticAt ℝ (lane F (G:=G)) 0:= by
   obtain ⟨a,ha⟩:= paint_supply G 0; exact (lane_price F ha _ (show ‖(0:E×Y)‖ ≤ 1 by simp) (fun i=>by rw [pul0]; simpa using! (Kale.guardChar G).down)).analytic.analyticAt
lemma mintL : input G f ∘ lane F =ᶠ[𝓝 0] pul F:= by filter_upwards [(((pul0 F) ▸ ((pulH F).tendsto 0))).eventually ((show ∀ᶠ x:Config G f in 𝓝 1, input G f (content x)=x from content_encodes).and (Kale.summit f))] with x hx; unfold Function.comp lane; rw [hx.2,hx.1]
variable (L:Anchor G c→L[ℝ] Truck G F)
local notation "Π" => levelL L
def clockF : Ξ →L[ℝ] ℝ:= (ContinuousLinearMap.fst ℝ ℝ (E×Y)).comp spinner
def localL : Ξ→L[ℝ] E×Y:= (levelL L).comp ((ContinuousLinearMap.snd ℝ ℝ (E×Y)).comp spinner)
def shuttle (x:Ξ):= (clockF F x,lane F (localL F L x))
local notation "ζ" => (localL F L)
local notation "θ" => (clockF (G:=G) F)
def ribbon (x:Ξ):= Lapis.table F j T.up T.high (ζ x)+(θ x)^2* Lapis.mist F P T.up (ζ x)
def matelier (U:PathData G)(p:Clip): cap G f→ℝ:=fun x=> Lintel.Angle.material p U x.1 (input G f x.2)
variable (hp:T.up.Bounds T.high σ C Λ)(hg:Larger (G:=G) S) (ht:LocalRatio P) {ρ:Bid.Dir G c→ AxisChart G F}
local notation "π" => (ribbon P F T j L)
local notation "Zr" => (shuttle F L)
lemma shuttle0 : Zr (0: Ξ)=(0:α):= by simp only [shuttle,map_zero,lane0,Prod.mk_zero_zero]
lemma shuttleH : AnalyticAt ℝ Zr 0:= by unfold shuttle; apply ContDiffAt.analyticAt; exact ((clockF (G:=G) F).contDiff.contDiffAt.prodMk (g:= lane F ∘ localL F L) (ContDiffAt.comp (g:=lane F) (f:=localL F L) (x:=0) (by rw [map_zero]; exact (lane_analytic F).contDiffAt) ((localL F L).contDiff.contDiffAt)))
include hp
-- material & mist metrics
private def trawl (U:PathData G): (E×Y)→ℝ:= fun w=> Precision.loop U (pul F w)
private lemma launchLoop : trawl F T.up=ᶠ[𝓝 0] (turnSeries T.up.loop) ∘ (lane F (G:=G)):= (mintL F).mono (fun _ hx=> congr_arg (Precision.loop T.up) hx.symm)
private lemma launchAna : AnalyticAt ℝ (trawl F T.up) 0:= by
   let v:=turnSeries T.up.loop (m:=f); refine ((AnalyticAt.comp (f:=lane F) (g:=v) (x:=0) ?_ (lane_analytic F))).congr ?_; rw [lane0]; exact turns_analytic _ hp.width hp.two; exact (launchLoop F T hp).symm
include ht
lemma sum_canvas : AnalyticAt ℝ (sumAt F P) 0 ∧ Measurable (sumAt F P):= by
    let P' z:= Real.log (P.J z); have hP : AnalyticAt ℝ P' 0:= ContDiffAt.analyticAt ((ht.germ 0 (mem_ball_self ht.patch)).log (ht.pos 0 (mem_ball_self ht.patch)).ne'); let L(i:F.Free):Y→L[ℝ] G.Color:=(Lapis.Hmap F G i).comp (weld _).toContinuousLinearMap; unfold Lapis.sumAt; exact ⟨ContDiffAt.analyticAt (ContDiffAt.sum fun i _=> (Forge.starts _ hP (L i)).contDiffAt), Finset.measurable_fun_sum _ (fun i _=> ((Real.measurable_log.comp ht.borel).comp (L i).continuous.measurable))⟩
lemma sum_zero : sumAt F P 0=0:= by apply sum_eq_zero; intro i hi; show Real.log _=0; change Real.log (P.J (Fare.windmill F 0 i))=0; rw [wind0,Pi.zero_apply,ht.anchored,Real.log_one]
lemma cell_metric : Lapis.mist F P T.up 0=0 ∧ AnalyticAt ℝ (Lapis.mist F P T.up) 0:= by
   have he:= launchAna F T hp; have hv : trawl F T.up 0=0:= by
      rw [(launchLoop F T hp).eq_of_nhds,Function.comp_apply,lane0]; exact ((jet_zero _ (0:Link G f)).symm.trans ((jet_bridge (turns_analytic _ hp.width hp.two)).mp (turns_low _ hp.width hp.two) _ 0 zero_lt_two));
   exact ⟨show trawl F T.up 0-sumAt F P 0=0 from by rw [hv,sum_zero P F T hp ht,sub_zero], he.sub (Forge.starts _ ((sum_canvas P F T hp ht).1) (ContinuousLinearMap.snd ℝ E Y))⟩
-- angular identification
include hg
lemma ribbonH : AnalyticAt ℝ π 0:= by unfold ribbon; refine (Forge.starts _ (kernelCost F T j hp hg).1 ζ).add ((((θ).analyticAt 0).pow _).mul (Forge.starts _ ((cell_metric P F T hp ht).2) ζ))
lemma ribbon_low {i:ℕ}(hi:i≤2) (x: Ξ) : jet π i x=jet (Lapis.table F j T.up T.high) i (ζ x):= by
   let t:= Lapis.mist F P T.up;  -- meta specify
   let V: Ξ→L[ℝ] ℝ×(E×Y):= (θ).prod ζ; have hx:= cell_metric P F T hp ht; let Z:= ζ; have he:= kernelCost F T j hp hg;
   rw [show π=(Lapis.table F j T.up T.high) ∘ ζ + (conjunct t 2) ∘ V from rfl,serif (Forge.starts _ he.1 _) _ (Forge.starts _ (conjunct_ana hx.2 _) _), Milling.Garf.woven he.1, Milling.Garf.woven (conjunct_ana hx.2 _),joint _ _ _ _ hx.2]; interval_cases i <;> simp [hx.1]
lemma ribbon_quality : Radial.Stationary π:= by
   refine ⟨(ribbonH P F T j L hp hg ht).contDiffAt, ?_,fun u=>?_⟩
   · exact (jet_zero π 0).symm.trans ((ribbon_low P F T j L hp hg ht (by decide) (0:Ξ)).trans ((jet_zero ..).trans (kernelCost F T j hp hg).2.base0))
   exact (ribbon_low P F T j L hp hg ht (by decide) u).trans ((kernelCost F T j hp hg).2.base1 _)
-- topology tools
omit ht hg in
lemma base_caps : Measurable (mainTerm T.high T.up (n:=f)) ∧ Measurable (Precision.loop (n:=f) T.up):= by
   let F t (U:Config G f):= Lintel.Angle.material T.high T.up t U; have hf(t:ℝ): Measurable (F t):=(Lintel.Plata.material_integrable hp f).comp (f:=fun x=> (t,x)) (measurable_const.prodMk measurable_id); have ht:F 0=mainTerm T.high T.up:=by funext x; simp [F,Lintel.Angle.material]; -- issue
   have hw:F 1-F 0=Precision.loop T.up:= by ext x; simp [F,Lintel.Angle.material]
   exact ⟨ht ▸ hf 0, hw ▸ ((hf 1).sub (hf 0))⟩
omit ht in
lemma table_caps : Measurable (Lapis.table F j T.up T.high):= by
   let T':=noiseTaylor S (G:=G); have hN : Measurable (fun w:E×Y=> T' (ship w.1) (pul F w) j):= measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (show Continuous G.price by fun_prop).measurable.comp (Measurable.mul (Measurable.comp (measurable_pi_apply i) (binding.measurable.comp measurable_fst)) (Measurable.inv (Measurable.comp (measurable_pi_apply i) ((S.prediction_meas hg.1 j).comp (pulH F).measurable))))) -- business
   exact ((base_caps T hp).1.comp (pulH F).measurable).add hN
lemma ribbon_caps : Measurable π:= by
   have hm:Measurable (Lapis.mist F P T.up):= (((base_caps T hp).2).comp ((pulH F).measurable)).sub (((sum_canvas P F T hp ht).2).comp measurable_snd); unfold ribbon; let U := ζ; have h : Measurable U:=U.continuous.measurable; exact ((table_caps F T j hp hg).comp h).add ((((θ).continuous.measurable).pow_const (2:ℕ)).mul (hm.comp h))
omit hp ht hg
lemma ray_meter (hp:LocalRatio P) (z:Y) (h : windmill F z∈ mouth P) : YM.Next.SectorChange.pay P (windmill F z)=P.scale^ Fintype.card F.Free * Real.exp (Lapis.sumAt F P z):= by
   unfold sumAt YM.Next.SectorChange.pay; simp only [Real.exp_sum,Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ]; apply congr_arg; apply Finset.prod_congr rfl; intro i _; exact (Real.exp_log (hp.pos _ (h i (Set.mem_univ _)))).symm
end Cove
end YM.Contacts.Junction
