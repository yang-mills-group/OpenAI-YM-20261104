import YM.FVA2.Index
import YM.FVA2.TreeFormal

/-!
# Transfer Orb's finite stationary argument to every XSpace tree

In contrast to the qlocal analytic estimate, everything here *fixes the regulator first* and
expands the finite link integral. Key support property `Reg.flat_unique` established without any
hypotheses on the near-identity window. This permits a bridge to the analytic-boundary task's
coefficients including O dependent observables, not just a vacuum identification.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeFormal
open XSpace PertExtension PertExtension.Series PertExtension.Series.Radial
open Set Function Filter MeasureTheory Metric Lattice
open scoped Topology ContDiff BigOperators ENNReal
variable {G:Gauge}{R:XSpace.Period}(T:R.Tree)
local notation "X"=> T.Slice G
local notation "Δ"=> T.Field G
local notation "Z"=> Bare.chart G
local notation "L"=> Chart.expLinks G T.Free
local notation "Y"=> Chart.tangent G T.Free

lemma vacant : T.drape (1:X)=1:=by
   funext i; by_cases h:i∈T.edges
   · exact T.drape_tree _ ⟨i,h⟩
   exact T.drape_free _ ⟨i,h⟩
lemma chart_link (x:Δ): Reg.bill T (L x)=T.action x:=rfl
@[fun_prop] lemma folds_cost: Continuous (Reg.bill (G:=G) T):=by unfold Reg.bill; fun_prop

def billrow (O:X→ℝ)(t:ℝ)(x:X) := O x*Real.exp (-Reg.bill T x / t^2)
def cost (O:X→ℝ)(t:ℝ) := (t^Module.finrank ℝ Δ)⁻¹ * ∫ x,billrow T O t x ∂T.measure G
def reading (O:X→ℝ):Δ→ℝ:= Chart.jacobian Z*(O ∘ L)
lemma cost_cont {O:X→ℝ}(h:Continuous O)(t:ℝ):Continuous (billrow T O t) := h.mul (Real.continuous_exp.comp ((folds_cost T).neg.div_const _))
lemma cost_int {O:X→ℝ}(h:Continuous O)(t:ℝ):Integrable (billrow T O t) (T.measure G):= (cost_cont T h t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma changeNear {O:X→ℝ}(h:Continuous O){r t:ℝ}(hr:r<Chart.small G Z)(hv:0<r)(ht:0≤t):
   (t^Module.finrank ℝ Δ)⁻¹ * (∫ x in Chart.chamber G T.Free r,billrow T O t x ∂T.measure G)=
      Radial.partialSum Y (reading T O) T.action r t:=by
   let A:=ball (0:Δ) r; let S:= Chart.chamber G T.Free r; let D:= Radial.disc (E := Δ) t r
   rw [show (∫ x in S, _ ∂T.measure G)=_ from
      Chart.Ratio.chamber_integral (U:=T.Free) (Bare.chart_ratio G) _ (cost_cont T h t).measurable hr hv]
   let f (x:Δ):= Chart.jacobian Z x * billrow T O t (L x)
   have hI x: A.indicator f (t • x)= D.indicator (fun x=> f (t • x)) x:=by
      by_cases h:t•x∈A
      · rw [indicator_of_mem h,indicator_of_mem (show x∈D from h)]
      rw [indicator_of_notMem h,indicator_of_notMem (show x∉D from h)]
   have hs:= Measure.integral_comp_smul_of_nonneg Y (A.indicator f) t (hR:=ht); simp_rw [hI] at hs; rw [integral_indicator (s:=D) (Radial.disc_meas ..), integral_indicator (s:=A) isOpen_ball.measurableSet] at hs
   have he (u:Δ) : Radial.projection (reading T O) T.action t u = f (t • u):=by
      rw [projection_eq]; unfold f reading billrow; rw [Pi.mul_apply,comp_apply,chart_link,mul_assoc]
   unfold Radial.partialSum; simp_rw [he]; exact hs.symm

lemma alone_top {r:ℝ}(hr : r<Chart.small G Z)(hx:0<r): ∃ b>0,∀ u:X,u∈(Chart.chamber G T.Free r)ᶜ → b≤ Reg.bill T u:= by
   let A:=(Chart.chamber G T.Free r)ᶜ
   by_cases h:A.Nonempty
   · obtain ⟨a,ha,hq⟩:=(Chart.Ratio.chamber_open (U:=T.Free) (Bare.chart_ratio G) hr.le|>.isClosed_compl.isCompact).exists_isMinOn h (folds_cost T).continuousOn
     have hv: 0<Reg.bill T a:=lt_of_le_of_ne (div_nonneg (Wilson.energy_nonneg _) (by norm_num)) (fun e=>?_)
     · exact ⟨Reg.bill T a,hv,hq⟩
     apply ha; rw [Reg.flat_unique T e.symm]; exact (fun i _=>⟨0,mem_ball_self hx,G.mat_lieExp_zero⟩)
   exact ⟨1,one_pos,fun _ hu=> False.elim (h ⟨_,hu⟩)⟩

private lemma exp_gone (d N:ℕ){b:ℝ}(hb:0<b):∃ C,0≤C∧∀ t>0,(t^d)⁻¹*Real.exp (-b/t^2)≤ C*t^N:=by
   obtain ⟨C,hC,H⟩:= bounded_exp hb (d+N); refine ⟨C,hC,fun t ht=>?_⟩
   refine le_of_mul_le_mul_right (a:=t⁻¹ ^ N) ?_ (by positivity)
   rw [show C*t^N*t⁻¹^N=C by rw [mul_assoc,← mul_pow,mul_inv_cancel₀ ht.ne',one_pow,mul_one], ← inv_pow,
       show -b/t^2= -b * t⁻¹^2 by rw [inv_pow,div_eq_mul_inv]]
   calc
      _ = t⁻¹^(d+N) * Real.exp (-b*t⁻¹^2):=by rw [pow_add]; ring
      _ ≤ (1+t⁻¹)^(d+N)*Real.exp (-b*t⁻¹^2) := by gcongr; linarith
      _ ≤ _ := H _ (by positivity)

lemma outer {r:ℝ}(hr : r<Chart.small G Z)(hr':0<r){O:X→ℝ}(h:Continuous O)(N:ℕ): ∃ C,0≤C ∧∀ t>0,
   ‖(t^Module.finrank ℝ Δ)⁻¹ * (∫ x in (Chart.chamber G T.Free r)ᶜ,billrow T O t x ∂T.measure G)‖ ≤ C*t^N:=by
   obtain ⟨b,hb,H⟩:= alone_top T hr hr'; obtain ⟨C,hC,hC'⟩:= exp_gone (Module.finrank ℝ Δ) N hb
   obtain ⟨a,ha⟩:=isCompact_univ.exists_bound_of_continuousOn h.continuousOn
   refine ⟨|a| *C,mul_nonneg (abs_nonneg a) hC,fun t ht=>?_⟩
   let S:=(Chart.chamber G T.Free r)ᶜ; let M:=T.measure G; let K:=|a| *Real.exp (-b/t^2)
   have he : ∀ᵐ x ∂M.restrict S, ‖billrow T O t x‖ ≤ K:=by
     filter_upwards [ae_restrict_mem (Chart.Ratio.chamber_open (U:=T.Free) (Bare.chart_ratio G) hr.le |>.measurableSet.compl)] with x hx
     unfold billrow; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
     refine mul_le_mul ((ha x (mem_univ _)).trans (le_abs_self _)) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (abs_nonneg _)
     exact div_le_div_of_nonneg_right (neg_le_neg (H _ hx)) (sq_nonneg _)
   have hv: ‖∫ x in S,billrow T O t x ∂T.measure G‖ ≤ K:= by
     refine (norm_integral_le_of_norm_le (integrable_const _) he).trans ?_
     have hK:0≤K:=by unfold K; positivity
     apply (setIntegral_le_integral (integrable_const K) (Filter.Eventually.of_forall (fun _=>hK))).trans
     simp [M]
   rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (t^Module.finrank ℝ Δ)⁻¹)]; grw [hv]; unfold K
   rw [mul_left_comm _ |a|,mul_assoc]; exact mul_le_mul_of_nonneg_left (hC' _ ht) (abs_nonneg a)

lemma saddle_ready : Radial.Stationary (T.action (G:=G)) where
  smooth:= (T.continuousJet G).of_le le_top
  base0:= (T.action_jets G).1
  base1 x:=by rw [jet,iteratedFDeriv_one_apply,(T.action_jets G).2.1]; simp

lemma reading_smooth {O:X→ℝ}(hf: ContDiffAt ℝ ∞ (O ∘ L) 0) : ContDiffAt ℝ ∞ (reading T O) 0:= (ContDiffAt.mul ((Chart.Ratio.jacobian_smooth (U:=T.Free) (Bare.chart_ratio G)).of_le le_top) hf)

theorem amounts {O:X→ℝ}(hc:Continuous O)(hf:ContDiffAt ℝ ∞ (O ∘ L) 0): Tested.Aspiration (cost T O) (moment Y (reading T O) T.action):=by
   intro j; obtain ⟨δ,hδ,H⟩:= Radial.Stationary.rescale_estimate Y (F:=saddle_ready T (G:=G)) (hf:=reading_smooth T hf)
      ((Chart.Ratio.jacobian_meas (U:=T.Free) (Bare.chart_ratio G)).mul (hc.measurable.comp Chart.expLinks_meas))
      (show Measurable (T.action (G:=G)) by rw [show T.action (G:=G)=Reg.bill T ∘ L from rfl]; exact (folds_cost T).measurable.comp Chart.expLinks_meas)
      (quadratic_min T.action (fun u hu=>by rw [action_radial]; exact half_pos (T.quadratic_pos hu))) j
   let r:=min δ (Chart.small G Z) / 2; have hp:0<r:=half_pos (lt_min hδ (Chart.Ratio.small_pos (Bare.chart_ratio G)))
   have hs:r<min δ (Chart.small G Z):= half_lt_self (lt_min hδ (Chart.Ratio.small_pos (Bare.chart_ratio G)))
   have hr:r<Chart.small G Z:=hs.trans_le (min_le_right ..)
   obtain ⟨a,h⟩:=H r ⟨hp,hs.trans_le (min_le_left ..)⟩
   obtain ⟨c,hC,h'⟩:= outer T hr hp hc (j+1); let A:=Chart.chamber G T.Free r
   refine ⟨|a|+c,add_nonneg (abs_nonneg a) hC,?_⟩
   filter_upwards [h,Tested.eventually_pos] with t ht hh; unfold cost Tested.peval Zone.eval; simp only [Pi.sub_apply,smul_eq_mul]
   rw [← integral_add_compl (s:=A) (Chart.Ratio.chamber_open (Bare.chart_ratio G) hr.le|>.measurableSet) (cost_int T hc t), mul_add,changeNear T hc hr hp hh.le, add_sub_right_comm,add_mul]
   exact (norm_add_le ..).trans (add_le_add (ht.trans (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity))) (h' t hh))

open PowerSeries
lemma ext_zero : 0 < moment Y (Chart.jacobian Z) (T.action (G:=G)) 0 := by
   unfold moment normTerm; simp [integrandSeries,Zone.mul,expsum,Zone.TaylorPow,MeasureTheory.integral_const_mul];
   have hx : 0< Chart.jacobian (U:=T.Free) Z 0:=by rw [(unmasked_haar T (G:=G)).eq_of_nhds]; change 0<cH T G*Bare.relative T 0; rw [Bare.relative_one,mul_one]; exact cH_pos T G
   simp_rw [same_kernel T]; exact mul_pos hx (TaylorWick.mass_pos ..)

def system (O:X→ℝ):= Tested.divide (moment Y (reading T O) T.action) (moment Y (Chart.jacobian Z) T.action)
def actual (O:X→ℝ) (t:ℝ):=(∫ x,billrow T O t x ∂ T.measure G)/(∫ x:X,billrow T 1 t x ∂ T.measure G)

theorem quotients {O:X→ℝ}(hc:Continuous O)(hf:ContDiffAt ℝ ∞ (O ∘ L) 0): Tested.Aspiration (actual T O) (system T O):=by
  intro i
  have he:= (amounts T hc hf).quotient (amounts T (G:=G) (O:=1) continuous_const contDiffAt_const) (show moment _ (reading T _) _ 0≠0 from ?_) i
  · obtain ⟨c,hC,h⟩:= he; refine ⟨c,hC,?_⟩; filter_upwards [h,Tested.eventually_pos] with t ht hh
    change ‖cost T O t / cost T 1 t - _‖≤_ at ht
    have hv : reading T (1:X→ℝ)=Chart.jacobian Z:= by unfold reading; change Chart.jacobian Z*1=_; rw [mul_one]
    unfold cost at ht; rw [mul_div_mul_left,hv] at ht
    · exact ht
    positivity
  unfold reading; change moment _ (Chart.jacobian Z*1) _ _≠ _; rw [mul_one]; exact (ext_zero T).ne'
end YM.FVA2.TreeFormal
