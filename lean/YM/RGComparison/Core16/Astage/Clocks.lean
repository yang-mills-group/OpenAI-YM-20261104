import YM.Pert.Asymptotics.RawAxis
import YM.RGComparison.Core16.Witness.Assemble
import YM.OPE.Log.Wallet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Precision at the A stage (not X-frame measuring coupling convention)

Keep ledger geometry or use the actual indices (r,b,t,N,p,..) any of the filters they establish.
Results in rate variables α_t have essentially pointwise algebra meanings; don't assert admissible
geometries enlarge. Basic rates in this file are uniform in N≥m, period arbitrary (we allow any
filter into this sector with m cofinal). Don't change Lambda-m (log of β!) into larger
'powers of log' costs. Use rates-only at strict gain. NOT to infer sharp powers from a subpower.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage
open Function Filter Lattice RG Wilson Pert.Asymptotics OPE Witness Set Metric
open Asymptotics
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G} (H:C.Makes)(hG:G.Simple)
variable {ι : Type*}{l:Filter ι}{m N p : ι→ℕ}
    (h : Tendsto m l atTop) (hk: ∀ᶠ i in l, m i ≤ N i)

-- keep names for billing tests; g=C.path variable. scale C is LOG 1/a; λ is log/log.
def budgetLog (C:Family G) (m:ι→ℕ) (i:ι):= Witness.mainLog C.path.levels (m i)
abbrev rho (C:Family G) (m N p:ι→ℕ) (i:ι):= regulatorRun C (N i) (p i) (m i)
def ruler (C:Family G) (m:ι→ℕ) (i:ι):= C.S.scale (m i)
abbrev frameTime (C:Family G) (m:ι→ℕ) (i:ι):= C.path.levels.clock.hatBeta (m i)
set_option quotPrecheck false
local notation "s"=>ruler C m
local notation "Λ"=>budgetLog C m
local notation "g"=>rho C m N p
local notation "x"=>fun i=>C.path.β (N i) (p i) (m i)
local notation "y∘"=>frameTime C m
variable (C)
include h in
lemma large_s : Tendsto (ruler C m) l atTop := C.S.divergent.comp h
include h hG
lemma large_B : Tendsto (frameTime C m) l atTop :=
    tendsto_atTop_add_const_left _ _ ((large_s C h).const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma large_Λ : Tendsto (budgetLog C m) l atTop := tendsto_atTop_add_const_left _ _
    (Real.tendsto_log_atTop.comp (large_B C hG h))
omit hG in
lemma linear_s : Tendsto (fun i=>frameTime C m i / ruler C m i) l (𝓝 G.slopeConstant):= by
    let c:= C.path.levels.clock.bar
    have ht:= large_s C h
    have h0:= (tendsto_const_nhds («x»:=c)).div_atTop ht
    rw [show G.slopeConstant=0+G.slopeConstant by simp]
    apply (h0.add_const G.slopeConstant).congr'
    filter_upwards [ht.eventually_gt_atTop 0] with i hi
    change _=(c+G.slopeConstant *ruler C m i)/ _; rw [add_div,mul_div_cancel_right₀ _ hi.ne']
lemma negligible : Tendsto (fun i=> budgetLog C m i /ruler C m i) l (𝓝 0):= by
    have hu := large_B C hG h; have hc:= (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu)
    have ht:= linear_s C h; have hw := (tendsto_const_nhds («x»:=(2:ℝ))).div_atTop (large_s C h)
    simpa only [zero_mul,add_zero] using! ((hw.add (hc.mul ht)).congr' (f₂:=fun i=> budgetLog C m i /ruler C m i) (by
        filter_upwards [hu.eventually_gt_atTop 0] with i hi
        change 2 / (s) i+ (Real.log (y∘ i) / y∘ i) * (y∘ i/(s) i) = (2+Real.log (y∘ i))/(s) i
        rw [add_div, div_mul_div_cancel₀ hi.ne'] ))
variable {C}
include H hk
lemma beta_relation : Tendsto (fun i=>C.path.β (N i) (p i) (m i) / frameTime C m i) l (𝓝 1) := by
    have ht : Tendsto (fun i=> C.path.β (N i) (p i) (m i) /s i) l (𝓝 G.slopeConstant):=by
        rw [←b0_normalizes]; apply Metric.tendsto_nhds.mpr; intro ε hz
        filter_upwards [hk,h.eventually (zeroUp_bound C H hz)] with i hi he using he (N i) (p i) hi
    have hh := (ht.div (linear_s C h) (Gauge.slopeConstant_pos hG).ne')
    rw [div_self (Gauge.slopeConstant_pos hG).ne'] at hh
    exact hh.congr' (by filter_upwards [(large_s C h).eventually_gt_atTop 0] with i hi; exact div_div_div_cancel_right₀ hi.ne' _ _)

/-- Two scales of exponent accounting, on any admission cofinal in m. -/
lemma pace : RateIs l (budgetLog C m) (rho C m N p) (-(1/2:ℝ)) :=by
    have ht:= large_Λ C hG h; have hi:=beta_relation (p:=p) H hG h hk
    have he :∀ᶠ i in l, 0 < x i:= hk.mono fun i hi => Overlay.beta_positive H.wilson hi
    refine ⟨he.mono fun _ hi=> inv_pos.mpr (Real.sqrt_pos.mpr hi),?_⟩
    have hh:= ((Real.continuousAt_log («x»:=(1:ℝ)) (by norm_num)).tendsto.comp hi)
    rw [Real.log_one] at hh
    let z i:= Real.log ((x i) / (y∘ i)); let H₂:Tendsto z l (𝓝 0):= hh
    have hv:=(((H₂.sub_const 2).div_atTop ht).const_add 1).const_mul (-(1/2:ℝ))
    rw [add_zero,mul_one] at hv; apply hv.congr'
    filter_upwards [ht.eventually_gt_atTop 0, he] with i ht hi
    change -(1/2:ℝ)*(1+(z i-2)/Λ i)=Real.log (Real.sqrt (x i))⁻¹/Λ i
    have hw:0< y∘ i:=zero_lt_one.trans (C.path.levels.fits.delayed _)
    unfold z; rw [Real.log_div hi.ne' hw.ne',Real.log_inv, Real.log_sqrt hi.le]
    field_simp
    unfold budgetLog mainLog; ring
lemma budget_s_pace : RateIs l (ruler C m) (rho C m N p) 0:=by
    have he:= pace (p:=p) H hG h hk; have hf:=large_Λ C hG h; have hz:=he.rate.mul (negligible C hG h)
    rw [mul_zero] at hz; refine ⟨he.pos,hz.congr' ?_⟩; filter_upwards [hf.eventually_gt_atTop 0] with i hi; rw [div_mul_div_cancel₀ hi.ne']
omit hk H
lemma slow_stage (j:ι→ℕ) (hj:Tendsto j l atTop) (hJ:∀ᶠ i in l,j i ≤ m i) : RateLE l (budgetLog C m) (fun i=>C.path.levels.clock.monitor (j i)) 0 :=by
    let z i:= Real.log (y∘ i); let w:(ι→ℝ):=fun i=> Real.log (frameTime C j i)
    have he:= large_Λ C hG h; have h₁:Tendsto w l atTop:=Real.tendsto_log_atTop.comp (large_B C hG hj)
    have h₂:Tendsto z l atTop:=Real.tendsto_log_atTop.comp (large_B C hG h)
    suffices hc: Tendsto (fun i=> (Real.log (z i))^2 / Λ i) l (𝓝 0) by
       apply ((RateIs.exp' hc).pays he).transfer
       filter_upwards [hJ,h₁.eventually_ge_atTop 1] with i hi hv
       rw [show C.path.levels.clock.monitor (j i)= Real.exp ((Real.log (w i))^2) from rfl,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (Real.exp_nonneg _)]
       have ht :0 ≤ Real.log (w i):=Real.log_nonneg hv
       gcongr
       apply Real.log_le_log (zero_lt_one.trans (C.path.levels.fits.delayed _)); unfold frameTime Calendar.hatBeta
       have := Gauge.slopeConstant_pos hG; gcongr; exact (OPE.scale_mono _).monotone hi
    have hw:= (tendsto_const_nhds («x»:=(2:ℝ))).div_atTop h₂ |>.add_const 1
    have hh:Tendsto (fun i=> (Real.log (z i)) ^2 / z i) l (𝓝 0):= by
       have hp:= (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp h₂
       simpa [Real.rpow_two, Real.rpow_one,Function.comp_def] using hp
    have hf:= hh.div hw (by norm_num); rw [zero_div] at hf; apply hf.congr'
    filter_upwards [h₂.eventually_gt_atTop 0] with i hi; dsimp only [Pi.div_apply]; rw [←div_self hi.ne',← add_div]; apply div_div_div_cancel_right₀ hi.ne'
end YM.RGComparison.Core16.Astage
