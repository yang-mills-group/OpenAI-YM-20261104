import YM.SignedWilsonExpansion.F9.Empathy
import YM.Planned.PRIMARY_INTEGRAL_295.East
/-! # eventual monotone receipt bounds and birth of natural length due -/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open Wilson Gauge RG Push Lattice Source Planned.PrimaryIntegral295
open WilsonCoeffUV.Bank
open Set Asymptotics Filter Function Real
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}
lemma hat_rateM (M:Levels G)(g:G.Simple): Tendsto M.clock.hatBeta atTop atTop:= tendsto_atTop_add_const_left _ _ ( M.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos g))
lemma hat_monoM (M:Levels G)(g:G.Simple) : Monotone M.clock.hatBeta:= fun _ _ h=> add_le_add_right (mul_le_mul_of_nonneg_left (PathCost.scales M.S h) (Gauge.slopeConstant_pos g|>.le)) _
lemma threshold_decr (M:Levels G)(g:G.Simple): ∀ᶠ i:ℕ in atTop,∀ j≥i,M.clock.threshold j≤ M.clock.threshold i:=by
    have ht(i:ℕ):0<M.clock.threshold i:= (M.budget i).threshold_pos; have h(i:ℕ):1<M.clock.hatBeta i:= M.fits.delayed i
    let u(i:ℕ):= log (M.clock.hatBeta i); let v(x:ℝ):= -x/2 + (log x)^2
    have he(i): log ( M.clock.threshold i )= v (u i):=by
       have hx:0< M.clock.hatBeta i:= zero_lt_one.trans (h i); have ht':=sqrt_pos.mpr hx; unfold Calendar.threshold Calendar.hatCoupling Calendar.monitor
       rw [log_mul (by positivity) (by positivity),log_exp,log_inv, Real.sqrt_eq_rpow, log_rpow hx]; dsimp only [v,u]; ring
    have t:Tendsto (fun x:ℝ=> 2*log x/x) atTop (𝓝 0):=by
         have hp : Tendsto (fun x:ℝ=> log x/x) atTop (𝓝 0):=by simpa using! (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
         simpa only [mul_div_assoc,mul_zero] using! hp.const_mul 2 -- simp mul_div_assoc direction?
    obtain ⟨U,s⟩:= eventually_atTop.mp (t.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1/2)))
    let S:=max U 1; have hs:0<S:=zero_lt_one.trans_le (le_max_right ..)
    have hv {x:ℝ}(hp: S≤x): HasDerivAt v (-1/2+2*log x/x) x:=by
       have hx:= (hs.trans_le hp).ne'; convert (((hasDerivAt_id' x).neg.div_const 2).add ((Real.hasDerivAt_log hx).pow 2)) using 1 <;> (first| rfl| simp [div_eq_mul_inv])
    have HH : AntitoneOn v (Ici S):=by
       apply antitoneOn_of_deriv_nonpos (convex_Ici S) (fun x hx=>(hv (mem_Ici.mp hx)).continuousAt.continuousWithinAt)
       · exact fun x hx=> (hv (mem_Ici.mp (interior_subset hx))).differentiableAt.differentiableWithinAt
       intro x hx; have hl:= mem_Ici.mp (interior_subset hx); rw [(hv hl).deriv]; have hp:= s x ((le_max_left ..).trans hl); linarith
    have w: Monotone u:= fun i j hp=> Real.log_le_log (zero_lt_one.trans (h i)) (hat_monoM M g hp)
    filter_upwards [ (Real.tendsto_log_atTop.comp (hat_rateM M g)).eventually_ge_atTop S] with i hi j hj; apply (log_le_log_iff (ht j) (ht i)).1; rw [he,he]; exact HH hi (hi.trans (w hj)) (w hj)
end YM.SignedWilsonExpansion.Purchases
