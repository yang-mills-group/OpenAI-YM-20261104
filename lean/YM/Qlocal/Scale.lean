import YM.Qlocal.Fortune
/-!
 Booking rough charges and cumulative currency of Step.Hustings. Cost in `Geo`
 per step; explicitly quantified through the actual Coat. Make stages also pay
 the exponent `ceiling` for ALL transitions: no inference that all steps after
 one are alone. Set extra sparse heights for branching caps near Fermi. Senior.S.
 Needs Step occupant ledger Lifeboat.E. Preserve invariant across iterating
 all orders. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Scale
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{m n p : ℕ}{M : Metals G} {D:Rolls M.p}{u t ζ b: ℝ}{L:Side}
section cumulative
/- eventually across any lease, including accumulating bounded by subpowers on ordinary CLOSE windows. -/
def drawer (x:ℝ) := Real.exp (Real.sqrt (Real.log x))
lemma plank (u:ℝ) : 1 ≤ drawer u:= Real.one_le_exp (Real.sqrt_nonneg _)
lemma late (b : ℝ) (k:ℕ) (L : Side) (G : Gauge) : ∀ᶠ x in atTop, b*(Delay.fineMonitor G L x)^k ≤ drawer (betaF G x L):=by
 by_cases hb:0<b; swap; · refine Eventually.of_forall fun x=>?_ ; exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (pow_nonneg (Delay.monitor_pos ..|>.le) _)).trans (Real.exp_nonneg _)
 -- loglog little than sqrt.
 let c (t:ℝ):=Real.sqrt t; let d:= Real.log ∘ fun x=> betaF G x L
 have hd:Tendsto d atTop atTop:=Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)
 have h(o:ℝ):0<o →∀ᶠ x:ℝ in atTop,(Real.log (d x))^(2:ℕ)≤ o*c (d x):=by
    intro hV; have hp:= (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show 0<(1/2:ℝ) by norm_num)).bound hV
    filter_upwards [hd.eventually hp,hd.eventually_ge_atTop (1:ℝ)] with x hx hy; rw [show c=Real.sqrt from rfl,Real.sqrt_eq_rpow]; simp only [Real.rpow_two] at hx; rwa [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hy) _)] at hx
 have hk : 0 ≤ (k:ℝ):= by positivity
 let η:ℝ:=2*(1+k); have hη : 0 < η:= by unfold η; positivity
 filter_upwards [h η⁻¹ (inv_pos.mpr hη), (Real.tendsto_sqrt_atTop.comp hd).eventually_ge_atTop (2*Real.log b)] with t ht hC
 let x:=betaF G t L; have hj : k*(Real.log (d t))^(2:ℕ)≤c (d t)/2:= by
    have he:=ht; rw [mul_comm η⁻¹,← div_eq_mul_inv] at he; apply (le_div_iff₀ (by norm_num)).mpr; apply le_trans _ ((le_div_iff₀ hη).mp he); unfold η; nlinarith [sq_nonneg (Real.log (d t))]; -- annotate k coerces
 nth_rw 1 [← Real.exp_log hb]; unfold drawer; rw [show Delay.fineMonitor G L t=Real.exp ((Real.log (d t))^2) from rfl, ← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; change _ ≤ c (d t); change _ ≤ c (d t) at hC; linarith
lemma saves (L:Side)(f:ℝ→ℝ)(h: RGComparison01.Geo G L f): ∀ᶠ x in atTop, |f x| ≤ drawer (betaF G x L):=by
 obtain ⟨C,b,hC,hZ⟩:= h; filter_upwards [hZ,late C b L G] with x hx hp using hx.trans hp
end cumulative
open Clock Instrument
section force
-- Direct payment uses `Postage.pos` even for every β simultaneously. Can absorb any fixed powers
-- after compare to w0 not only after √. No authority wrt increment.C.
lemma after_bill (G:Gauge) (T : Postage)(b:ℝ)(L : Side): ∀ᶠ x in atTop,
    let y:=betaF G x L; ∀ β,inBand y β → Real.exp (-Payments.Pairing.kGoal T y β) ≤ Instrument.plain.w x*y^b := by
  let f (x:ℝ):=betaF G x L
  have hx:Tendsto f atTop atTop:=Work.E09.betaF_growth ..
  let γ:=Instrument.plain.P; let v:=T.rate/8
  have hv:0<v:= div_pos T.pos (by norm_num)
  have h1: ∀ᶠ x in atTop, Real.exp (-v*γ (f x)^2) ≤ (f x)^b:= by
     have ht : Rate G L (b-1) (fun x=> Real.exp (-v* Delay.fineMonitor G L x^2)) := by
        simpa only [Real.rpow_two] using (Rate.monitor_cutoff (G:=G) (L:=L) (a:=b-1) hv (show 0<(2:ℝ) by norm_num)) -- let reduction.S
     filter_upwards [ht b (by linarith)] with x hx
     rw [show γ (f x)=Delay.fineMonitor G L x from Clock.watch_two _]; exact (le_abs_self _).trans hx
  let q:=G.slopeConstant*Real.log (L.val:ℝ)
  filter_upwards [h1, hx.eventually (Postage.saved plain v hv), just_near q, plain.support 2 one_lt_two, hx.eventually_gt_atTop 0] with x hh ht he hy hx y β hβ
  have hS : Real.exp (-v*γ y^2) ≤ _ := (show Real.exp (-v*γ y^2) ≤ Instrument.plain.w x from ht x (hy x y (same x) he))
  have hV : 0<γ y:= Clock.wp ..
  have hf: 0<gap y:=gp hx
  have hp := band_gap y β hx hβ
  have hz:0<gap β:= (half_pos hf).trans_le hp.1; let γ' := plain.t y/gap β
  have hi : γ y / 2 ≤ γ':= (le_div_iff₀ hz).2 (by unfold Instrument.t; change γ y/2 * _ ≤ gap y* γ y; nlinarith only [hp.2,hV]); have hB:= T.pos
  refine le_trans ?_ (mul_le_mul hS (show Real.exp (-v* γ y^2) ≤ y^b from hh) (Real.exp_nonneg _) (Real.exp_nonneg _)); rw [← Real.exp_add]; apply Real.exp_monotone; unfold Payments.Pairing.kGoal v; nlinarith only [mul_le_mul_of_nonneg_left ((sq_le_sq₀ (half_pos hV|>.le) ((half_pos hV|>.le).trans hi)).mpr hi) hB.le]
end force
end YM.Qlocal.Scale
