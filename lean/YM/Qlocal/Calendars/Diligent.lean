import YM.Qlocal.Calendars.Fiscal
import YM.Qlocal.Money
import YM.Qlocal.Skating.Seasons
/-! # Convert estimates to conventional powers.Wallet τ<=fixed tolerance. 
 Need k+ for larger mark scope, `r≤Burn.horizon k+1`. valid already across all steps in each
 warmed Opportunity before next shipment. For κ-divided signed budget pay Hull.divisor at same **output**. This includes projections
 with any predicted frequencies under exponent scaling frame. Doesn't infer for more reflected copies etc than BoothRent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Calendars.Form
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 Coat PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Squall.Skull Program Hull Frigus
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z n : ℕ} {δ r θ u v w E C ℓ: ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
open Camp Frigus Time
local notation "Y"=> fineY (a)
lemma print_low {L:Side}(x β ε s:ℝ) (r:ℕ)(hs:1 ≤ Pressure.betaF G x L)(hβ:0<β)(hk:β ≤ 2*Pressure.betaF G x L) (he:ε≤ ((r+1:ℕ):ℝ))(hc:s≤ε/2): Squall.Skull.tone G L x s r ≤ (2:ℝ)^(((r+1:ℕ):ℝ)-ε) * Coat.gStep β ^ (((r+1:ℕ):ℝ)-ε) := by
 let b:=Pressure.betaF G x L; let p:= ((r+1:ℕ):ℝ); let v:= p-ε; have hx:b>0:=zero_lt_one.trans_le hs; have ht : b^(Squall.Skull.platform s r) ≤ b ^ (-(1/2)*v):= by
    apply Real.rpow_le_rpow_of_exponent_le hs ?_
    unfold platform v p Squall.Skull.score AllOrder.Catch.graded; linarith -- notation
 have hh: Coat.gStep b ≤ 2*Coat.gStep β:= Geo.strip hx hβ hk
 rw [Real.rpow_mul hx.le, Real.rpow_neg hx.le,← Real.sqrt_eq_rpow] at ht; refine ht.trans (le_trans (b:=(2*Coat.gStep β)^v) ?_ ?_); exact Real.rpow_le_rpow (Fare.gS b hx|>.1.le) hh (sub_nonneg.mpr he); rw [Real.mul_rpow zero_le_two (Fare.gS β hβ|>.1.le)]
private lemma sheltered (hs:0<v): ∀ᶠ x:ℝ in atTop,Scale.drawer x≤ x^v:= by
 let y (x:ℝ):= Real.sqrt (Real.log x); have hy:Tendsto y atTop atTop:= Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop; filter_upwards [hy.eventually_ge_atTop (1/v), eventually_ge_atTop (1:ℝ)] with x hx he; have hr:0<x:=zero_lt_one.trans_le he
 have hv:0≤ Real.log x:=Real.log_nonneg he; rw [Scale.drawer,Real.rpow_def_of_pos hr]; apply Real.exp_monotone; nth_rw 2 [←Real.sq_sqrt hv]; have hy:1≤y x*v:=(div_le_iff₀ hs).mp hx; have hψ:0≤y x:=Real.sqrt_nonneg _; change y x ≤ y x ^ 2*v; nlinarith only [mul_le_mul_of_nonneg_left hy hψ]
variable (ζ:ℕ→ℝ)(T:ℕ→ℕ){η:ℕ→ℝ}{H:ℕ→ℕ}(K:Camp F η H T)(h:G.Simple)
local notation "r'"=>Real.log 0
local notation "cκ"=> Time.credit
local notation "p★"=> (((p+1:ℕ):ℝ)-δ)
local notation "P"=> Price -- meaningless
include h K
-- use actual roll.Solve H for Tκ and power.Clock_BootETA reciprocal shrink.Y.D.M.We.Start.Elapsed proof. does NOT prove Aff α window. helper expresses bound after masks.
lemma conventional (k:ℕ)(hζ:Tendsto ζ atTop (𝓝 0))(hp:0<δ)(he:δ≤ ((p+1:ℕ):ℝ))(hT:Tendsto T atTop atTop) (hv:0<v) : ∀ᶠ m in atTop,∀ β∈band A.B.a (m+1), Banknote.stipend A m p ζ ≤ (2:ℝ)^p★ * (gStep β)^p★ ∧ Banknote.breadQuota (A:=A) (m:=m) ≤ Hull.soft v β ∧ hardcap A.B.a T m ≤ (Hull.hard A.B.a m)*(gStep β)^k := by
 have hA:=hζ.comp ((A.B.a.fits.deep).comp (tendsto_add_atTop_nat 1)); have hy:Tendsto (fun i=>Hull.fineY a i) atTop atTop:= (Corrected.Grows.beta a h).comp (tendsto_add_atTop_nat 1); filter_upwards [(tendsto_order.mp hA).2 (δ/4) (div_pos hp (by norm_num)),Hull.bagged F K h hT 0 k,(Hull.always_close (A:=A) h 0),hy.eventually (Form.sheltered (v:=v/2) (half_pos hv))] with m ht hf hh ht' β hβ; obtain ⟨hq,hu,hG,hQ⟩:= Hull.blue (A:=A) hβ
 let y:= Hull.fineY (a) m; let L:=D.L (A.B.a.clock.J (m+1)); have hh': y=Pressure.betaF G ((a).clock.hatBeta m) L:= PriceCompiler.beta_eq A.B.valid m; have h2: β ≤ 2*Pressure.betaF G ((a).clock.hatBeta m) L:= hh' ▸ (show β≤2*y from hβ.2); refine ⟨Form.print_low _ _ _ _ p (hh' ▸ hq.le) hu h2 he ?_, ?_, by simpa using hf m le_rfl (hh m le_rfl) β hβ⟩
 · apply le_trans _ (by ring_nf; apply le_rfl : 2*(δ/4)≤ δ/2); exact mul_le_mul_of_nonneg_left ht.le zero_le_two -- syntax tactic
 let v':= Banknote.breadQuota (A:=A) (m:=m); apply (show v'≤_ from (min_le_left (Scale.drawer y) (Cove.meterlog y)).trans ht' ).trans; have hz: y ≤ 2*β:= by linarith only [show y/2≤β from hβ.1]
 apply (Real.rpow_le_rpow (zero_le_one.trans (a|>.fits.delayed _|>.le)) hz (half_pos hv).le).trans_eq; rw [Real.mul_rpow (by norm_num : (0:ℝ)≤ 2) hu.le]; unfold Hull.soft; congr 1
 rw [Real.rpow_neg hG.le]; conv_lhs => rw [show β=(gStep β)^(-2:ℝ) from (by rw [Real.rpow_neg hG.le,Real.rpow_two,hQ,inv_inv])]
 rw [← Real.rpow_mul hG.le,← Real.rpow_neg hG.le]; ring_nf
end YM.Qlocal.Calendars.Form
