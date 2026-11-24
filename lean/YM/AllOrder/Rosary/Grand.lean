import YM.AllOrder.Rosary.Room
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/-! Pole & Estimate budgets billed after L. Coarse T.cost=up betaHat(s) or down exactly (for simplicity). -/
namespace Repair
open Push PriceCompiler Floe Floe.Step Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
namespace PostP
open Guard Lapis Gyro Time Payments Next.Scheduling
variable (G)(g:G.Simple)(p:Stage)(u:ℕ)(b H:ℝ)
lemma hedge_ok {B:ℕ} {f g':ℝ} {a v t w κ:ℝ}(h:Rates B a f g' κ)(he:0≤v)(hh:v≤f)(hq:0≤w)(hk:w≤g')(ht:a≤t): Rates B t v w κ:=by
    have hl : inflation v w κ ≤ inflation f g' κ := add_le_add (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left hk zero_le_two)
    exact ⟨h.heading,he,hq,hk.trans h.soft_limit,(mul_le_mul_of_nonneg_left hl (by positivity)).trans h.capital, ((mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_monotone hl) _) (Real.exp_pos _).le).trans h.returns).trans ht⟩ -- Args
variable {F:Postage}(A:Forecast F)
lemma strong (h:0≤H):∀ᶠ x:ℝ in atTop,∀ β,inBand (x+H) β→ ∀ B ≤ Next.Scheduling.Clock.cover x, Rates B (Real.exp (-Pairing.kGoal F (x+H) β)) (A.pair.strong (x+H) β) (x^(-(1/3:ℝ))) (Pairing.kGoal F (x+H) β):= by
 let τ:=(1/2:ℝ);
 filter_upwards [eventually_gt_atTop (1:ℝ),(Next.Scheduling.Clock.similar_gap_power τ) 2 one_lt_two, just_near H,(tendsto_atTop_add_const_right _ H tendsto_id).eventually A.pair.currency, clockI.slack (by norm_num : -(1/3:ℝ)< -(1/4)) 2] with i hi ht hh hv he β hb B hB
 have hq: inBand (i+H) β:=hb; let v:=Next.Scheduling.Clock.cover; have hI : 0 < i := (by linarith); have hg: v i ≤ v (i+H):= Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_pos hi|>.le) (Real.log_le_log hI (by linarith)) _); have hw: i^(-(1/3:ℝ))≤ A.pair.mild (i+H):= by
    unfold Pairing.mild Forecast.pair; let a:=Next.Scheduling.Clock.gap i; simp only [pow_zero,mul_one,Real.rpow_zero]; have hp:= (ht i (i+H) (Next.Scheduling.Clock.same i) hh); have hc:a^τ=i^(-(1/4:ℝ)):=by unfold a Next.Scheduling.Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hI.le,← Real.rpow_mul hI.le, show -(1/2:ℝ)*τ=-1/4 by unfold τ; norm_num]; ring_nf -- -1/4 = -(1/4)
    have hx:2*i^(-(1/3:ℝ))≤ a^τ:=hc.symm ▸ he.le; refine le_trans (b:=Next.Scheduling.Clock.gap (i+H)^τ) ?_ (le_mul_of_one_le_left (by unfold Next.Scheduling.Clock.gap; positivity) (le_max_left ..)); linarith only [hx,show a^τ ≤ 2*Next.Scheduling.Clock.gap (i+H)^τ from hp]
 exact hedge_ok (hv.2 _ hq B (hB.trans hg)) (hv.2 _ hq B (hB.trans hg)|>.hard) le_rfl (Real.rpow_pos_of_pos hI _).le hw le_rfl
lemma prefer : ∀ᶠ x:ℝ in atTop,∀ p':BudgetPoint, Time.Same p p' → p'.B=Pressure.radiusB x→Width (pearl p') p.clip p.width := by
 filter_upwards [(tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto).eventually_ge_atTop (4*(p.supportExponent+4) / p.width)] with x hx p' hp he; have h:=p.width_pos; refine ⟨h,p.slow_selector,?_⟩; unfold pearl preExponent; dsimp; apply (div_le_iff₀ (Nat.cast_pos.mpr p'.B_pos)).mpr; rw [hp.2.2,he]; have hu:4*(p.supportExponent+4)≤ Pressure.radiusB x * p.width:= (div_le_iff₀ h).mp hx; linarith
-- billing actor small ledger: actual model Λ−delta prediction. one frame Plan Yθ given by forecast; uses exact phi diff from puzzle. ζ external K cost ledger Marlin may be zero. All costs.True β harness separately. Keep Center stats.
end PostP
end Repair
end YM.AllOrder.Rosary
