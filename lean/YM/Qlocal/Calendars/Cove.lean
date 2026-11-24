import YM.Qlocal.Calendars.Lift
import YM.AllOrder.Burn.Camp
/-! # Stage barter with projected thermal goal and actual Stamp.
 `caps` tighter post-block log goal for multiplicative expenses in any traversal.Time. Still subpowers rather than price ≤z^C where height pays monitor itself.
 Pole in Housing.Lesson: allows paying in all μ-conventions. Later need apply with coherent old budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Calendars
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost Coat ThroughLaunch Animals
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings BudgetPoint
open Push.Uniform Sienna Gauges
open Parabola Reckoner Scribe
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open AllOrder Floe Step Step.PlanV Catch Squall Squall.Lumber Squall.Skull
variable {G:Gauge}{β Ω d₀ w u ξ ζ z t a b s χ c v:ℝ}{m n d M k r:ℕ}
variable {V:Type}[DecidableEq V] (R: Marker.Census V)
namespace Cove
open Lobby Lamp.Frame
variable {L:Side}{Y Z p:ℝ→ℝ}
set_option quotPrecheck false
local notation "B"=>radiusB t
local notation "Φ"=> StellarTree.spare B
local notation "y"=>betaF G t L
local notation "f"=> Fiord.room n t -- danger binder
variable (k r)
lemma young (hk:r≤Burn.horizon k+1) : Rate G L (Skull.score r) (fun t=> Burn.young (betaF G t L) k):= Rate.weaken (Rate.power) (by rw [Burn.sale_eq]; unfold Skull.score graded; push_cast; have ht:(r:ℝ) ≤ ↑(Burn.horizon k)+1:= (by exact_mod_cast hk); unfold Burn.horizon at ht; push_cast at ht; linarith)
variable (u:Bauble G L)
noncomputable abbrev bias (G:Gauge)(L:Side)(t:ℝ)(r:ℕ):ℝ:=betaF G t L^ (score r)
noncomputable abbrev journeyGap (t:ℝ):= u.miss t*Burn.young (betaF G t L) k+Skull.rise G L t u r+Cove.bias G L t r
lemma ahead (hk:r≤Burn.horizon k+1) : Rate G L (score r) (journeyGap k r u):= by
  let F(t:ℝ):= Burn.young (betaF G t L) k; have hu : Rate G L (score r) (fun t=> u.miss t*F t):= by simpa only [zero_add] using (u.progress.rate.mul (young (G:=G) (L:=L) k r hk))
  exact Rate.add (Rate.add hu (Skull.risen G L r u)) Rate.power
variable {k r u}
-- Keep the supplied `Crop.till β, unmasked accuracy`; b price may shrink. Height gap when stamp ε_R even before ζ. Actual needs b * count Π.Sound.Row.Meta.
noncomputable abbrev postTint (G:Gauge)(L:Side)(t:ℝ)(ζ:ℝ)(r:ℕ)(s:ℝ)(n:ℕ):ℝ:= Skull.tone G L t ζ r/ Real.exp ((s+8)*Trio.coverTicket n)
noncomputable abbrev chart_out (R: Marker.Census V)(G:Gauge)(L:Side)(t:ℝ)(ζ:ℝ)(r:ℕ)(s:ℝ)(n:ℕ):= cardB R (StageP.acres n) (s+StellarTree.spare (radiusB t)) (postTint G L t ζ r s n)
local notation "S0"=> postTint G L t ζ r s n
lemma pass_tint (hk:r≤Burn.horizon k+1)(hp:0 ≤ ζ)(he:Geo G L p) (ht:ζ<a)(v:ℕ) : ∀ᶠ t in atTop,(p t)^v * (chart_out R G L t ζ r s n + journeyGap k r u t) ≤ tone G L t a r := by
 let F:=fun t:ℝ => postTint G L t ζ r s n; let d' x:=cardB R (StageP.acres n) (s+1) (F x); have hf: Rate G L (platform ζ r) F:= by unfold F postTint; simp only [div_eq_mul_inv]; exact Rate.power.mul_right _
 have hH: Rate G L (platform ζ r) (chart_out R G L · ζ r s n):= by
    have hd:Rate G L (platform ζ r) d':= Rate.mul_right (Rate.mul_left hf _) _ -- order
    refine hd.compare ((Delay.shift_pos G L).mono fun t ht=> ?_); have hv: 0 ≤ postTint G L t ζ r s n:= div_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _); rw [abs_of_nonneg (by change 0 ≤ cardB _ _ _ _; exact amount _ hv)]; exact (Lobby.side (c:=s+StellarTree.spare (radiusB t)) (v:=s+1) R (le_refl _) hv (add_le_add_right (Lobby.current _).2 _)).trans (le_abs_self (d' t))
 let H:= (he.power v).rate.mul (hH.add ((ahead k r u hk).weaken (le_add_of_nonneg_right hp))); filter_upwards [H _ (by unfold platform; linarith only [ht] : 0+platform ζ r < platform a r)] with t ht; exact (le_abs_self _).trans ht
-- rates also in Loom statement; no need Polynomial amounts exposed when not needed.End.
noncomputable def meterlog (x:ℝ):ℝ:= Real.exp ((Real.log (Real.log x))^3)
lemma log_saver (hp:Geo G L p):∀ᶠ t:ℝ in atTop, |p t| ≤ meterlog (betaF G t L):=by
 obtain ⟨C,k,hc,h⟩:= hp; let z t:= Real.log (Real.log (betaF G t L)); have hz: Tendsto z atTop atTop:= Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth ..))
 let K:ℝ:=k; let Y x:= Delay.fineMonitor G L x; filter_upwards [hz.eventually_ge_atTop (K+1),hz.eventually_ge_atTop (Real.log (C+1)),h] with x hx hh hv; apply hv.trans; refine le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (show 0≤(1:ℝ) from zero_le_one)) (show 0≤Y x^k from pow_nonneg (Delay.monitor_pos ..|>.le) _)) ?_; let t:=z x; have hq: 0 < C+1:= add_pos_of_nonneg_of_pos hc zero_lt_one; have he:1 ≤ t:= (le_add_of_nonneg_left (show 0≤K from Nat.cast_nonneg _)).trans hx; nth_rw 1 [← Real.exp_log hq]; rw [show Delay.fineMonitor G L x= Real.exp (t^2) from rfl,← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; change Real.log (C+1)+K*t^2 ≤ t^3; nlinarith only [show Real.log (C+1) ≤ t from hh,mul_le_mul_of_nonneg_right hx (sq_nonneg (z x)),show K+1 ≤ t from hx,mul_le_mul_of_nonneg_right he (zero_le_one.trans he)]
noncomputable def caps (x:ℝ):ℝ:= min (Scale.drawer x) (meterlog x)
lemma stays (hp:Geo G L p): ∀ᶠ x in atTop,|p x|≤ caps (betaF G x L):= by filter_upwards [Scale.saves _ _ hp,log_saver hp] with x hx ht using le_min hx ht
-- buying b ≤1 with tiny ζ.Demand.At nonlinear cap raises.E. extra caution.
lemma offer (G:Gauge)(L:Side)(h:ζ ≤1/4) (n:ℕ) (r:ℕ): ∀ᶠ t:ℝ in atTop, 0< Cove.postTint G L t ζ r s n∧ Cove.postTint G L t ζ r s n ≤ 1:= by
 let q (x:ℝ) := Cove.postTint G L x ζ r s n; have hd: Rate G L (platform ζ r) q:= by unfold q postTint; simp only [div_eq_mul_inv]; exact Rate.power.mul_right _
 have hp : platform ζ r < 0:=by unfold platform Skull.score graded; push_cast; linarith only [h,Nat.cast_nonneg (α:=ℝ) r]
 filter_upwards [Delay.shift_pos G L, hd 0 hp] with x hx hy; exact ⟨div_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _),(le_abs_self (q x)).trans (hy.trans_eq (Real.rpow_zero _))⟩
end Cove
end YM.Qlocal.Calendars
