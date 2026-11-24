import YM.Qlocal.Squall.Gentry
import YM.Qlocal.Gauges.Havens
/-!
# Choosing support-fugacity leases for all the mark-core realignments in one step.

*Large*, rather than tiny, forced fugacity is important: restoration will still see the full
K term with its exponential price, including all after/sqrt-divisor prices. Keep unused margin at true point cost
(measured here as inverse-poly of Stella's sites of that metric radius) for all of these, including when marking
instruction horizon is tall. This is in the *same year-level* duration; not inferring anything for a new step at that ζ.
-/
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
variable {G:Gauge}{V:Type}{β Ω d w u ξ ζ z r a s χ c v:ℝ}{m n M k x:ℕ}{B:Marker.Census V}
namespace Lobby
open StellarTree
noncomputable def grain (M:ℕ):ℝ:=32*sites M*sites M
local notation "η"=>StellarTree.spare M
local notation "K"=>grain M
lemma strong (M:ℕ):1≤grain M:=le_trans (by norm_num : (1:ℝ)≤32*1*1) (by unfold grain; have hs:=sites_one M; gcongr)
lemma tall (M:ℕ):0<grain M:=zero_lt_one.trans_le (strong M)
lemma current (M:ℕ):0 < StellarTree.spare M ∧ StellarTree.spare M ≤ 1:= by
 refine ⟨spare_pos M,?_⟩; have h:= keep_range M; unfold StellarTree.keep at h; unfold StellarTree.spare; linarith [h.1]
lemma grain_size (G:Gauge)(L:Side): Geo G L fun x=> grain (Pressure.radiusB x):=by
 have h : Geo G L fun x=> sites (Pressure.radiusB x):= by unfold sites; push_cast; exact ((Geo.radii.joins Geo.radii).joins (Geo.fixed _)).power _
 exact (((Geo.fixed 32).times h).times h)
lemma occupants (z t:ℕ) (G:Gauge) (L:Side): Geo G L fun x=> (Animals.ballCost (t*(Fiord.room z x)):ℝ):= by refine Geo.balling ?_; simp only [Nat.cast_mul]; exact (Geo.fixed _).times (Geo.basic (Trio.rows G L z).2.2.1)
noncomputable def levy (M:ℕ)(w:ℝ):ℝ:=(w*grain M)⁻¹
local notation "μ"=> levy M w
lemma invoked (h:0<w): levy M w *w = K⁻¹:=by unfold levy; field_simp [(tall M).ne']
lemma sheltered (h:0<w)(hx:c≤ K⁻¹): sites M*(μ *w + c)≤ η/2:= by
  rw [invoked h]; refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_right hx _) (sites_pos M).le) (le_of_eq ?_); unfold StellarTree.spare StellarTree.cut grain; field_simp [(sites_pos M).ne']; ring
lemma opens (h:0<w)(hx:w*grain M≤1) : 1 ≤ levy M w:= by
 unfold levy; rw [inv_eq_one_div, le_div_iff₀ (mul_pos h (tall _)),one_mul]; exact hx
noncomputable def crown (M:ℕ):ℝ:= 1+grain M * Real.exp 2
lemma crown_p M: 0 ≤ crown M:=add_nonneg zero_le_one (mul_nonneg (tall _|>.le) (Real.exp_nonneg _))
lemma crown_size (L:Side)(G:Gauge): Geo G L fun x=> crown (radiusB x):= (Geo.fixed 1).joins ((grain_size G L).times (Geo.fixed _))
lemma advice (hv:1≤ v)(h:0<w)(hu:c≤ K⁻¹): v^n* Lot.walletK μ w c ≤ w * (v^n * crown M) := by
 have hz:0 < v:= zero_lt_one.trans_le hv; rw [mul_left_comm w]; apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg hz.le _)
 unfold Lot.walletK; rw [invoked h]; have hy':0 ≤grain M:= (tall _).le; have he:(levy M w)⁻¹=w*grain M:= inv_inv _; have hy :(grain M)⁻¹ ≤1:= inv_le_one_of_one_le₀ (strong _);
 unfold crown; rw [he,mul_add,mul_one,←mul_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_left ((sub_le_self _ zero_le_one).trans (Real.exp_monotone (by linarith only [hu,hy]))) (mul_nonneg h.le hy')) _ -- `add..right?` Lean API right left
open Clock Instrument
variable (L:Side)(G:Gauge)(T:Postage)(d:ℕ)(p:ℝ→ℝ)
set_option quotPrecheck false
local notation "Y"=>betaF G z L
local notation "Γ"=>Real.exp (-Payments.Pairing.kGoal T (betaF G z L) β)
/- regardless of extra polynomial loss demanded at this scale on K. Wages apply uniformly *even AFTER* restoring. -/
lemma post (t:ℝ)(hv:Geo G L p): ∀ᶠ x in atTop, ∀ β:ℝ,inBand (betaF G x L) β → Real.exp (-Payments.Pairing.kGoal T (betaF G x L) β)* (p x) ≤ Instrument.plain.w x*(betaF G x L)^t:= by
 filter_upwards [Scale.after_bill G T (t-1) L, hv.rate 1 zero_lt_one,(Work.E09.betaF_growth G L).eventually_gt_atTop 0] with z hx he hv β hβ; apply (mul_le_mul_of_nonneg_left ((le_abs_self _).trans he) (Real.exp_nonneg _)).trans; refine (mul_le_mul_of_nonneg_right (hx _ hβ) (Real.rpow_nonneg hv.le _)).trans_eq ?_; rw [mul_assoc,← Real.rpow_add hv,sub_add_cancel]
-- universal for all v with positive choice depending stage x only. include constraint grain enough.Coordinator forecast.He.Weight.
lemma minted : ∀ᶠ x in atTop, ∀ β:ℝ,inBand (betaF G x L) β → 1 ≤ levy (radiusB x) (Real.exp (-Payments.Pairing.kGoal T (betaF G x L) β)):= by
 filter_upwards [post L G T _ 0 (grain_size G L)] with x hx β hβ; refine opens (Real.exp_pos _) ((hx _ hβ).trans ?_); rw [Real.rpow_zero,mul_one]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (show 0 ≤ Instrument.plain.P x from Clock.wp _ _|>.le) _))
lemma labelled (t:ℝ)(hv: Geo G L p) : ∀ᶠ x in atTop, ∀ β:ℝ,inBand (betaF G x L) β →∀ c:ℝ,c ≤ (grain (radiusB x))⁻¹ → 1≤ p x → (p x)^d* Lot.walletK (levy (radiusB x) (Real.exp (-Payments.Pairing.kGoal T (betaF G x L) β))) (Real.exp (-Payments.Pairing.kGoal T (betaF G x L) β)) c ≤ Instrument.plain.w x*(betaF G x L)^t:= by filter_upwards [post L G T (fun x=>(p x)^d*crown (radiusB x)) t ((hv.power d).times (crown_size L G))] with x hx β he c h p' using (advice p' (Real.exp_pos _) h).trans (hx _ he)
end Lobby
end YM.Qlocal.Calendars
