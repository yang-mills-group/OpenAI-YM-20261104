import YM.GradedFar.Progress
/-!
# Choosing T by the measured clock after fixing B

Use the receding window in M.3 even though its bounding constants are fixed independent of B.
Then order p in that window. Don't need a uniform-in-B limiting power calculation, onsets
in r are after B+costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open FVA2 XSpace XSpace.Normalize Scale Dframe O O.Score O.Enh FVA2.GradedFar FVA2.GradedFar.Budget Trace.Pilot PhysMS
open scoped Topology BigOperators Classical
variable {G:Gauge}(hG:G.Simple) {t:ℝ→ℝ} (ht:Coupling G t)
local notation "g"=> strength G
include hG ht
lemma recedes_by_reading (B:ℝ){a b:ℝ}(ha:a<1)(hb:1<b): ∀ᶠ r in trail,receding (g r) B a b (t r^(-B)):=by
 have H : Tendsto (fun r=> (t r/g r)^(-B)) trail (𝓝 1):= by simpa only [Real.one_rpow] using ((ratio_clock hG ht).rpow_const (p:=-B) (Or.inl one_ne_zero)) -- check arguments
 filter_upwards [H.eventually_const_lt ha,H.eventually_lt_const hb,ht.positive,strength_positive hG] with r h hc hT hp
 rw [Real.div_rpow hT.le hp.le] at h hc
 exact ⟨((lt_div_iff₀ (by positivity)).mp h).le,((div_lt_iff₀ (by positivity)).mp hc).le⟩
end YM.Integration.GradedFar
