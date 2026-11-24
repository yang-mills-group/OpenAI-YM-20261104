import YM.Integration.WilsonOriginalAlternativeTrialWallet
import YM.Integration.WilsonThermometerSameWalkSectionFare

/-! Actual derivative rent of every finite guarded input at its common K birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialCapital
open Filter Function Finset Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn
open PhysicalNext.Repeat.Legato Push.Local Push.AbsoluteSums AnalyticNext WilsonRetainedMarkedInletRegular
open ActualRunPhysicalPages ActualRunCurvaturePackets
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) {V:Type} [DecidableEq V] [Fintype V] (d:V→ℕ)
local notation "C₀" => R.family
local notation "β" j:max => (C₀).path.levels.clock.hatBeta j
open WilsonOriginalAlternativeTrialWallet

omit [Fintype V] [DecidableEq V] in
private theorem amount {N p K:ℕ} (live:K ≤ N) (ref:∀j,(C₀).ref (d j) ≤ K) (o:V→Site ((C₀).side K p))
    (v:∀j,(C₀).label (d j))(a:ℝ)(j:V):
    0 ≤ WilsonOriginalAlternativeTrialWallet.price R d N p K o v a j:=by
  unfold WilsonOriginalAlternativeTrialWallet.price WilsonOriginalStarPrimaryCatalog.rent
  apply Finset.sum_nonneg
  intro u _
  have raw:= (priced R N p K (d j) live (ref j) (((C₀).labels.level (d j)).core (v j)) (o j)).2.1
  have num:0 ≤ WilsonOriginalStarPrimaryCatalog.amount R N p K (d j) o j (v j) u:=by
    unfold WilsonOriginalStarPrimaryCatalog.amount
    split
    · exact norm_nonneg _
    · apply mul_nonneg _ raw
      unfold moving
      positivity
  exact mul_nonneg (mul_nonneg zero_le_one num) (Real.exp_nonneg _)

omit [DecidableEq V] in
theorem original (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (C₀).path.levels):
    ∀ᶠ K:ℕ in atTop,∀N p (_live:K ≤ N) (_ref:∀j,(C₀).ref (d j) ≤ K),
      ((C₀).path.levels.params K).supportExponent=100 →
      ∀ (o:V→Site ((C₀).side K p)) (v:∀j,(C₀).label (d j)) (τ:ℝ),0<τ→∀j,
        ((WilsonOriginalAlternativeTrialWallet.radius R d N p K o v (100+1+1) τ) j)⁻¹  ≤ 
          (((Fintype.card V:ℝ)+1)*(1+(β K)^6*((C₀).labels.level (d j)).coeffSize (v j)))/τ:=by
  have start:∀ᶠ K:ℕ in atTop,∀j:V,∀N p:ℕ,K ≤ N→((C₀).path.levels.params K).supportExponent=100→
      ∀(o:V→Site ((C₀).side K p))(v:(C₀).label (d j)),
        WilsonOriginalStarPrimaryCatalog.rent R N p K (d j) o j v (fun _=>1) (100+1+1)
           ≤  (β K)^6*((C₀).labels.level (d j)).coeffSize v:=by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [WilsonThermometerSameWalkSectionFare.original R (d j) simple pace forecast] with K cost
    intro N p top budget o v
    simpa only [one_mul] using cost N p top budget o j v (fun _=>1) zero_le_one
  filter_upwards [start] with K cash
  intro N p live ref budget o v τ τp j
  have bill:=cash j N p live budget o (v j)
  rw [WilsonOriginalAlternativeTrialWallet.radius,inv_div,abs_of_nonneg (amount R d live ref o v _ j)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right bill 1) (by positivity)) τp.le

end YM.Integration.WilsonOriginalAlternativeTrialCapital
end
