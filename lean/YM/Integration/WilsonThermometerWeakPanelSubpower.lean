import YM.Integration.WilsonThermometerOrdinaryPanels
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPanelSubpower
open Filter RG Next.Rank Next.Rank.Station Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price PhysicalNext.Repeat.Legato Next.Rank.Atlas
open scoped Topology
variable {G:Gauge} {d:ℕ}

theorem original (A:Levels G) (simple:G.Simple) (P:Panel d) {ε:ℝ} (hp:0<ε):
    ∀ᶠ k:ℕ in atTop,Perch.bill ((P.bag (A.clock.J k)).credit-1) (clim A k)≤A.clock.hatBeta k^ε:=by
  let L:=|P.currency|+10
  have hL:0<L:=by dsimp [L]; positivity
  have high:=hat_rate A simple
  have rate:=Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp high)
  have takes:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp rate
  filter_upwards [takes.eventually (ge_mem_nhds (div_pos hp hL)),high.eventually (eventually_gt_atTop 1)] with k h large
  let x:=A.clock.hatBeta k
  have logpos:0<Real.log x:=Real.log_pos large
  have xPos:0<x:=zero_lt_one.trans large
  have credit:(P.bag (A.clock.J k)).credit-1≤L:=by
    have budget:=(P.bag (A.clock.J k)).fits
    rw [P.vital] at budget
    dsimp [L]
    linarith only [budget,neg_le_abs P.currency]
  change Real.log (Real.log x)^2*Real.exp (-Real.log (Real.log x))≤ ε/L at h
  rw [Real.exp_neg,Real.exp_log logpos,←div_eq_mul_inv] at h
  have final:Real.log (Real.log x)^2*L≤Real.log x*ε:= by
    have b:=(div_le_div_iff₀ logpos hL).mp h
    linarith only [b]
  rw [Real.rpow_def_of_pos xPos]
  exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left credit (sq_nonneg _)).trans final)

end YM.Integration.WilsonThermometerWeakPanelSubpower
end
