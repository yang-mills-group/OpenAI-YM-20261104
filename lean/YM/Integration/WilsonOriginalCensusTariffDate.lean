import YM.Integration.WilsonOriginalCensusTariff

/-! The angular tariff starts on a date determined by the finite physical roster and its
booked polynomial orders. The threshold precedes the running side and the fitted cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusTariffDate
open Filter Lattice Wilson WilsonEmittedFiledCatalogue WilsonEmittedWordJointFare
open Function Finset RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open scoped BigOperators

variable {G:Gauge}
def fee (G:Gauge)(pieces D J:ℕ)(p ℓ:Bool→ℕ)(a:Bool):ℝ:=
  |WilsonEmittedTransitionJet.fee J (ℓ a) (WilsonEmittedCompactTariff.fixed G J (p a+D+1) pieces)|
def ceiling (G:Gauge)(pieces D J:ℕ)(p ℓ:Bool→ℕ):ℝ:=
  max (fee G pieces D J p ℓ false) (fee G pieces D J p ℓ true)

theorem fits (G:Gauge)(pieces D J:ℕ)(p ℓ:Bool→ℕ)(a:Bool):fee G pieces D J p ℓ a ≤ ceiling G pieces D J p ℓ:=by
  cases a
  · exact le_max_left .. 
  · exact le_max_right .. 

def Begun (tube:LinkTube G)(pieces D J T:ℕ)(p ℓ:Bool→ℕ)(H:ℝ):Prop:=
  1<H ∧ 1 ≤ Real.log H ∧ (256*((T:ℝ)+1))^2 ≤ Real.log H ∧
  (∀a,(p a+D+1:ℕ) ≤ Real.log H ∧ (pieces:ℝ) ≤ Real.log H ∧ (2:ℝ)^(p a+D+1) ≤ H) ∧
  groupPrice tube 0*ceiling G pieces D J p ℓ*(1+Real.log H)^(13+J*(max (p false) (p true)+D+1)) ≤ H

theorem original (tube:LinkTube G)(pieces D J T:ℕ)(p ℓ:Bool→ℕ):
    ∀ᶠH:ℝ in atTop,Begun tube pieces D J T p ℓ H:=by
  have individual (a:Bool):∀ᶠ H:ℝ in atTop,(p a+D+1:ℕ) ≤ Real.log H ∧ (pieces:ℝ) ≤ Real.log H ∧
      (2:ℝ)^(p a+D+1) ≤ H:=by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((p a+D+1:ℕ):ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (pieces:ℝ),eventually_ge_atTop ((2:ℝ)^(p a+D+1))] with H a b c
    exact ⟨a,b,c⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop ((256*((T:ℝ)+1))^2),individual false,individual true,
    WilsonOriginalCensusTariff.logarithm (groupPrice tube 0*ceiling G pieces D J p ℓ)
      (13+J*(max (p false) (p true)+D+1))] with H hi early start a b cap
  exact ⟨hi,early,start,fun v=>by cases v <;> assumption,cap⟩

end YM.Integration.WilsonOriginalCensusTariffDate
end
