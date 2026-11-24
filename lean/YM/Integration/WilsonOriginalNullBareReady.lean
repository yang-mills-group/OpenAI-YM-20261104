import YM.Integration.WilsonOriginalNullBareDeadline
import YM.Integration.WilsonTrueProjectedLocatedSeedTail

/-! The actual terminal basis coefficients of the inverted point (WilsonOriginalNullBareDeadline.original R wood a depth simple o formal point weakly q power margin stable)
have subcritical growth at every cutoff, uniformly in the physical period. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareReady
open Function Filter Finset Lattice Wilson RG Source Labels Trace.Physical
open FormalBulk08 City Pose PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PowerSeries WilsonTrueProjectedPointInverse WilsonTrueProjectedPointProgram WilsonPinnedWidthTransport
open ConnectedActivityE6
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d D:ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "clock" => R.family.path.levels.clock
local notation "s" => R.family.S.scale
variable (wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (simple:G.Simple)(o:Stationary.Loc G 1){U:ℕ→ℕ}
    (formal:WilsonWindowFormalPurchase.Canonical U R.kit)(point:WilsonNeutralPointForecast.Filed R.kit)
    (weakly:WilsonNeutralPointWeakForecast.Filed R.kit)(q:ℕ)

private theorem margin : 0<(1/16:ℝ):=by norm_num
private theorem stable : (1/16:ℝ)<1/8:=by norm_num
variable (power:ℕ)

def first:ℕ:=(eventually_atTop.1 (WilsonOriginalNullBareDeadline.original R wood a depth simple o formal point weakly q power margin stable)).choose

def last {b:ℕ}(allowed:first R wood a depth simple o formal point weakly q power ≤ b)(front:d ≤ R.family.path.levels.clock.J (b+1))
    (cash origin tol:ℝ)(charge:0≤cash)(mass:0≤origin)(target:0<tol) : ℕ:=(eventually_atTop.1 ((eventually_atTop.1 (WilsonOriginalNullBareDeadline.original R wood a depth simple o formal point weakly q power margin stable)).choose_spec b allowed
  front cash origin tol charge mass target)).choose

include simple o formal point weakly in
theorem granted {b:ℕ}(allowed:first R wood a depth simple o formal point weakly q power ≤ b)(front:d ≤ R.family.path.levels.clock.J (b+1))
    (cash origin tol:ℝ)(charge:0≤cash)(mass:0≤origin)(target:0<tol) {j:ℕ}(live:last R wood a depth simple o formal point weakly q power
      allowed front cash origin tol charge mass target ≤ j)
    (digit:∀l,Site (R.family.S.block l))(per:ℕ)(report:ι→ℂ)(fees:∀l,‖report l‖≤origin) :
    let g:=fun t=>Coat.gStep ((R.family.path.rep (j+1) per t).beta)
    let top:=take R q (lift R wood a depth digit (j+1) b g (fun l=>PowerSeries.C (report l)) ((j+1)-b))
    let X:=income R wood a depth digit (j+1) (j+1) q g top
    WilsonOriginalNullCorridor.gain R.family b (j+1)*
      ((∑l:ι,‖∑e:Fin (q+1),X (j+1) e l‖)*(cash*(1+(clock).hatBeta ((j+1)+1))^power)) ≤ tol :=
  (eventually_atTop.1 ((eventually_atTop.1 (WilsonOriginalNullBareDeadline.original R wood a depth simple o formal point weakly q power margin stable)).choose_spec b allowed
    front cash origin tol charge mass target)).choose_spec j live digit per report fees

end YM.Integration.WilsonOriginalNullBareReady
