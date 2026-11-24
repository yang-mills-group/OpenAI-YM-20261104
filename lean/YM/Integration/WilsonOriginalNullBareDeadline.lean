import YM.Integration.WilsonOriginalNullBareStock
import YM.Integration.WilsonTrueProjectedLocatedSeedTail

/-! The actual terminal basis coefficients of the inverted point program
have subcritical growth at every cutoff, uniformly in the physical period. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareDeadline
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

include simple o formal point weakly in
theorem original (power:ℕ){δ:ℝ}(margin:0<δ)(stable:δ<1/8) :
    ∀ᶠ b:ℕ in atTop, ∀ (_:d ≤ (clock).J (b+1))(cash origin tol:ℝ),
      0 ≤ cash → 0 ≤ origin → 0<tol → ∀ᶠ j:ℕ in atTop,
    ∀ (digit:∀l,Site (R.family.S.block l))(per:ℕ)(report:ι→ℂ), (∀l,‖report l‖ ≤ origin) →
    let g:=fun t=>Coat.gStep ((R.family.path.rep (j+1) per t).beta)
    let top:=take R q (lift R wood a depth digit (j+1) b g (fun l=>PowerSeries.C (report l)) ((j+1)-b))
    let X:=income R wood a depth digit (j+1) (j+1) q g top
    WilsonOriginalNullCorridor.gain R.family b (j+1)*
      ((∑l:ι,‖∑e:Fin (q+1),X (j+1) e l‖)*(cash*(1+(clock).hatBeta ((j+1)+1))^power)) ≤ tol := by
  classical
  obtain ⟨K,V,positive,paid⟩:=WilsonOriginalNullBareStock.original R wood a depth simple o formal point weakly q margin
  filter_upwards [paid] with b ready
  intro front cash origin tol charge initial yes
  let C:=K*(Λ b)^V*origin*cash
  have hC:0 ≤ C:=by
    have L:0 ≤ Λ b:=(by norm_num : (0:ℝ)≤1).trans (WilsonTrueProjectedPointClock.log_rise R simple (le_refl b)).1
    exact mul_nonneg (mul_nonneg (mul_nonneg positive.le (pow_nonneg L _)) initial) charge
  obtain ⟨lower,cut⟩:=eventually_atTop.1 (WilsonTrueProjectedLocatedSeedTail.original R simple b power hC stable yes)
  filter_upwards [eventually_ge_atTop lower,eventually_ge_atTop b] with j able pointwise
  intro digit per report fares
  dsimp only
  let N:=j+1
  let g:=fun t=>Coat.gStep ((R.family.path.rep N per t).beta)
  let top:=take R q (lift R wood a depth digit N b g (fun l=>PowerSeries.C (report l)) (N-b))
  let X:=income R wood a depth digit N N q g top
  let B:=∑l:ι,‖∑e:Fin (q+1),X N e l‖
  let H:=(1+(clock).hatBeta (N+1))^power
  have pay:=ready front digit j per pointwise report origin initial fares
  dsimp only at pay
  change B ≤ K*(Λ b)^V*origin*Real.exp (δ*(s N-s b)) at pay
  have hH:0 ≤ H:=pow_nonneg (by have h:1≤(clock).hatBeta (N+1):=(R.family.path.levels.fits.delayed (N+1)).le;linarith) _
  have bound:B*(cash*H)+0 ≤ C*H*Real.exp (δ*(s N-s b)):=by
    rw [add_zero]
    calc
      _ ≤ (K*(Λ b)^V*origin*Real.exp (δ*(s N-s b)))*(cash*H):=mul_le_mul_of_nonneg_right pay (mul_nonneg charge hH)
      _ = _:=by dsimp only [C];ring
  simpa only [add_zero] using cut N (by dsimp [N];omega) (B*(cash*H)) 0 bound

end YM.Integration.WilsonOriginalNullBareDeadline
