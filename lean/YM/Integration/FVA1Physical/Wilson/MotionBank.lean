import YM.Integration.FVA1Physical.Wilson.ForcedTransport
import YM.Integration.FVA1Physical.Wilson.LocalExterior
import YM.MSbar.Cottage.Posture

/-! Independent Wilson energy increments on pairs of genuine measured forest
postures. Both chart copies have empty exact-cover inventories. The original
fields may retain arbitrary remote failures. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {f : Side}

private theorem chart_segment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x z : V} {w : ℝ} (hx : ‖x‖≤w) (hz : ‖z‖≤w) (t : ℝ) (ht : t∈Set.Icc 0 1) :
    x+t • (z-x)∈Metric.closedBall 0 w := by
  have A := convex_closedBall (0:V) w (mem_closedBall_zero_iff.mpr hx) (mem_closedBall_zero_iff.mpr hz)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  rw [show x+t • (z-x)=(1-t) • x+t • z by rw [sub_smul,one_smul,smul_sub];abel]
  exact A

def moveEvent (χ κ : Config G f → Config G f) (g w H : ℝ) : Set (Config G f) :=
    (χ ⁻¹' regularInputs g w) ∩ ((χ ∘ κ) ⁻¹' regularInputs g w) ∩
    {U | (∑ i, |(chartLog g (χ U)-chartLog g (χ (κ U))) i|)≤H}

def moveBank (R : Rep G f) (χ κ : Config G f → Config G f) (B : Positions (Primary f G)→ℝ)
    (g w H : ℝ) : Config G f→ℝ :=
  (moveEvent χ κ g w H).piecewise (fun U=>B (chartLog g (χ U))-B (chartLog g (χ (κ U))))
      (fun U=>R.exponent U-R.exponent (κ U))

theorem moveBank_meas (R : Rep G f) {σ C δ Λ ζ : ℝ} (law : R.Lawful σ C Λ δ ζ)
    (χ κ : Config G f → Config G f) (cχ : Measurable χ) (cκ : Measurable κ)
    (B : Positions (Primary f G)→ℝ) (cB : Continuous B) (g w H : ℝ) : Measurable (moveBank R χ κ B g w H) := by
  have x := (chartLog_meas (G:=G) (f:=f) g).comp (cχ.comp cκ)
  have z := (chartLog_meas (G:=G) (f:=f) g).comp cχ
  have one (i : Primary f G) := ((measurable_pi_apply i).comp (z.sub x)).abs
  have evt : MeasurableSet (moveEvent χ κ g w H) := ((cχ (regular_meas g w)).inter
    ((cχ.comp cκ) (regular_meas g w))).inter (measurableSet_le (Finset.measurable_fun_sum _ fun i _=>one i) measurable_const)
  exact ((cB.measurable.comp z).sub (cB.measurable.comp x)).piecewise evt
    ((R.exponentEnv law).meas.sub ((R.exponentEnv law).meas.comp cκ))

/-- A physical local displacement known to have the canonical two copy geometries.
The dimensional price is the measured L1 displacement of these copies. -/
theorem moveBank_price (R : Rep G f) {σ C δ Λ ζ : ℝ} (law : R.Lawful σ C Λ δ ζ)
    (pos : ∀ U, 0<R.eval U) {g w H ε fee : ℝ} (hg : g≠0) (hw : 0<w) (e₀ : 0≤ε) (hH : 0≤H) (hfee : 0≤fee)
    (χ κ A : Config G f → Config G f) (B : Positions (Primary f G)→ℝ) {Y : Support f} {d M : ℕ}
    (deep : Heath.Cottage.deepCopy R.p d≤M) (wide : R.p.B≤M) (dec : WilsonStartup.Decent R.clip R.p)
    (beta : 0≤R.beta) (feeOK : Heath.Cottage.silkRoad C σ δ Λ R.beta Y.card M R.p d≤fee)
    (rows : ∀ x v : Positions (Primary f G),
      (∀ a∈Set.Icc (0:ℝ) 1, x+a • v ∈ Metric.closedBall 0 w) →
      |(Real.log (R.eval (palace (g • (x+v)))) - B (x+v)) -
       (Real.log (R.eval (palace (g • x)))-B x)| ≤ (∑ i,|v i|)*(ε/w))
    {U : Config G f} (phase : ∀ V,R.exponent (A V)=R.exponent V)
    (place : Heath.Place Y M (A U) (χ U) (A (κ U)) (χ (κ U)) R.p.threshold)
    (copied : Heath.Place Y M (χ U) (χ U) (χ (κ U)) (χ (κ U)) R.p.threshold)
    (clear : flags R.p.threshold (χ U)=∅) (clear' : flags R.p.threshold (χ (κ U))=∅) :
    |moveBank R χ κ B g w H U-(R.exponent U-R.exponent (κ U))| ≤ H*(ε/w)+fee := by
  rw [moveBank]
  by_cases good : U∈moveEvent χ κ g w H
  · rw [Set.piecewise_eq_of_mem _ _ _ good]
    let z := chartLog g (χ U)
    let x := chartLog g (χ (κ U))
    have rz : palace (g • z)=χ U := recover_chartLog hg _ (Set.mem_univ_pi.mp good.1.1.1)
    have rx : palace (g • x)=χ (κ U) := recover_chartLog hg _ (Set.mem_univ_pi.mp good.1.2.1)
    have p := rows x (z-x) (chart_segment good.1.2.2 good.1.1.2)
    rw [show x+(z-x)=z by abel,rz,rx,log_eval R pos,log_eval R pos,
      Activities.gas_one _ _ clear,Activities.gas_one _ _ clear',Real.log_one,add_zero,add_zero] at p
    have bound := Heath.Cottage.copied law place deep copied wide dec beta
    rw [phase,phase] at bound
    have bound2 := p.trans (mul_le_mul_of_nonneg_right (show (∑ i,|(z-x) i|)≤H from good.2)
      (div_nonneg e₀ hw.le))
    have changing : (R.exponent (χ U)-R.exponent (χ (κ U)))-(B z-B x) =
        (R.exponent (χ U)-B z)-(R.exponent (χ (κ U))-B x) := by ring
    have step : |(R.exponent (χ U)-R.exponent (χ (κ U)))-(B z-B x)| ≤ H*(ε/w) := by
      rw [changing]; exact bound2
    rw [abs_sub_comm]
    exact (abs_sub_le (R.exponent U-R.exponent (κ U)) (R.exponent (χ U)-R.exponent (χ (κ U)))
      (B z-B x)).trans (by linarith only [bound,step,feeOK])
  rw [Set.piecewise_eq_of_notMem _ _ _ good,sub_self,abs_zero]
  exact add_nonneg (mul_nonneg hH (div_nonneg e₀ hw.le)) hfee

end YM.Integration.FVA1Physical.Wilson
