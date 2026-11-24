import YM.Integration.WilsonOriginalFullRosterMountedReturn
import YM.Integration.WilsonOriginalFullRosterAngularPayment

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterDatedOpening
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
variable {G:Gauge}
open WilsonOriginalFullRosterAngularPayment

private lemma costs {t T r n:ℕ}(age:t ≤ T)(load:r ≤ n):opening t r ≤ opening T n:=by
  unfold opening
  gcongr

/-- The actual Wilson thermal band supplies the stronger finite crop opening
on any original run, at every physical period, before either regulator. -/
theorem original (simple:G.Simple)(R:Run G)(T n:ℕ):
    ∀ᶠ i:ℕ in atTop, ∀(m N per k:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
      (Ψ:∀j,RG.Rep G (R.family.side j per)),Concourse R.alloy R.kit R.T π Γ m N per k Ψ →
      m ≤ i+1 → (i+1) ≤ N → ∀{β H:ℝ},0<β →
      (Real.sqrt (Ψ (i+1)).beta)⁻¹=(Real.sqrt β)⁻¹ → β ≤ 2*H →
      (Ψ (i+1)).p.B=Nat.ceil ((Real.log H)^2) →
      64*(n+1) ≤ (Ψ (i+1)).p.B ∧ ∀t r,t ≤ T → r ≤ n → opening t r ≤ Real.log H:=by
  let threshold:=max ((64*(n+1):ℕ):ℝ) (opening T n)
  let χ:=fun i=>R.family.path.levels.clock.hatBeta (i+1)
  have grows:Tendsto χ atTop atTop:=(RG01.Physical.hats simple R.alloy.B.a).comp (tendsto_add_atTop_nat 1)
  filter_upwards [grows.eventually_ge_atTop (4*Real.exp threshold)] with i large
  intro m N per k π Γ Ψ course base top β H bp coin therm side
  have measured:χ i/2 ≤ (Ψ (i+1)).beta:=by
    rw [(course.1.walk (i+1) base top).beta]
    exact (R.makes.wilson.represents N per (i+1) top).band.1
  have original_pos:0 ≤ (Ψ (i+1)).beta:=by linarith only [measured,large,Real.exp_pos threshold]
  have eqn:(Ψ (i+1)).beta=β:=calc
    _=(Real.sqrt (Ψ (i+1)).beta)^2:=(Real.sq_sqrt original_pos).symm
    _=(Real.sqrt β)^2:=congrArg (fun t:ℝ=>t^2) (inv_inj.mp coin)
    _=β:=Real.sq_sqrt bp.le
  rw [eqn] at measured
  have lower:Real.exp threshold ≤ H:=by linarith only [large,measured,therm]
  have openAt:threshold ≤ Real.log H:=calc
    _=Real.log (Real.exp threshold):=(Real.log_exp _).symm
    _ ≤ Real.log H:=Real.log_le_log (Real.exp_pos _) lower
  have cap:((64*(n+1):ℕ):ℝ) ≤ Real.log H:=(le_max_left _ _).trans openAt
  have big:(1:ℝ) ≤ Real.log H:=by
    have c:(1:ℝ) ≤ ((64*(n+1):ℕ):ℝ):=by exact_mod_cast (show 1 ≤ 64*(n+1) by omega)
    exact c.trans cap
  have squared:Real.log H ≤ (Real.log H)^2:=by nlinarith only [mul_nonneg (by linarith only [big] : 0 ≤ Real.log H) (sub_nonneg.mpr big)]
  constructor
  · rw [side]
    exact_mod_cast (cap.trans squared).trans (Nat.le_ceil ((Real.log H)^2))
  · exact fun t r age load=>(costs age load).trans ((le_max_right _ _).trans openAt)

end YM.Integration.WilsonOriginalFullRosterDatedOpening
end
