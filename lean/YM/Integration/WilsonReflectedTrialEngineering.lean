import YM.Integration.WilsonReflectedFullPanel
import YM.Integration.WilsonOriginalMicroscopicGuardedGrid
import YM.Integration.WilsonOriginalNullOriginGrid
import YM.Integration.WilsonReceivedQUnitPosterior

/-! Normalize the original local-section numerator on its actual two
dates. The guarded source starts on the already evolved N-cutoff vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedTrialEngineering
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)

private theorem dress (d i:ℕ)(F:space (i+1)→ℂ)(paid:Integrable F (prior G _))(z:ℂ):
    GermGraph.transition (C:=C₀) d N p i (z • F)=z • GermGraph.transition (C:=C₀) d N p i F:=by
  rw [GermGraph.transition,blast,StepData.push_smul _ _ _ _ paid]
  simp only [GermGraph.transition,blast,smul_smul,mul_comm]

theorem scalar (d f:ℕ)(n:ℕ)(F:space (f+n)→ℂ)(paid:Integrable F (prior G _))(z:ℂ):
    flow (C₀) d N p f n (z • F)=z • flow (C₀) d N p f n F:=by
  induction n with
  | zero => rfl
  | succ n ih => rw [flow,flow,dress R d (f+n) F paid z];exact ih _ (WilsonOriginalNullCorridor.integrable (C₀) d N p paid)

theorem weight (d f:ℕ)(n:ℕ)(F:space (f+n)→ℂ)(paid:Integrable F (prior G _)):
    flow (C₀) d N p f n F=((((C₀).S.steps f n).val:ℂ)^d) • flow (C₀) 0 N p f n F:=by
  induction n with
  | zero => simp [flow,Schedule.steps]
  | succ n ih =>
    let U:=GermGraph.transition (C:=C₀) 0 N p (f+n) F
    let L:ℂ:=((C₀).S.block (f+n)).val
    have good:Integrable U (prior G _):=WilsonOriginalNullCorridor.integrable (C₀) 0 N p paid
    have eq:GermGraph.transition (C:=C₀) d N p (f+n) F=L^d • U:=by simp [GermGraph.transition,blast,U,L]
    rw [flow,flow,eq,scalar R d f n U good,ih U good,smul_smul,Schedule.steps,PNat.mul_coe,Nat.cast_mul,mul_pow]
    exact congrArg (fun a:ℂ=>a • flow (C₀) 0 N p f n U) (mul_comm ..)

theorem gust_scalar (f n:ℕ)(F:space (f+n)→ℂ)(paid:Integrable F (prior G _))(z:ℂ):
    gust (C₀).path N p (f+n) (z • F) f (Nat.le_add_right f n)=
      z • gust (C₀).path N p (f+n) F f (Nat.le_add_right f n):=by
  rw [←WilsonReceivedQUnitPosterior.raw,←WilsonReceivedQUnitPosterior.raw]
  exact scalar R 0 f n F paid z

end YM.Integration.WilsonReflectedTrialEngineering
end
