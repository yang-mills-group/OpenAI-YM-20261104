import YM.Integration.WilsonReflectedMixedTrialField
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedCutoffField
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta


open WilsonReflectedMixedThermalArms

open Filter Trace.Physical.GermGraph
open scoped Topology



open WilsonReflectedPublicGuardedMotion (coords)
open WilsonReflectedFundedHearing (Arm cropped)


/-- The genuinely submitted uncut microscopic observable, evaluated at the
same link configuration and original translated source pin. -/
theorem physical {ι:Type}[Fintype ι]{d:ℕ}(N p:ℕ)(o:Site ((C).side N p))(U:Config G ((C).side N p))
    (c:ι→ℂ)(Y:ι→(C).label d):
    (C).O N p (∑i,c i•Y i) o U=∑i,c i*((C).O N p (Y i) o U):=by
  let wages:=((C).localSection d).eval_linear.mk' _
  let chart:=((C).labels.level d).scaled ((C).path.levels.clock.threshold N)⁻¹
  let file:=((C).factory d N p).terminal.symm
  let price:=(((C).S.a N:ℂ)^d)⁻¹
  change price*(wages (chart (file (∑i,c i•Y i)))) (expandAt o U)=
    ∑i,c i*(price*(wages (chart (file (Y i)))) (expandAt o U))
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end YM.Integration.WilsonReflectedMixedCutoffField
end
