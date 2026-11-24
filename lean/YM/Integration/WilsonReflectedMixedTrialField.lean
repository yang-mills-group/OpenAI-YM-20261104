import YM.Integration.WilsonReflectedMixedTrialMap
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedTrialField
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

/-- Reflection and complex superposition of an actual K-born clover at its
one original pin, including the very same all-field failed-support mask. -/
theorem field {ι:Type}[Fintype ι]{d f K N p:ℕ}(up:f≤K)(B:Arm R d N p f K)
    (row:ι→Arm R d N p f K)(c:ι→ℂ)(sites:∀i,(row i).o=B.o)
    (turns:∀i,((row i).s,(row i).b)=(B.s,B.b))(sum:B.w=∑i,c i•(row i).w)
    (U:Config G ((C).side K p)):
    cropped R B up U=∑i,Motion.scalar (B.s,B.b) (c i)*cropped R (row i) up U:=by
  have combined:coords R B=∑i,Motion.scalar (B.s,B.b) (c i)•coords R (row i):=by
    simp only [coords,turns]
    exact WilsonReflectedMixedTrialMap.turned R (B.s,B.b) c sum
  rw [WilsonReflectedPublicGuardedMotion.placed R B up U,combined,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [WilsonReflectedPublicGuardedMotion.placed R (row i) up U,sites i,map_smul]
  simp only [smul_eq_mul]
  ring

/-- Recover the preceding field identity from the measured original inputs,
allowing a different previously funded single-column calibration for each. -/
theorem original {ι:Type}[Fintype ι]{d j f K N p current order:ℕ}{before:j≤K}{up:f≤K}{live:K≤N}
    (admit:Opened C d j p){η η':ℝ}{F A:(C).label d≃ₗ[ℂ](C).label d}
    (paid:∀x,Arrived R d j K N p current before live η F x)
    (c:ι→ℂ)(Y:ι→(C).label d)(old:ι→(C).label d≃ₗ[ℂ](C).label d)
    {orders:ι→ℕ}{widths:ι→ℝ}
    (income:∀i,Arrived R d j K N p (orders i) before live (widths i) (old i) (fitted R d j N p (Y i)))
    (total:Arrived R d j K N p order before live η' A (fitted R d j N p (∑i,c i•Y i)))
    (B:Arm R d N p f K)(row:ι→Arm R d N p f K)(sites:∀i,(row i).o=B.o)
    (turns:∀i,((row i).s,(row i).b)=(B.s,B.b))
    (columns:∀i,(row i).w=(old i).symm (fitted R d j N p (Y i)))
    (fit:B.w=A.symm (fitted R d j N p (∑i,c i•Y i)))(U:Config G ((C).side K p)):
    cropped R B up U=∑i,Motion.scalar (B.s,B.b) (c i)*cropped R (row i) up U:=by
  apply field R up B row c sites turns _ U
  simp only [fit,columns]
  exact WilsonReflectedMixedTrialMap.original R admit paid c Y old income total

end YM.Integration.WilsonReflectedMixedTrialField
end
