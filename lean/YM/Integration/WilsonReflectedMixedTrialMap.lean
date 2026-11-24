import YM.Integration.WilsonReflectedMixedSharpReplay
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedTrialMap
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


/-- The actual linear map on original cutoff labels on a fixed finite side. -/
def trialMap {d j N p:ℕ}(admit:Opened C d j p)(live:j≤N)
    (A:(C).label d≃ₗ[ℂ](C).label d):(C).label d≃ₗ[ℂ](C).label d:=
  (((C).factory d N p).terminal.symm.trans (fitting d N p j R.makes admit live)).trans A.symm

theorem read {d j N p:ℕ}(admit:Opened C d j p)(live:j≤N)
    (A:(C).label d≃ₗ[ℂ](C).label d)(Y:(C).label d):
    trialMap R admit live A Y=A.symm (fitted R d j N p Y):=rfl

/-- Arbitrary signed complex coefficients act on the true pre-existing inverse
columns on the one finite history. The aggregate may have an independently
issued physical calibration. -/
theorem original {ι:Type}[Fintype ι]{d j K N p target group:ℕ}{before:j≤K}{top:K≤N}
    (admit:Opened C d j p){η η':ℝ}{F A:(C).label d≃ₗ[ℂ](C).label d}
    (current:∀x,Arrived R d j K N p target before top η F x)
    (c:ι→ℂ)(Y:ι→(C).label d)(B:ι→(C).label d≃ₗ[ℂ](C).label d)
    {orders:ι→ℕ}{widths:ι→ℝ}
    (income:∀i,Arrived R d j K N p (orders i) before top (widths i) (B i) (fitted R d j N p (Y i)))
    (total:Arrived R d j K N p group before top η' A (fitted R d j N p (∑i,c i•Y i))):
    A.symm (fitted R d j N p (∑i,c i•Y i))=∑i,c i•(B i).symm (fitted R d j N p (Y i)):=by
  let P:=trialMap R admit (before.trans top) F
  rw [WilsonReflectedMixedIntrinsicAxis.original R admit.post before top total current]
  change P (∑i,c i•Y i)=_
  rw [map_sum];simp only [map_smul]
  apply sum_congr rfl
  intro i _
  change c i•F.symm (fitted R d j N p (Y i))=_
  rw [WilsonReflectedMixedIntrinsicAxis.original R admit.post before top (income i) current]

/-- The reflected branch conjugates precisely the numerical scalar of each
column on the actual physical receiving orientation. -/
theorem turned {ι:Type}[Fintype ι]{d:ℕ}(m:Motion){w:(C).label d}{v:ι→(C).label d}
    (c:ι→ℂ)(joined:w=∑i,c i•v i):
    Motion.patch ((C).labels.level d) m w=∑i,Motion.scalar m (c i)•Motion.patch ((C).labels.level d) m (v i):=by
  rw [joined,Motion.patch_sum]
  simp_rw [Motion.patch_smul]

end YM.Integration.WilsonReflectedMixedTrialMap
end
