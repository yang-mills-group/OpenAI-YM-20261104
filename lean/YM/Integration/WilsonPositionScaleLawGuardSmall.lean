import YM.Integration.WilsonPositionScaleLawGuardEveryUnit
import YM.Integration.WilsonPositionProgramTrialPublicJointFourHorizons

/-! All original fields below weight four enjoy the exact scale equality simultaneously, on all positive short ratios. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardSmall
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawGuardInvoice (issue)
open WilsonPositionScaleLawDressedTransport (guard dressed)
open WilsonPositionScaleLawKinetic (kinetic)
open Pert.RawLabels (physicalLabel enroll physical_round physical_unit)
open scoped Topology Classical Asymptotics
variable {G:Gauge}

theorem scalar (C:Family G)(simple:G.Simple){d:ℕ}(small:d<4)(v:(Bel C.book).Field d):∃s:ℂ,v=s • (Bel C.book).unit d:=by
  obtain ⟨s,read⟩:=WilsonPositionProgramTrialPublicJointFourHorizons.scalar (C.labels.level d) simple small (physicalLabel C.labels d v)
  refine ⟨s,?_⟩
  calc
    v=enroll C.labels d (physicalLabel C.labels d v):=(physical_round C.labels v).symm
    _=enroll C.labels d (s • Labels.unit G d):=congrArg (enroll C.labels d) read
    _=_:=by rw [map_smul,←physical_unit C.labels d,physical_round]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "unit"=> (Bel R.family.book).unit

include H in
theorem original (lead:Leading F J){d:ℕ}(small:d<4):∀ᶠr in trail,∀t:ℝ,∀ht:0<t,t≤1→∀q:ℕ,
    change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t ht=
      issue R.family q (guard Z M ν (-Real.log t) d) (kinetic Z F J r:ℂ):=by
  filter_upwards [WilsonPositionScaleLawGuardEveryUnit.original F J Z M H ν lead d] with r hit t ht short q
  ext v
  obtain ⟨s,rfl⟩:=scalar R.family hG small v
  rw [map_smul,map_smul,hit t ht short q]

include H in
theorem half (lead:Leading F J){d:ℕ}(small:d<4)(q:ℕ):WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q:=by
  let X:=(Bel R.family.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter WilsonPositionScaleLawHome.Ratio))).eventually (original F J Z M H ν lead small)] with z hit
  have eq:dressed Z F J d z.1 z.2=WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d q z.1 z.2:=hit z.2.val (WilsonPositionScaleLawNative.positive z.2) z.2.property.2 q
  rw [eq,sub_self,norm_zero]
  exact mul_nonneg hε.le (norm_nonneg _)

end YM.Integration.WilsonPositionScaleLawGuardSmall
