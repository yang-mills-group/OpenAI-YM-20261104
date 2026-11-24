import YM.Integration.WilsonMeasuredSignedActionObserved
import YM.Integration.WilsonMeasuredSignedActionDirection
/-! Appoint the unturned physical action on a previously filed roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionEnrolled
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
    {T:Campaign R}(L:Pillars R T)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4


open WilsonMeasuredSignedActionPacket (Packet)
open WilsonMeasuredSignedActionRegistry (weak HeardAt)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (castField turned)
open WilsonReflectedPublicGuardedMotion


open WilsonMeasuredPublicEntranceMarkedQuadratics (marked)
open WilsonMeasuredPublicEntranceCommonColor (carried)
open WilsonMeasuredPublicEntranceFiniteFreeTests (Hearing heard)
open XSpace XSpace.Normalize XSpace.Stab
open WilsonPhysicalPositionAdmissible (Native)

def attach {n K:ℕ}{d:Fin n→ℕ}(E:Packet R d K)(i:Fin n)(four:d i=4)(Y:ℕ×ℕ→(C).label 4):Packet R d K:=
  {E with words:=fun z=>Function.update (E.words z) i (four.symm ▸ Y z)
          turns:=Function.update E.turns i (1,false)}

private theorem uncast {a:ℕ}(eqn:a=4)(x:(C).label 4):
    castField R eqn (eqn.symm ▸ x)=x:=by
  subst a
  rfl

theorem named {n K:ℕ}{d:Fin n→ℕ}(E:Packet R d K)(i:Fin n)(four:d i=4)(Y:ℕ×ℕ→(C).label 4)(z:ℕ×ℕ):
    castField R four ((attach R E i four Y).words z i)=Y z:=by
  change castField R four (Function.update (E.words z) i (four.symm ▸ Y z) i)=_
  rw [Function.update_self]
  exact uncast R four (Y z)

theorem plain {n K:ℕ}{d:Fin n→ℕ}(E:Packet R d K)(i:Fin n)(four:d i=4)(Y:ℕ×ℕ→(C).label 4):
    (attach R E i four Y).turns i=(1,false):=Function.update_self ..

def rows (family:Family G):Finset (Hearing (Fin ((Extra.FD.recorded family.labels 4).m+1))):=
  Classical.choose (WilsonMeasuredSignedActionHeard.tested family)

def heardAll (family:Family G)(A:Module.End ℂ ((Bel family.book).Field 4)):Prop:=
  let e:=(Extra.FD.recorded family.labels 4).b.map (fields family.labels 4)
  ∀h∈rows family,heard e (carried family A) h=0

theorem tested (family:Family G)(A:Module.End ℂ ((Bel family.book).Field 4))(native:Native family A)(heard:heardAll family A)
    (ray:∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,A (stepField family)=(s:ℂ) • stepField family+c • (Bel family.book).unit 4):
    A (stepField family)=stepField family ∧ carried family A (marked G (le_refl 4) 1)=marked G (le_refl 4) 1:=by
  have tested:=Classical.choose_spec (Classical.choose_spec (WilsonMeasuredSignedActionHeard.tested family))
  have head:=tested.2 A native heard ray
  refine ⟨head,?_⟩
  have moved:carried family A (fields family.labels 4 (stepField family))=fields family.labels 4 (stepField family):=by
    change fields family.labels 4 (A ((fields family.labels 4).symm (fields family.labels 4 (stepField family))))=_
    rw [LinearEquiv.symm_apply_apply,head]
  rw [←WilsonMeasuredSignedActionDirection.direct family,two_smul,map_add,moved]

end YM.Integration.WilsonMeasuredSignedActionEnrolled
end
