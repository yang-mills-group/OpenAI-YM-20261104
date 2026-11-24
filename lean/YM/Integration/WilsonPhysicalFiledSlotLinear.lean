import YM.Integration.WilsonPhysicalElementaryMasterHearing

/-! Linearity of the deposited original page and of the uncut fitted trial at its
own physical site. The measured page includes the entire regular angular sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalFiledSlotLinear
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow RG16 RG16.Literal
open Climb OPE Overlay Bid Push.GridApprox RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut names)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

private theorem coefficient {C₁:Family G}(makes:C₁.Makes)(d N per j:ℕ)(eligible:C₁.ref d≤j)(live:j≤N):
    IsLinearMap ℂ (fun v:C₁.label d=>GermGraph.page d per j ((C₁.factory d N per).entries j v)):=by
  have hv:(C₁.path.rep N per j).p=plank C₁ j:=(makes.wilson.represents N per j live).vac
  have hs:=dimensions d N per j makes eligible live
  have hq (v):=entryOk d N per j makes eligible live v
  have ht:=(makes.calibrated d N per (eligible.trans live)).linear j eligible live
  simpa only [GermGraph.page,←hv] using Germ.linear_projection (C₁.labels.level d) C₁.params
    (R:=C₁.path.rep N per j) (o:=0) ((C₁.factory d N per).entries j) hs.1 hs.2
    (fun v=>(hq v).1) (fun v=>⟨_,_,(hq v).2⟩) ⟨ht.1,ht.2.1⟩

theorem entry (d N per j:ℕ)(eligible:(C).ref d≤j)(live:j≤N):
    IsLinearMap ℂ (fun v:(C).label d=>GermGraph.page d per j (((C).factory d N per).entries j v)):=coefficient (C₁:=R.family) R.makes d N per j eligible live

def measured (d N per j:ℕ)(eligible:(C).ref d≤j)(live:j≤N):(C).label d→ₗ[ℂ](C).label d:=
  ((entry R d N per j eligible live).mk' _).comp ((C).factory d N per).terminal.symm.toLinearMap

theorem deposited (d N per j:ℕ)(eligible:(C).ref d≤j)(live:j≤N)(v:(C).label d):
    measured R d N per j eligible live v=fitted R d j N per v:=rfl

def word (d N per K:ℕ)(o:Site ((C).side K per))(U:Config G ((C).side K per)):
    (C).label d→ₗ[ℂ]ℂ where
  toFun v:=uncut R d N per K o v U
  map_add' v w:=by
    simp only [uncut,WilsonPositionProgramBlockedTrialAddBack.names,map_add,Pi.add_apply,SectionData.places,SectionData.evaluate]
    ring
  map_smul' t v:=by
    simp only [uncut,WilsonPositionProgramBlockedTrialAddBack.names,map_smul,Pi.smul_apply,SectionData.places,SectionData.evaluate,smul_eq_mul,RingHom.id_apply]
    ring

theorem fitted_sum {I:Type}[Fintype I](d N per j:ℕ)(eligible:(C).ref d≤j)(live:j≤N)
    (v:I→(C).label d)(α:I→ℂ):
    fitted R d j N per (∑i,α i • v i)=∑i,α i • fitted R d j N per (v i):=by
  simp only [←deposited R d N per j eligible live,map_sum,map_smul]

end YM.Integration.WilsonPhysicalFiledSlotLinear
