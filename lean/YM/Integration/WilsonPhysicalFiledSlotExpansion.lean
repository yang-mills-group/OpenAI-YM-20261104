import YM.Integration.WilsonPhysicalFiledSlotLinear
import YM.Integration.WilsonPhysicalActualMixedFaces

/-! Preserve the same original fitted inverse before the oriented K-word is
evaluated on the actual field. The pooled source is kept as its own paid vector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalFiledSlotExpansion
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow RG16 RG16.Literal
open Climb OPE Overlay Bid Push.GridApprox RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonPhysicalFiledSlotLinear (word fitted_sum)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalActualMixedMenus (Port name weight source)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

def reading (d j N per K:ℕ)(A:(C).label d≃ₗ[ℂ](C).label d)(turn:Motion)
    (o:Site ((C).side K per))(U:Config G ((C).side K per))(v:(C).label d):ℂ:=
  uncut R d N per K o ((((C).S.a K:ℂ)^d)⁻¹ • Motion.patch ((C).labels.level d) turn
    (A.symm (fitted R d j N per v))) U

theorem linear {I:Type}[Fintype I](d j N per K:ℕ)(eligible:(C).ref d≤j)(live:j≤N)
    (A:(C).label d≃ₗ[ℂ](C).label d)(turn:Motion)(o:Site ((C).side K per))(U:Config G ((C).side K per))
    (v:I→(C).label d)(α:I→ℂ):
    reading R d j N per K A turn o U (∑i,α i • v i)=
      ∑i,Motion.scalar turn (α i)*reading R d j N per K A turn o U (v i):=by
  have base:=fitted_sum R d N per j eligible live v α
  let inc:=fun i=>Motion.patch ((C).labels.level d) turn (A.symm (fitted R d j N per (v i)))
  let cash:=(((C).S.a K:ℂ)^d)⁻¹
  have sum:Motion.patch ((C).labels.level d) turn (A.symm (fitted R d j N per (∑i,α i • v i)))=
      ∑i,Motion.scalar turn (α i) • inc i:=by
    rw [base,map_sum,Motion.patch_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,Motion.patch_smul]
  let lamp:=word R d N per K o U
  change lamp (cash • Motion.patch _ turn (A.symm (fitted R d j N per (∑i,α i • v i))))=
    ∑i,Motion.scalar turn (α i)*lamp (cash • inc i)
  rw [sum,Finset.smul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm cash,map_smul]
  rfl

variable {f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}

theorem original {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(v:(Bel R.family.book).Field d)
    (weak:Bool)(j N per K:ℕ)(eligible:(C).ref d≤j)(live:j≤N)
    (A:(C).label d≃ₗ[ℂ](C).label d)(turn:Motion)(o:Site ((C).side K per))(U:Config G ((C).side K per)):
    reading R d j N per K A turn o U (name F J Z d B v weak N per)=
      ∑e:Port R d weak,Motion.scalar turn (weight F J Z d B v weak e)*
        reading R d j N per K A turn o U (source F J Z d B v weak e N per):=by
  cases weak
  · simp [Port,source,WilsonPhysicalActualMixedMenus.weight,Motion.scalar]
  · change reading R d j N per K A turn o U (WilsonPhysicalActualWeakNames.name F J Z d B v N per)=_
    rw [←WilsonPhysicalActualWeakNames.entered F J Z d B v N per]
    exact linear R d j N per K eligible live A turn o U _ _

end YM.Integration.WilsonPhysicalFiledSlotExpansion
