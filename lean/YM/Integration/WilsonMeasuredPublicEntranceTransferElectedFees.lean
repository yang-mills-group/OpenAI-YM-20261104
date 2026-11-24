import YM.Integration.WilsonPhysicalElectedSourceFare
import YM.Integration.WilsonMeasuredPublicEntranceTransferLocatedPanel
/-! The original restored N income and co-issued K income on the booked source, at its preassigned thermal readout. -/
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferElectedFees
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceCellWords (physical)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}

local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

universe u
open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log
open MS MS.Land FVA2 FVA2.Register Pert.Asymptotics
open WilsonThermometerUnitFilingFourPoolClock (outer)
variable (J:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonMeasuredPublicEntranceTransferLocatedPanel (cost)
open WilsonAddressedHomeDose (ceiling)

theorem original {n:ℕ}[Nonempty (Fin n)]{simple:G.Simple}{course:Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F course Q J H z l simple cohort)
    (slow:WilsonWindowReportingPace.Slow R.kit)(clock:Coupling G (WilsonPositionHomogeneousFrame.reading F J Z))
    (D T h:ℕ)(d:Fin n→Fin (D+1))(y:∀i,(Spin.comparator (C₀).book).Field (d i).val)
    (x:∀i,RG17.Free C₀ (d i).val){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (admit:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:Fin n→ℝ,∃E:Fin n→ℕ,(∀i,1≤A i) ∧ ∀p:ℕ,∀ᶠr in trail,
    ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∀(M:Fin n→ℝ)(_one:∀i,1≤M i)(q desired:ℕ),
    (∑i:↥(Stock.final (Fin n)).val,E i.val)+2*(2*p)≤q → 2*(2*p)≤desired →
    ∀(mode b:Fin n→Bool),let name:=fun i v=>WilsonReflectedMixedMasterSchool.field F J Z D T d y x books i (ρ i) (mode i) v
    cost F d books ρ f q desired M name b ≤
      ((∏i:↥(Stock.final (Fin n)).val,A i.val)+(∏i,ceiling (R:=R) (d i).val (M i)))*
        (WilsonPositionHomogeneousFrame.reading F J Z r)^p:=by
  classical
  obtain ⟨A,E,one,charged⟩:=WilsonPhysicalElectedSourceFare.original F J Z run slow clock D T h d y x books admit
  refine ⟨A,E,one,?_⟩
  intro p
  filter_upwards [charged p] with r offer
  intro ρ dates near f M own q desired cap rest mode b name
  have physical:=offer ρ dates near (n:=n) id (Stock.final (Fin n)) b mode q cap
  letI : IsEmpty (↥(Stock.final (Fin 0)).val):=⟨fun i=>Fin.elim0 i.val⟩
  have scalar:=offer ρ dates near (n:=0) Fin.elim0 (Stock.final (Fin 0)) (fun _=>false) (fun _=>false) desired (by simpa using rest)
  have heat: ((β f)^desired)⁻¹≤(WilsonPositionHomogeneousFrame.reading F J Z r)^p:=by simpa using scalar
  have nonnegative(i:Fin n):0≤ceiling (R:=R) (d i).val (M i):=
    le_trans (mul_nonneg (by norm_num) (zero_le_one.trans (own i))) (le_max_left ..)
  unfold WilsonMeasuredPublicEntranceTransferLocatedPanel.cost
  rw [add_mul]
  exact add_le_add physical (mul_le_mul_of_nonneg_left heat (Finset.prod_nonneg (fun i _=>nonnegative i)))

end YM.Integration.WilsonMeasuredPublicEntranceTransferElectedFees
end
