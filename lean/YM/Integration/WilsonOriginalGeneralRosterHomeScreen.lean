import YM.Integration.WilsonOriginalGeneralRosterUnionScreen
import YM.Integration.WilsonOriginalGeneralRosterHomePlacement

/-! The physical geometry and hearings of one row, at a reserve fixed jointly with all other rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeScreen
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Climb Maxwell Maxwell.Free Trace.Terrace GapsContact PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (threshold)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Fee)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker WilsonLimitConstruction PhysMS
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "P" => R.family.path.levels

open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonMeasuredPublicEntranceScreen (Ground)
variable {n:ℕ}(port:Fin n→I)
local notation "g" => (fun i:Fin n=>(d (port i)).val)

open WilsonOriginalGeneralRosterUnionScreen (Ready)

universe u
theorem original {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))(lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)(np:0<n)(φ:Test n)(tuition:ℝ)(request reserve power h t:ℕ):
    ∀ᶠ m:ℕ in atTop,∀u:ℕ,m≤u→∀ᶠr in trail,
    ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∃j:ℕ,u≤j ∧ j+2≤f ∧ ∀ scale : ℝ, r ≤ scale → scale ≤ outer z h r → Ready F books (d:=d) port tuition request reserve power t m j f φ scale ρ:=by
  classical
  letI:Nonempty (Fin n):=⟨⟨0,np⟩⟩
  have costs:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  obtain ⟨_,faculty⟩:=WilsonMeasuredPublicEntranceMasterUpper.original R simple costs.2.1 costs.2.2.2
    costs.2.2.1 bank lamp costs.1 paid
  obtain ⟨apron,place⟩:=WilsonOriginalGeneralRosterHomePlacement.original F simple bliss costs.2.1 d books φ h
  have size:Fintype.card (Fin n)≤n:=by simp
  let first:=threshold R simple costs.2.1 costs.2.2.2 costs.2.2.1 bank lamp costs.1
    (g) n apron request t reserve power (capital R D tuition) np size
  have pos:0≤capital R D tuition:=by unfold capital;positivity
  obtain ⟨ear,openEar⟩:=eventually_atTop.mp (open_late (C) simple 0)
  filter_upwards [faculty n D request,eventually_ge_atTop ear] with m classAt start
  intro u mu
  let floor:=max u first
  have stations:=WilsonAddressedMixedStationRange.original F simple bliss costs.2.1 D T h floor d books
  filter_upwards [place floor,stations] with r housed times
  intro ρ span near f
  obtain ⟨j,fj,height,support⟩:=housed ρ span near
  have uj:u≤j:=(le_max_left u first).trans fj
  have firstJ:first≤j:=(le_max_right u first).trans fj
  have jf:j≤f:=(Nat.le_add_right j 2).trans height
  let K:=berth R reserve f
  have fk:f≤K:=(WilsonInvariantActionPosition.arrival R reserve f).1.le
  refine ⟨j,uj,height,?_⟩
  intro scale lower upper
  refine ⟨jf,fun N per cut a=>(support scale lower upper N per (fk.trans cut) a).2,?_⟩
  intro branch N per cut road a A station loc v uv vj vf
  have mN:=mu.trans (uj.trans (jf.trans (road.trans cut)))
  obtain ⟨_,_,_,offer⟩:=classAt N mN
  have bill:=offer (Fin n) (g) np size (fun i=>Nat.le_of_lt_succ (d (port i)).isLt) apron request t reserve power
    (capital R D tuition) pos per
  have begin(i:Fin n):first≤A.slot i:=by
    rw [station]
    exact (le_max_right u first).trans ((times ρ span near).2 (port i) (branch i)).1
  have ground:WilsonMeasuredPublicEntranceScreen.Ground R N per j f apron A.loc:=by
    rw [loc]
    exact (support scale lower upper N per (road.trans cut) a).1
  exact bill j f K firstJ (mu.trans uj) height rfl road cut A begin (Or.inr ground) v uv vj
    (openEar v (start.trans uv) per) (openEar j (start.trans (mu.trans uj)) per)

end YM.Integration.WilsonOriginalGeneralRosterHomeScreen
end
