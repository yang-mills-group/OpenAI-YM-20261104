import YM.Integration.WilsonPhysicalStationSelectedLower
import YM.Integration.WilsonPhysicalStationReferenceSalary
import YM.Integration.WilsonPhysicalStationDetectorCurrency
import YM.Integration.WilsonPhysicalStationLowerImage

/-! On the original ordered regulator filter, the same uniquely filed lower
source used by every reflected detector has strictly lower physical grade. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCofinalLower
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationDatedSalary (span datedMass)
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h   <   D+1) (db:h   <   D'+1)
local notation "a₀" => (⟨h,da⟩:Fin (D+1))
local notation "b₀" => (⟨h,db⟩:Fin (D'+1))
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "μ" => (F₀).coeffSize
local notation "P₀" => Columns.low (F₀) e
local notation "K₀" => R.family.factory h N p
local notation "C₀" => ((L₀).params A.k).columns
local notation "C₁" => ((L₀).params B.k).columns
local notation "δ₀" => barunit (R.family.S.block A.k)
local notation "D₀" => (F₀).scaled (ratio R A.k)

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


local notation "t₀" => (shrink R.family A.k N p)⁻¹
local notation "t₁" => (shrink R.family B.k N p)⁻¹




open Function Filter RG Wilson Labels Source Lattice OPE Next.Extract
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open scoped Classical Topology
open Push.RelayDifference
open WilsonPhysicalStationSelectedLower (Receipt)
include L fac in
theorem original (F:Spec.Final R.family f S) (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (next:(C₁)*err R B.k ≤ 1/2)
    (a:(F₀).Index)(weight:((F₀).grades a).1=h) {b:Filter Cutoffs}[b.NeBot]
    (ordered:b ≤ f.fuse) (late:∀ᶠ i:Cutoffs in b,B.k < i.1):
    ∃ w:Cutoffs→R.family.label h,
      (∀ i:Cutoffs,∀ t:B.k < i.1,Receipt R A B h e da db (p:=i.2) ca cb t a (w i)) ∧
      ∃ l:Filter Cutoffs,l ≤ b ∧ l.NeBot ∧ ∃ v:R.family.label h,
       Tendsto (fun i:Cutoffs=>(R.family.factory h i.1 i.2).terminal (w i)) l (𝓝 v) ∧
        S.project h v∈LinearMap.range (F.sector.derivatives.rise (show e ≤ h by omega)):=by
  classical
  have chooseW (i:Cutoffs)(t:B.k < i.1):=WilsonPhysicalStationSelectedLower.original R L fac A B h e da db
    (p:=i.2) hg ca cb dates t horizon gate next a weight
  let w (i:Cutoffs):R.family.label h:=if t:B.k < i.1 then (chooseW i t).exists.choose else 0
  have captured (i:Cutoffs)(t:B.k < i.1):Receipt R A B h e da db (p:=i.2) ca cb t a (w i):=by
    rw [show w i=(chooseW i t).exists.choose by simp [w,t]]
    exact (chooseW i t).exists.choose_spec
  refine ⟨w,captured,WilsonPhysicalStationLowerImage.bounded R F fac h e (by omega) w ordered ?_
    (WilsonPhysicalStationUniformLower.allowance R A.k B.k h ((F₀).grades a).2 (M₀) (M₁)) ?_⟩
  · filter_upwards [late] with i t
    exact (captured i t).lower
  · filter_upwards [late] with i t
    exact (captured i t).reference

end YM.Integration.WilsonPhysicalStationCofinalLower
end
