import YM.Integration.WilsonPhysicalStationCoincidentLower
import YM.Integration.WilsonPhysicalStationCofinalBasis
import YM.Integration.WilsonPhysicalStationKineticLimit
import YM.Integration.WilsonPhysicalStationReferenceSalary
import YM.Integration.WilsonPhysicalStationDetectorCurrency
import YM.Integration.WilsonPhysicalStationLowerImage

/-! On the original ordered regulator filter, the same uniquely filed lower
source used by every reflected detector has strictly lower physical grade. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentBasis
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
open WilsonPhysicalStationCoincidentLower (Receipt)

open WilsonPhysicalStationKineticLimit (transit)
include fac in
theorem original {I:Type*}[Fintype I](F:Spec.Final R.family f S)
    (ca:A.checked f H D)(cb:B.checked f H D')(dates:B.k=A.k)(horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (next:(C₁)*err R B.k ≤ 1/2)
    (a:I→(F₀).Index)(weight:∀j,((F₀).grades (a j)).1=h) {b:Filter Cutoffs}[b.NeBot]
    (ordered:b ≤ f.fuse) (late:∀ᶠ i:Cutoffs in b,B.k < i.1):
    ∃ w:I→Cutoffs→R.family.label h,
     (∀j i,∀ t:B.k < i.1,Receipt R A B h e da db (p:=i.2) ca cb t (a j) (w j i)) ∧
     ∃ l:Filter Cutoffs,l ≤ b ∧ l.NeBot ∧
       ∃ v:I→R.family.label h, ∀j,
        Tendsto (fun i:Cutoffs=>(R.family.factory h i.1 i.2).terminal (w j i)) l (𝓝 (v j)) ∧
         S.project h (v j)∈LinearMap.range (F.sector.derivatives.rise (show e ≤ h by omega)):=by
  classical
  have issue (j:I)(i:Cutoffs)(t:B.k < i.1):= (WilsonPhysicalStationCoincidentLower.original R fac A B h e da db (p:=i.2) ca cb dates t horizon gate next (a j) (weight j)).exists
  let w (j:I)(i:Cutoffs):R.family.label h:=if t:B.k < i.1 then (issue j i t).choose else 0
  have faces (j:I)(i:Cutoffs)(t:B.k < i.1):
      Receipt R A B h e da db (p:=i.2) ca cb t (a j) (w j i):=by
    simpa only [w,dif_pos t] using (issue j i t).choose_spec
  let val (i:Cutoffs)(j:I):R.family.label h:=(R.family.factory h i.1 i.2).terminal (w j i)
  let fee (j:I):ℝ:=WilsonPhysicalStationCoincidentLower.allowance R A.k B.k h ((F₀).grades (a j)).2 (M₀) (M₁)
  let reserve:ℝ:=∑j,|fee j|
  have cap:∀ᶠ i in b,‖val i‖ ≤ reserve:=by
    filter_upwards [late] with i t
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _=>abs_nonneg (fee j)))).2
    intro j
    exact (faces j i t).reference.trans ((le_abs_self (fee j)).trans
      (Finset.single_le_sum (f:=fun j=>|fee j|) (fun j _=>abs_nonneg _) (Finset.mem_univ j)))
  obtain ⟨u,ub,active,v,arrived⟩:=finite_extract (𝓛:=b) val reserve cap
  letI:=active
  refine ⟨w,faces,u,ub,active,v,?_⟩
  intro j
  have converges:Tendsto (fun i:Cutoffs=>(R.family.factory h i.1 i.2).terminal (w j i)) u (𝓝 (v j)):=tendsto_pi_nhds.mp arrived j
  refine ⟨converges,WilsonPhysicalStationLowerImage.original R F fac h e (by omega) (w j)
     (ub.trans ordered) ?_ (v j) converges⟩
  filter_upwards [late.filter_mono ub] with i t
  exact (faces j i t).lower
end YM.Integration.WilsonPhysicalStationCoincidentBasis
end
