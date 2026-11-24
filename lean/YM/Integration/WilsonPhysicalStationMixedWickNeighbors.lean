import YM.Integration.WilsonPhysicalStationOwnedTablePair
import YM.Integration.WilsonMovingForkReporterMixedHouses
/-! The two selected Wilson reporters inherit their actually subscribed mixed panels. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickNeighbors
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent


open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterBasisVisits (Seen)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonMovingForkReporterRestriction (vane)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open WilsonPhysicalStationOwnedTableFaculty (Faculty)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
    (fac:Facilities R.family f S)(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
    (J₀:ℝ→tower S)(H:(Bel R.family.book).Hierarchy){arch:Arch R.family}
    (B:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
variable (number:ℕ→ℕ)(tests:∀d,Fin (number d)→Axes R.family)
    {radius:ℝ}(cap:Ioc (0:ℝ) radius→ℕ)(V:∀s,Vane R.family (cap s))
    (pan:∀s,Tapes.Panel (cap s))(outer inner:ℕ→Ioc (0:ℝ) radius)
open WilsonMovingForkReporterMixedBasis (Slot)
variable (qty:ℕ→ℕ)(menu:∀d,Fin (qty d)→Slot R.family)

def month (side:Bool)(i:ℕ):ℕ:=if side then 2*i+1 else 2*i
def venue {Y:Type*}(o u:ℕ→Y)(pick:ℕ→ℕ)(side:Bool)(i:ℕ):Y:=
  if side then u (pick i) else o (pick i)

theorem date (grade k:ℕ→ℕ)(deep:Tendsto (fun i=>grade (k i)) atTop atTop):Tendsto k atTop atTop:=by
  apply tendsto_atTop.2
  intro n
  let limit:=∑j∈Finset.range n,grade j
  filter_upwards [deep.eventually_gt_atTop limit] with i newer
  by_contra! small
  have bounded:grade (k i)≤limit:=Finset.single_le_sum (fun j _=>Nat.zero_le (grade j)) (Finset.mem_range.mpr small)
  exact (not_lt_of_ge bounded) newer

variable (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))(J:Scaling S)

def Admitted :Prop:=
  ∀side:Bool,
    let z:=venue outer inner c.pick side
    (∀i,WilsonMovingForkReporterMixedHouses.Held (f:=f) R B O χ H price qty menu (pan (z i)) (c.report (month side i))) ∧
    Tendsto (fun i=>(c.report (month side i)).k) atTop atTop ∧
    Tendsto (month side) atTop atTop ∧ Tendsto (fun i=>cap (z i)) atTop atTop ∧
    ∀d,∃M C:ℝ,1≤M ∧ 0≤C ∧ ∀ᶠi:ℕ in atTop,Filed (f:=f) (l:=l) J₀ J c.report d (month side i) M C

theorem original (grade:ℕ→ℕ)(chart:∀s,grade (V s).k=cap s)
    (mixed:∀s h,∀w:h≤cap s,WilsonMovingForkReporterMixedHouses.Held (f:=f) R B O χ H price qty menu
      (pan s) (vane w (V s)))
    (registered:WilsonPhysicalStationOwnedTablePair.Held R F (l:=l) J₀ H (arch:=arch) number tests cap V outer inner c J):
    Admitted R (f:=f) (l:=l) J₀ H B O χ price cap V pan outer inner qty menu c J:=by
  intro side
  let z:=venue outer inner c.pick side
  have months:Tendsto (month side) atTop atTop:=tendsto_atTop.2 fun n=>(eventually_ge_atTop n).mono fun i ge=>by
    cases side with
    | false=>change n≤2*i; omega
    | true=>change n≤2*i+1; omega
  have height (i:ℕ):month side i≤cap (z i):=by
    cases side with
    | false=>exact c.outer i
    | true=>exact c.inner i
  have stages:Tendsto (fun i=>cap (z i)) atTop atTop:=tendsto_atTop.2 fun n=>
    (months.eventually_ge_atTop n).mono fun i ge=>ge.trans (height i)
  have exactDate (i:ℕ):grade (c.report (month side i)).k=cap (z i):=by
    cases side with
    | false=>rw [show month false i=2*i from rfl,even];exact chart _
    | true=>rw [show month true i=2*i+1 from rfl,odd];exact chart _
  refine ⟨?_,date grade _ (stages.congr fun i=>(exactDate i).symm),months,stages,?_⟩
  · intro i
    cases side with
    | false=>rw [show month false i=2*i from rfl,even];exact mixed _ _ (c.outer i)
    | true=>rw [show month true i=2*i+1 from rfl,odd];exact mixed _ _ (c.inner i)
  · intro d
    obtain ⟨M,C,hM,hC,onFile⟩:=registered.2.2.2.1 d
    refine ⟨M,C,hM,hC,?_⟩
    cases side with
    | false=>exact onFile.mono fun _ both=>both.1
    | true=>exact onFile.mono fun _ both=>both.2

end YM.Integration.WilsonPhysicalStationMixedWickNeighbors
end
