import YM.Integration.WilsonMovingForkReporterOwnVane
import YM.Integration.WilsonMovingForkReporterMeasuredRadii
import YM.Integration.WilsonMeasuredPublicEntranceNativeAppointment

/-! One measured chart at each original radius, its own full raw test bank, and
a compatible position frame on the same physical cutoff order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeSchool
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


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterPostedRanks (paid)
variable {G:Gauge} (R:Run G) (B:Binding R.family) (O:HaarBudget G) (χ:ChartRatio G)
    {f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy) {arch:Arch R.family}
    (price:ℕ→ℝ) (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family)
    (F:Final R.family f S) (J₀:ℝ→tower S)
local notation "C"=>R.family


open WilsonMovingForkReporterRankFilament (Kept)
variable (b:ℕ→Fin 3→ℝ) (c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
    {start:ℕ} {radius:ℝ} (station:Ioc (0:ℝ) radius→{k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ)


open WilsonMeasuredPublicEntranceNativeFrame WilsonMeasuredPublicEntranceNativeStaff
open PhysMS.Frame
open private dates from YM.Integration.WilsonMovingForkReporterMeasuredRadii

def lift {δ:ℝ}(sub:δ≤radius)(s:Ioc (0:ℝ) δ):Ioc (0:ℝ) radius:=
  ⟨s.val,s.property.1,s.property.2.trans sub⟩

def home {δ:ℝ}(sub:δ≤radius)(X:∀s:Ioc (0:ℝ) δ,ℕ→ℕ→TableL R.family (grade (station (lift sub s))))
    (s:Ioc (0:ℝ) δ):Vane R.family (grade (station (lift sub s))):=
  let k:=station (lift sub s)
  WilsonMovingForkReporterOriginalCouncil.reporters R (grade k) k (b (grade k) 0) (c (grade k)) (X s) (offset (lift sub s))

theorem original (lead:Leading F J₀)(simple:G.Simple)(bliss:Bliss F l arch H)(rp:0<radius)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels
      (b (grade (station s)) 0+offset s) (station s))
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)):
    ∃(δ:ℝ)(_positive:0<δ)(sub:δ≤radius)
      (X:∀s:Ioc (0:ℝ) δ,ℕ→ℕ→TableL R.family (grade (station (lift sub s)))),
      let cap:=fun s=>grade (station (lift sub s))
      let V:=home R b c grade station offset sub X
      (∀s,let pan:=P (cap s) (offset (lift sub s)) 0
          Named (f:=f) R B O χ H price count tests pan (V s) ∧
          ∀h,∀w:h≤cap s,WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan
            (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      ∃J:ℝ→tower S,Leading F J ∧ localCost trail (atRadius l cap V J₀) J ∧
        (∀d,∀ᶠr in trail,obedient F H (J r) d) ∧
        ∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap V J₀ r) (J r) m:=by
  obtain ⟨Z,paid⟩:=WilsonMovingForkReporterOwnVane.original R B O χ H price count tests
    b c P grade station offset issued legal finance
  obtain ⟨e,ep,onset⟩:=large 1
  let δ:=min radius (e/2)
  have pos:0<δ:=lt_min rp (half_pos ep)
  have sub:δ≤radius:=min_le_left .. 
  have allowed(s:Ioc (0:ℝ) δ):1≤grade (station (lift sub s)):=onset _
    (s.property.2.trans_lt ((min_le_right radius (e/2)).trans_lt (half_lt_self ep)))
  let X(s:Ioc (0:ℝ) δ):=Z ⟨lift sub s,allowed s⟩ (station (lift sub s))
  let cap(s:Ioc (0:ℝ) δ):=grade (station (lift sub s))
  let V:=home R b c grade station offset sub X
  have named(s:Ioc (0:ℝ) δ):=paid ⟨lift sub s,allowed s⟩
  refine ⟨δ,pos,sub,X,fun s=>named s,?_⟩
  have place (s:Ioc (0:ℝ) δ):(V s).wheel.r=s.val:=(located (lift sub s)).symm
  have calendar(xs:ℕ→Ioc (0:ℝ) δ)(vanish:Tendsto (fun i=>(xs i).val) atTop (𝓝 0)):
      Tendsto (fun i=>cap (xs i)) atTop atTop ∧ Tendsto (fun i=>(V (xs i)).k) atTop atTop:=
    dates grade station (fun i=>lift sub (xs i)) vanish large
  obtain ⟨J,good,cost,all⟩:=WilsonMeasuredPublicEntranceNativeAppointment.original
    F J₀ cap V lead R.makes simple bliss pos place (fun s=>(named s).1.choose) calendar
  exact ⟨J,good,cost,fun d=>(all d).mono fun _ read=>read.1.spins (Fin.last d),all⟩

end YM.Integration.WilsonMeasuredPublicEntranceNativeSchool
end
