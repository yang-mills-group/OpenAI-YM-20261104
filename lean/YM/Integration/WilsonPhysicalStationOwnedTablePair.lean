import YM.Integration.WilsonPhysicalStationOwnedTableFaculty
import YM.Integration.WilsonMeasuredPublicEntranceNativeProgram
/-! Signed measurements on the actual pair drawn from an earlier filed Vane at each radius. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedTablePair
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
def Held (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))(J:Scaling S):Prop:=
  Scribe f J c.report arch F.sector l F.room.kernel H ∧
  (∀i,J.r (2*i)=(outer (c.pick i):ℝ) ∧ J.r (2*i+1)=(inner (c.pick i):ℝ)) ∧
  (∀d,∀ᶠ i:ℕ in atTop,
    atRadius l cap V J₀ (outer (c.pick i)) d=J.U (2*i) d ∧ atRadius l cap V J₀ (inner (c.pick i)) d=J.U (2*i+1) d) ∧
  (∀d,∃A B':ℝ,1≤A ∧ 0≤B' ∧ ∀ᶠi:ℕ in atTop,
    Filed (f:=f) (l:=l) J₀ J c.report d (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J c.report d (2*i+1) A B') ∧
  ∀e:ℕ,Faculty R (l:=l) H number tests F J₀ c.report J (h:=e+1) (e:=e) rfl

include L fac in
theorem original (lead:Leading F J₀)(simple:G.Simple)(bliss:Bliss F l arch H)(below:(l:Filter _) ≤ f.fuse)
    (house:∀ᶠk:ℕ in atTop,MergeProof.East.topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k)
    (located:∀s,(V s).wheel.r=(s:ℝ))
    (clock:∀ xs:ℕ→Ioc (0:ℝ) radius,Tendsto (fun i=>(xs i:ℝ)) atTop (𝓝 0)→
      Tendsto (fun i=>cap (xs i)) atTop atTop ∧ Tendsto (fun i=>(V (xs i)).k) atTop atTop)
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ) ≤ u→(u:ℝ) ≤ 2*(s:ℝ)→
      (V u).k ≤ (V s).k ∧ (V s).k ≤ (V u).k+1)
    (named:∀s,Named (f:=f) R B O χ H price number tests (pan s) (V s) ∧
      ∀h,∀w:h≤cap s,Seen (f:=f) R B O χ H price number tests (pan s) (vane w (V s)))
    (fall:Tendsto (fun i=>(outer i:ℝ)) atTop (𝓝 0))(fall':Tendsto (fun i=>(inner i:ℝ)) atTop (𝓝 0))
    (apart:∀ᶠi:ℕ in atTop,(inner i:ℝ)<(outer i:ℝ))(comparable:∀i,(outer i:ℝ) ≤ 2*(inner i:ℝ)):
    ∃c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)),∃J:Scaling S,
      Held R F (l:=l) J₀ H (arch:=arch) number tests cap V outer inner c J:=by
  obtain ⟨higher,age⟩:=clock outer fall
  obtain ⟨lower,_⟩:=clock inner fall'
  obtain ⟨c,J,scribe,places,ident,files⟩:=WilsonMeasuredPublicEntranceNativeProgram.original
    F J₀ cap V outer inner lead R.makes simple bliss higher lower (by simpa only [located] using fall)
    (by simpa only [located] using fall') (by simpa only [located] using apart) age (clock inner fall').2
    (fun i=>(named (outer i)).1.choose) (fun i=>(named (inner i)).1.choose)
  refine ⟨c,J,scribe,fun i=>by simpa only [located] using places i,ident,files,?_⟩
  have deep:=higher.comp c.cofinal.tendsto_atTop
  have late:Tendsto (fun i=>(c.report (2*i)).k) atTop atTop:=by
    apply (age.comp c.cofinal.tendsto_atTop).congr
    intro i
    rw [even]
    rfl
  have earlier(i:ℕ): (inner (c.pick i):ℝ)<(outer (c.pick i):ℝ):=by
    simpa only [located] using c.separate i
  have dates(i:ℕ):(c.report (2*i+1)).k=(c.report (2*i)).k ∨ (c.report (2*i+1)).k=(c.report (2*i)).k+1:=by
    rw [even,odd]
    change (V (inner (c.pick i))).k=_ ∨ (V (inner (c.pick i))).k=_
    have same:=adjacent (inner (c.pick i)) (outer (c.pick i)) (earlier i).le (comparable _)
    change (V (inner (c.pick i))).k=(V (outer (c.pick i))).k ∨
      (V (inner (c.pick i))).k=(V (outer (c.pick i))).k+1
    omega
  have window(i:ℕ):(c.report (2*i+1)).wheel.r ≤ (c.report (2*i)).wheel.r:=by
    rw [even,odd]
    exact (c.separate i).le
  have seen(i:ℕ):Seen (f:=f) R B O χ H price number tests (pan (outer (c.pick i))) (c.report (2*i)):=by
    rw [even]; exact (named _).2 _ (c.outer i)
  have checked(i:ℕ):(c.report (2*i+1)).checked f H (2*i+1):=by
    rw [odd]; exact ((named _).2 _ (c.inner i)).choose
  intro e
  exact WilsonPhysicalStationOwnedTableFaculty.original R B O χ H price number tests F J₀ c.report
    (fun i=>cap (outer (c.pick i))) (fun i=>pan (outer (c.pick i))) L fac J simple below rfl
    deep late house dates window seen checked (files (e+1))

end YM.Integration.WilsonPhysicalStationOwnedTablePair
end
