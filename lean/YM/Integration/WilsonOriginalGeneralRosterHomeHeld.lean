import YM.Integration.WilsonOriginalGeneralRosterHomeStops
import YM.Integration.WilsonIndependentConditionedHeldRateBill

/-! The four held bills for every reflected pair are paid at its actual
home stopping address, at the common K of the finite stock. The cash and
tariff powers are bought before the pair's home, fine cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeHeld
open Function Filter Finset Set Lattice RG Wilson Marker Tree QuadraticLocal Multi Source Labels Extraction Table Spec PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato Climb Next.Rank Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonPositionProgramReporterBand (Band)
open WilsonReceivedChronologicalFixedCellFee (capture)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedWideBirthClock (Issued span)
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonIndependentConditionedHeldRateBill (bill)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][Nonempty I]{D T:ℕ}{δ:ℝ}
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "J" => Stock.census (Fin 2)

def Charged {world:XSpace.Run}{stage u depth:ℕ}(run:Band R world stage)
    (stop:WilsonIndependentCapturedPages.Stop R world run u depth)(φ:Test 2)(s heat:ℝ)
    (d p₀ target f K A P E promised goal:ℕ)(b C θ η cash:ℝ):Prop:=
  let v:=stop.date (capture R φ s-run.reporter)
  ∀N per:ℕ,K≤N→
    0 < regulatorRun R.family N per v ∧ regulatorRun R.family N per v≤4*heat ∧
    ∀S:(J).Mode,wallet R (fun _:Fin 2=>d) (fun _=>b*(β K)^p₀) S.val *
      bill (fun _:Fin 2=>d) A P E promised goal C θ η (regulatorRun R.family N per v) S ≤ cash*(thermal R f)^target

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels){world:XSpace.Run}{stage u depth:ℕ}
    (run:Band R world stage)(stop:WilsonIndependentCapturedPages.Stop R world run u depth)
    (active:0<stage)(deep:0<depth)(old:R.family.ref 0≤u)(ask floor h reserve:ℕ)
    (d:I→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (φ:I→Test 2)(house:I→ℝ)(positive:∀i,0<house i)
    (b:I→ℝ)(bn:∀i,0≤b i)(p₀ target A P E promised goal:I→ℕ)(C θ η:I→ℝ)
    (hp:∀i,target i+4*p₀ i ≤ P i)(hh:∀i,target i+4*p₀ i ≤ promised i)(hg:∀i,target i+4*p₀ i ≤ goal i):
    ∃cash:I→ℝ,(∀i,0≤cash i) ∧ ∀ᶠr in trail,
    ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R reserve f
    ∀i,let s:=(ρ i).val
      Issued R run stop ask floor (φ i) (house i) s (wilson z s) (date R simple s) f K
          (span R simple slow (2*T+11+2*h) reserve depth) ∧
      Charged run stop (φ i) s (wilson z s) (d i).val (p₀ i) (target i) f K (A i) (P i) (E i)
        (promised i) (goal i) (b i) (C i) (θ i) (η i) (cash i):=by
  classical
  let annual:=span R simple slow (2*T+11+2*h) reserve depth
  choose cash nn fiscal using fun i=>WilsonIndependentConditionedHeldRateBill.original R (fun _:Fin 2=>(d i).val)
    simple slow (b i) (bn i) (p₀ i) (target i) reserve annual (A i) (P i) (E i) (promised i) (goal i)
    (C i) (θ i) (η i) (hp i) (hh i) (hg i)
  obtain ⟨mark,buy⟩:=eventually_atTop.mp (Filter.eventually_all.mpr fiscal)
  refine ⟨cash,nn,?_⟩
  filter_upwards [(WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop mark,
    WilsonOriginalGeneralRosterHomeStops.original F simple bliss slow ready run stop active deep old ask floor h reserve d
      books (fun _=>2) φ house positive,
    WilsonOriginalGeneralRosterHomePage.original F simple bliss slow D T h reserve 0 d
      (show 0<(1:ℝ) by norm_num) books] with r late passes pages
  intro ρ range root f K i s
  obtain ⟨j,hj⟩:=root
  have base:=((pages ρ range ⟨j,hj⟩ j).2.2).before
  rw [hj] at base
  have sale:=passes ρ range ⟨j,hj⟩ i
  refine ⟨sale,?_⟩
  obtain ⟨w,address,_uc,vc,next,_uv,_sv,_strict,_floor,cf,_home,_thin,_fit,ticket,_offer⟩:=sale
  change capture R (φ i) s=run.reporter+w at address
  have key:capture R (φ i) s-run.reporter=w:=by rw [address];omega
  unfold Charged
  dsimp only
  rw [key]
  intro N per live
  have fk:f≤K:=((pages ρ range ⟨j,hj⟩ i).2.2).higher.le
  have warm:=ticket.heat N per (cf.le.trans (fk.trans live))
  rw [next] at warm
  have clock:=ticket.span
  rw [next] at clock
  exact ⟨warm.1,warm.2,fun S=>buy f (late.trans base) i (first:=stop.date w-1) (v:=stop.date w) (N:=N) (per:=per)
    (Nat.sub_le _ _) (vc.trans cf.le) live clock S⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeHeld
end
