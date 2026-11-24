import YM.Integration.WilsonOriginalGeneralRosterHomePage
import YM.Integration.WilsonIndependentConditionedWideBirthClock

/-! Each independently dilated stock test has its own genuine capture and
stop address on the one common physical K. Its period-uniform temperature is
the coupling at that stock's own radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeStops
open Function Filter Finset Set Lattice RG Wilson Source Labels Extraction Table Spec PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato Climb Next.Rank Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonPositionProgramReporterBand (Band)
open WilsonReceivedChronologicalFixedCellFee (factor)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedWideBirthClock (Issued span)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][Nonempty I]{D T:ℕ}{δ:ℝ}
local notation "mesh" => R.family.S.a
local notation "H₀" => R.family.path.levels.clock.hatBeta

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels){world:XSpace.Run}{stage u depth:ℕ}
    (run:Band R world stage)(stop:WilsonIndependentCapturedPages.Stop R world run u depth)
    (active:0<stage)(deep:0<depth)(old:R.family.ref 0≤u)(ask floor h reserve:ℕ)
    (d:I→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (arity:I→ℕ)(φ:∀i,Test (arity i))(house:I→ℝ)(positive:∀i,0<house i):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R reserve f
    ∀i,let s:=(ρ i).val
      Issued R run stop ask floor (φ i) (house i) s (wilson z s) (date R simple s) f K
        (span R simple slow (2*T+11+2*h) reserve depth):=by
  classical
  let U:=2*T+11+2*h
  have law:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have booked (i:I):=WilsonIndependentConditionedWideBirthClock.original R simple slow ready law run stop
    active deep old ask floor (φ i) (positive i) U reserve 0
  have margin (i:I):∀ᶠs in trail,(wilson z s)^2 < min (house i) (factor R (φ i))/8:=
    ((law.conforms simple).pow 2).eventually (gt_mem_nhds (by
      simpa using div_pos (lt_min (positive i) (WilsonReceivedChronologicalFixedCellFee.positive R (φ i))) (by norm_num:0<(8:ℝ))))
  obtain ⟨limit,lp,all⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp (Filter.eventually_all.mpr fun i=>(booked i).and (margin i))
  have narrow:∀ᶠr in trail,outer z h r≤limit:=(longer F simple bliss h).eventually
    ((eventually_le_nhds lp).filter_mono nhdsWithin_le_nhds)
  filter_upwards [narrow,WilsonOriginalGeneralRosterHomePage.original F simple bliss slow D T h reserve 0 d
    (show 0<(1:ℝ) by norm_num) books] with r low grid
  intro ρ range root f K i s
  obtain ⟨_first,small,page⟩:=grid ρ range root i
  obtain ⟨paid,space⟩:=all (Set.mem_Ioc.mpr ⟨(ρ i).property.1,((range i).2).trans low⟩) i
  have fit:mesh f ≤ s:=(R.family.S.strictAnti.antitone page.before).trans page.covers
  have quit:8*mesh f < min (house i) (factor R (φ i))*s:=by
    have inside:mesh f < (min (house i) (factor R (φ i))/8)*s:=(div_lt_iff₀ (ρ i).property.1).1 (small.trans_lt space)
    linarith only [inside]
  exact paid f f fit quit ((div_le_iff₀ (R.family.S.a_pos f)).1 page.optical) le_rfl s le_rfl (by simp [s])

end YM.Integration.WilsonOriginalGeneralRosterHomeStops
end
