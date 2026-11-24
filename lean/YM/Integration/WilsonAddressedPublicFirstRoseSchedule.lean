import YM.Integration.WilsonAddressedPublicFirstRoseBookedClock

/-! The physical clock width is named before the school, test, reporting
sites, infrared appointment and both regulators. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseSchedule
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open Analysis XSpace Cells Table Spec Extraction
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonReceivedChronologicalFixedCellFee (capture factor)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open WilsonPositionProgramReporterBand (Band)


open Pert.Asymptotics
local notation "β₀" => R.family.path.levels.clock.hatBeta
local notation "mesh" => R.family.S.a
local notation "scale" => R.family.S.scale

def allowance (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (T h reserve infrared:ℕ):ℕ:=
  (WilsonMovingForkOpticalStops.original R simple slow reserve (2*T+11+2*h+2) infrared).choose+2

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (world:XSpace.Run){stage u infrared:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u infrared)(positive:0 < stage)(deep:0 < infrared)
    (cu:R.family.ref 0 ≤ u)(power floor:ℕ){n:ℕ}(φ:Test n){hi:ℝ}(hp:0 < hi)
    (D T h reserve:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    let width:=allowance R simple slow T h reserve infrared
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let f:=berth R 5 (univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k)
      let K:=berth R reserve f
      let c:=capture R φ r
      ∃w:ℕ,∃_center:c=run.reporter+w,∃uc:u ≤ c,∃vc:v.date w ≤ c,
        let first:=v.date w-1
        first+1=v.date w ∧ u ≤ v.date w ∧ stage ≤ v.date w ∧ floor+1 ≤ c ∧
        c≤f ∧ WilsonAddressedPublicFirstRoseTicket.Receipt R hi (factor R φ) r (wilson z r) first f K c width ∧
        ∀N per:ℕ,c<N → Quote R N per u (v.date w) c power infrared uc vc:=by
  intro width
  let W:=2*T+11+2*h
  have cash:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have lp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  let size:=(WilsonMovingForkOpticalStops.original R simple slow reserve (W+2) infrared).choose
  have clock:=(WilsonMovingForkOpticalStops.original R simple slow reserve (W+2) infrared).choose_spec
  obtain ⟨older,clock⟩:=eventually_atTop.mp clock
  obtain ⟨hot,rich⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
    (3*factor R φ))
  obtain ⟨native,stop⟩:=eventually_atTop.mp v.heard
  let limit:=max floor (max older (max hot (run.reporter+native)))
  have entered:=WilsonAddressedPublicFirstRosePublicStops.original F simple bliss slow ready world run v
    positive deep cu power limit φ hp lp D T h d books
  filter_upwards [WilsonAddressedPublicFirstRoseTicket.original R simple cash hp lp,entered,WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T h d books,
    WilsonMovingForkStoppedHeat.original R simple cash (W+2) infrared,
    WilsonThermometerUnitFilingCaptureCoupling.small simple cash zero_lt_one,cash.positive,self_mem_nhdsWithin]
    with r fitted appointment publicMesh thermal cheap gp rp
  intro ρ span anchor f K c
  obtain ⟨w,eq,uc,vc,date,uv,age,floorFit,hiFit,loFit,quote⟩:=appointment ρ span anchor
  have after:limit≤c:=Nat.le_of_succ_le floorFit
  have cf:c≤f:=loFit.finer
  have ofit:older≤f:=(le_max_left older _).trans ((le_max_right floor _).trans (after.trans cf))
  have funded:hot≤f:=(le_max_left hot _).trans ((le_max_right older _).trans
    ((le_max_right floor _).trans (after.trans cf)))
  have reached:run.reporter+native≤c:=(le_max_right hot _).trans ((le_max_right older _).trans
    ((le_max_right floor _).trans after))
  have nw:native≤w:=by change c=run.reporter+w at eq;omega
  have fees:=publicMesh ρ span anchor
  have near:mesh f≤r:=(div_le_one₀ rp).mp (fees.1.trans (pow_le_one₀ gp.le cheap))
  obtain ⟨i,home⟩:=anchor
  have posted:r≤(β₀ f)^W*mesh f:=home ▸ fees.2 i
  have receipt:=WilsonAddressedPublicFirstRoseCaptureWidth.original R simple slow rp lp cf
    (WilsonCloseCaptureDate.bracket R.family.S (mul_pos lp rp) loFit.small).1 (rich f funded) posted
  have hours (N per:ℕ)(live:c≤N):scale c-scale (v.date w) ≤
      4*(2*(infrared:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹:=by
    change c=run.reporter+w at eq
    rw [eq] at live ⊢
    exact ((stop w nw).2 N per live).2.2.2
  have observed:mesh (v.date w)/mesh K ≤ (β₀ (v.date w))^size:=
    (clock f ofit c (v.date w) c 0 cf vc le_rfl receipt (hours c 0 le_rfl)).1
  have earned:=WilsonAddressedPublicFirstRoseCaptureWidth.previous R simple slow (v.date w-1) K size
    (by rw [date];exact observed)
  have fit:=fitted (v.date w-1) f hiFit loFit fees.1
  exact ⟨w,eq,uc,vc,date,uv,age,(Nat.succ_le_succ (le_max_left floor _)).trans floorFit,cf,
    ⟨rp,fit.1,fit.2,earned,fun N per live=>by
      rw [date]
      exact thermal f c (v.date w) N per near cf vc live receipt (hours N per live)⟩,quote⟩

end YM.Integration.WilsonAddressedPublicFirstRoseSchedule
end
