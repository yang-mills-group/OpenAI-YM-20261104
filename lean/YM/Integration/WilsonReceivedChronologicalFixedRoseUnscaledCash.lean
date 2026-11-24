import YM.Integration.WilsonOriginalTwoFlatIRPoolUnscaledVotes
import YM.Integration.WilsonOriginalObservedRosePooledVotes
import YM.Integration.WilsonReceivedChronologicalFixedRosePublicAperture
import YM.Integration.WilsonOriginalObservedRosePooledFilms
import YM.Integration.WilsonOriginalObservedRosePooledPurse
import YM.Integration.WilsonOriginalObservedRosePublicCurrency

/-! Sector-wise budgets on the actual pooled filed directions, including their original deposited terminal mass. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseUnscaledCash
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
  {n:ℕ}[Nonempty (Fin n)]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)


open WilsonMovingForkSlotDate (slot)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalObservedRosePooledWrap (allowance)
open WilsonOriginalObservedRoseMeshHeight (variation)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)

open WilsonOriginalObservedRosePooledPurse (reading)
open WilsonOriginalObservedRoseMeshHeight (tilt)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonThermometerPositionTunedSlope (Columns)
open ActualRunPhysicalPages Pert.Asymptotics

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(lo:∀j,1≤((P).budget j).supportExponent)
    (hi:∀j,((P).budget j).supportExponent≤100)(D T h:ℕ)(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free (C) (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    let k:=fun i=>(d i).val
    ∃(M:Fin n→ℝ)(E:ℕ),(∀i,0≤M i) ∧ ∀reserve:ℕ,∃U:Set ℝ,U∈trail ∧ ∀A:ℕ,∀ᶠv:ℕ in atTop,∀r∈U,
      ∀ρ:Fin n→{t:ℝ // 0<t ∧ t<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      let L:=fun i=>reading F Jr Z (books (ρ i)) (d i) (x i)
      let W:=WilsonReceivedChronologicalFixedRosePublicAperture.width reserve (2*T+11+2*h)
      let mesh:=WilsonOriginalObservedRosePublicMesh.aperture W
      let K:=WilsonInvariantActionPosition.berth R reserve f
      ∀(N per requested power tag:ℕ)(credit:ℝ)(bk:f≤K)(kn:K≤N),f<N→v≤f →
      (C).S.scale K-(C).S.scale (v-1)≤(A:ℝ)*(1+Real.log (β v))→let θ:=regulatorRun (C) N per v
      ∀P₀:Panel R k N per f K bk kn requested power tag credit,∀file:Filed R k K,
      P₀.slot=file.station→P₀.axis=file.A N per→(∀i,P₀.slot i=(L i).j)→(∀i,P₀.names i=(L i).arm.source (N,per))→
      ∀s:Finset (Fin n),let w:=votes R k (N:=N) (per:=per) file P₀.names P₀.turn
      let due:=WilsonOriginalObservedRosePooledVotes.charge (R:=R) k M E s*(θ⁻¹)^(2*E)*
        (θ⁻¹)^(mesh*WilsonOriginalObservedRoseMeshHeight.height k s+1)
      (∑q:Selection R k s,‖weight R k N per K w s q‖)≤due ∧
      (∑b:Columns R (fun i:s=>k i),‖packet R k s w N per K b‖)≤due:=by
  intro k
  obtain ⟨M,E,positive,earned⟩:=WilsonOriginalTwoFlatIRPoolUnscaledVotes.original F Jr Z simple bliss slow
    lead paid shop lo hi D T h d x books window
  refine ⟨M,E,positive,?_⟩
  intro reserve
  let W:=WilsonReceivedChronologicalFixedRosePublicAperture.width reserve (2*T+11+2*h)
  obtain ⟨U,earlier,prices⟩:=earned (WilsonOriginalObservedRosePublicMesh.aperture W)
  obtain ⟨S₀,tape,geometry⟩:=WilsonReceivedChronologicalFixedRosePublicAperture.original F Jr Z simple bliss slow reserve D T h d x books
  refine ⟨U∩S₀,inter_mem earlier tape,?_⟩
  intro A
  filter_upwards [prices (2*A),geometry A,WilsonOriginalOpticalCouplingBand.cold R simple 1]
    with v cash meshAt cold r present ρ span near f L W₀ mesh K N per requested power tag credit bk kn live vf elapsed θ
  obtain ⟨direct,relative⟩:=meshAt r present.2 ρ span near (N:=N) (per:=per) vf bk kn elapsed
  intro P₀ file seats axes stationed names s
  have zp:1≤θ⁻¹:=cold N per ((vf.trans bk).trans kn)
  apply cash r present.1 ρ span near N per f K requested power tag credit bk kn live (vf.trans bk) bk direct
    P₀ file seats axes stationed names zp s
  intro i _hi
  rw [stationed i]
  exact relative i

end YM.Integration.WilsonReceivedChronologicalFixedRoseUnscaledCash
