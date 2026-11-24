import YM.Integration.WilsonOriginalObservedRosePublicConnected
import YM.Integration.WilsonReceivedChronologicalFixedCellFee
import YM.Integration.WilsonThermometerAlignedCells
import YM.Integration.WilsonOriginalObservedRosePublicMesh

/-! The signed relative-cell test of the complete connected finite-Haar tail, using the true deposited source tape, the original moving stop, and the actual appointed digits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseConnectedCells
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

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

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOlderFreshSoftRoseMesh (filed)
open WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonReflectedPublicStationFare
open PhysMS
open MS MS.Land FVA2 FVA2.Register
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse

variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalObservedRoseMeshHeight (tilt height)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonThermometerDeclaredSeeds
local notation "J" => Stock.census (Fin 3)

open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshSoftSocketOptical (fixed fixed_nonneg)
open WilsonOriginalObservedRoseStoppedSalary (stop)
local notation "σ" => R.family.S.scale
local notation "g" => Pert.Asymptotics.regulatorRun R.family

open WilsonOriginalOpticalSchedule (prepared)
open WilsonOlderFreshSoftRoseCourse (seat)
open WilsonOlderFreshSoftRoseNodes (Covered)
open WilsonOlderFreshSoftRoseIncome (Stock)
universe u
variable {axis:Axis}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}{crop:Campaign R}{W:Campaign.Pillars R crop}

open WilsonOriginalObservedRosePublicMesh (aperture)
open WilsonInvariantActionPosition (berth)

open WilsonOriginalObservedRosePublicGross (base)
open WilsonPositionThermometerConnected (value)
local notation "Faces" => Finset (Fin 3)

open WilsonOriginalObservedRosePublicConnected (cut)
open WilsonReceivedChronologicalFixedCellFee (tape)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonThermometerAlignedCells (atOrigin)
open MeasureTheory

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P))
    (funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W):
    ∃bank:ℕ,∀target debt width:ℕ,∃U:Set ℝ,U∈trail ∧
    let J₀:=cut target bank debt width
    ∀Q:ℕ,J₀≤Q → ∀L:ℕ,∀D:Fin 3→ℕ,(∀i,ages i<D i) → ∀X opt tol:ℝ,0≤X → 0≤opt → 0<tol →
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (Q+1) Credit.leanC)(draw:V.draws=P),
    V.paid=R.metals.O ∧ V.y=zz P ∧ V.anchor=v ∧ Covered R D Q v start V draw opt tol ∧
    (∀s:Finset (Fin 3),s.Nonempty → Stock R D Q v start V draw opt tol s) ∧
    ∀r∈U,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),WilsonMovingForkWindowBooks.Priced F B →
    ∀actual:Next.UVStress.Lifts (C) B.k,let K:=berth R width B.W.k
    v≤B.W.k → ∀(N per b c requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N →
    v≤c → c≤K → v+1≤K → σ K-σ v≤L*Real.log (β v) →
    let θ:=g N per v
    ∀(q₁:ℕ)(W:Realm G (q₁+1) Credit.leanC)(source:W.draws=(P))(first:ℕ),first+1≤v →
    ∀(file:Filed R ages K)(Φ:Test 3),
    let μ:=WilsonThermometerAlignedCells.mass (R:=R) r (b,per) Φ
    let Active:Type:={y:Site ((C).side b per) × Site ((C).side b per) // μ y≠0}
    ∀(panel:(o:Active)→{Z:Panel R ages N per b K bk kn requested power tag credit // Z.loc=atOrigin o.val}),
    (∀o,(panel o).val.slot=file.station) → (∀o,(panel o).val.axis=file.A N per) →
    (∀o i,(panel o).val.slot i=B.W.k) →
    (∀o i,(panel o).val.names i=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i) →
    ∀(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)
      (test:(o:Active)→(s:Faces)→Pen D s→L[ℝ]ℝ),
      (∀o,∀s:Faces,s.Nonempty → ‖test o s‖≤X*(θ⁻¹)^debt) →
    let filed o:=tape source bk (panel o).val.loc
    let cells o:=onLevels source (filed o)
    let pins o:=address (P) (cells o) (c-v) v (homes (V:=W) (filed o) 0 first (v-1-first))
    let w o:=votes R ages (N:=N) (per:=per) file (panel o).val.names (panel o).val.turn
    let row o j s:=normalized R ages κ pt N per K c v (cells o) s (w o) (pins o) (test o s) j θ
    let hearing j:=∑o:Active,μ o.val*((r:ℂ)^14*value (row o j))
    ‖hearing Q-hearing J₀‖≤(∫z:Points 3,‖Φ z‖)*θ^target:=by
  obtain ⟨E,booked⟩:=WilsonOriginalObservedRosePublicConnected.original F Jr Z simple bliss lead obedient slow shop cap upper quote funded
  refine ⟨E,?_⟩
  intro target debt width
  obtain ⟨U,active,cal⟩:=booked target debt width
  refine ⟨U,active,?_⟩
  intro J₀ Q retained L D fits X opt tol xp op tp
  obtain ⟨start,school⟩:=cal Q retained L D fits X opt tol xp op tp
  refine ⟨start,?_⟩
  filter_upwards [school] with v bought
  obtain ⟨V,draw,scheme,heat,anchor,covered,issued,spend⟩:=bought
  refine ⟨V,draw,scheme,heat,anchor,covered,issued,?_⟩
  intro r hr T B book actual K vj N per b c requested power tag credit bk kn deep vc ck next span θ q₁ W source first old file Φ μ Active panel stations axes heads names κ pt test paid filed cells pins w row hearing
  have each (o:Active):r^14*‖value (row o Q)-value (row o J₀)‖≤θ^target:=
    spend r hr B book actual vj N per b c requested power tag credit bk kn deep vc ck next span file
      (panel o).val (stations o) (axes o) (heads o) (names o) κ pt (cells o) (pins o) (test o) (paid o)
  have gp:0<θ:=ActualRunKernelPackets.regulator_pos R N per v ((vc.trans ck).trans kn)
  have rp:0≤r:=B.W.wheel.rad.le.trans B.active.le
  have cash:(∑o:Active,‖μ o.val‖)≤∫z:Points 3,‖Φ z‖:=by
    apply le_trans _ (WilsonThermometerAlignedCells.variation (R:=R) r (b,per) Φ)
    let ι:Active↪(Site ((C).side b per) × Site ((C).side b per)):=⟨Subtype.val,Subtype.val_injective⟩
    have identical:(∑o:Active,‖μ o.val‖)=∑z∈(Finset.univ:Finset Active).map ι,‖μ z‖:=by rw [Finset.sum_map];rfl
    rw [identical]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>norm_nonneg _)
  change ‖(∑o:Active,μ o.val*((r:ℂ)^14*value (row o Q)))-
    ∑o:Active,μ o.val*((r:ℂ)^14*value (row o J₀))‖≤_
  rw [←Finset.sum_sub_distrib]
  calc _≤∑o:Active,‖μ o.val‖*θ^target:=by
         apply (norm_sum_le ..).trans
         apply Finset.sum_le_sum
         intro o _
         rw [←mul_sub,←mul_sub,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg rp]
         exact mul_le_mul_of_nonneg_left (each o) (norm_nonneg _)
       _=(∑o:Active,‖μ o.val‖)*θ^target:=(Finset.sum_mul ..).symm
       _≤_:=mul_le_mul_of_nonneg_right cash (pow_nonneg gp.le _)

end YM.Integration.WilsonOriginalObservedRoseConnectedCells
end
