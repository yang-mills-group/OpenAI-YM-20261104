import YM.Integration.WilsonOriginalObservedRosePublicConnected
import YM.Integration.WilsonOriginalObservedRosePooledFigure
import YM.Integration.WilsonReceivedChronologicalFixedRosePooledMesh
import YM.Integration.WilsonOriginalObservedRoseProbeShelf
import YM.Integration.WilsonOriginalObservedRosePooledRestore
import YM.Integration.WilsonOriginalObservedRosePooledVotes
import YM.Integration.WilsonOriginalObservedRoseMovingAbsolute
import YM.Integration.WilsonOriginalObservedRosePublicGross
import YM.Integration.WilsonOriginalObservedRoseMovingBoundary
import YM.Integration.WilsonOriginalObservedRoseMovingKinetic
import YM.Integration.WilsonOlderFreshSoftSocketCensus
import YM.Integration.WilsonOriginalObservedRosePublicVotes
import YM.Integration.WilsonOriginalObservedRoseMovingTail
import YM.Integration.WilsonOriginalObservedRosePublicCurrency

/-! Source-matched enrollment of the physical Rose, its independently normalized high and low figures, and its actual finite kinetic boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPooledFigures
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


open WilsonOriginalObservedRosePublicGross (base)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketFaces (fill)

open WilsonOriginalObservedRosePooledPurse (reading)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)

open private mass_on from YM.Integration.WilsonOriginalObservedRosePublicConnected

private theorem placed {L M:Levels G}(h:L=M)(x:Digits M (Fin 3)):
    cast (congrArg (fun q=>Digits q (Fin 3)) h) (show Digits L (Fin 3) from h.symm ▸ x)=x:=by cases h;rfl

def mesh (T h width:ℕ):ℕ:=WilsonOriginalObservedRosePublicMesh.aperture
  (WilsonReceivedChronologicalFixedRosePooledMesh.width width (2*T+11+2*h))
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (color:G.ColorIndex)(funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(T h:ℕ){δ:ℝ}
    (books:(t:{t:ℝ // 0<t ∧ t<δ})→Book F (l:=l) H z 6 T t.val)
    (delivered:∀t,WilsonMovingForkWindowBooks.Priced F (books t))(x:∀i:Fin 3,RG17.Free C (grade i).val):
    ∃bank:ℕ,∀debt width:ℕ,∃U:Set ℝ,U∈trail ∧
    ∀Q:ℕ,9≤Q → ∀(D:Fin 3→ℕ)(X:ℝ),0≤X → ∀ᶠv:ℕ in atTop,
    ∀{start:ℕ}{opt tol:ℝ}(_office:WilsonOriginalObservedRoseProbeShelf.Badge R D Q v start opt tol),
    ∀r∈U,∀ρ:Fin 3→{t:ℝ // 0<t ∧ t<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let slots i:=reading F Jr Z (books (ρ i)) (grade i) (x i)
    let f:=reporter F books ρ
    ∀(N per b K c requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N → v≤f → f≤K →
    v≤c → c≤K → v+1≤K → σ K-σ (v-1)≤(width:ℝ)*(1+Real.log (β v)) →
    ∀(panel:Panel R ages N per b K bk kn requested power tag credit)(file:Filed R ages K),
    panel.slot=file.station → panel.axis=file.A N per → (∀i,panel.slot i=(slots i).j) →
    (∀i,panel.names i=(slots i).arm.source (N,per)) →
    let θ:=g N per v
    ∀(s:Finset (Fin 3)),s.Nonempty → ∀(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)(cells:Digits (P) (Fin 3))
      (pins:Fin 3→ Cover)(test:Pen D s→L[ℝ]ℝ),‖test‖≤X*(θ⁻¹)^debt →
    let w:=votes R ages (N:=N) (per:=per) file panel.names panel.turn
    r^(height ages s)*‖figure R ages κ pt N per K c v cells s w pins test Q θ‖≤
      2*(θ⁻¹)^(base bank debt+mesh T h width*height ages s):=by
  classical
  obtain ⟨bank,figurePrice⟩:=WilsonOriginalObservedRosePooledFigure.original F Jr Z simple bliss lead
    obedient slow shop cap upper color funded paths T h books delivered x
  refine ⟨bank,?_⟩
  intro debt width
  obtain ⟨U,valid,offer⟩:=figurePrice debt (mesh T h width)
  obtain ⟨U',valid',grid⟩:=WilsonReceivedChronologicalFixedRosePooledMesh.original (R:=R) F Jr Z simple bliss slow
    width 6 T h grade x books
  refine ⟨U∩U',inter_mem valid valid',?_⟩
  intro Q q D X xp
  have all:=Filter.eventually_all.mpr (fun s:{s:(J).Mode // s.val.Nonempty}=>offer Q 0 q (2*width) D s.val s.property X xp)
  filter_upwards [all,grid] with v sale purchase
  intro start opt tol office r hr ρ home nearest slots f N per b K c req power tag credit bk kn deep vf fk vc ck next span
    panel file stations axes dates names θ s hs κ pt cells pins test budget w
  obtain ⟨cash,_,scales⟩:=purchase r hr.2 ρ home nearest (K:=K) (N:=N) (per:=per) vf fk kn span
  let mode:(J).Mode:=⟨s,Finset.mem_univ _⟩
  let pressed:Digits office.field.draws (Fin 3):=office.draw.symm ▸ cells
  have same:cast (congrArg (fun q=>Digits q (Fin 3)) office.draw) pressed=cells:=placed office.draw _
  have rates(i:Fin 3):(a (panel.slot i))/(a K)≤(θ⁻¹)^(mesh T h width):=by rw [dates i];exact scales i
  obtain ⟨low,_,reset⟩:=sale ⟨mode,hs⟩ office.field office.draw office.paid office.quiet office.date.le
    (mass_on s ▸ office.proper s) r hr.1 ρ home nearest N per b K c req power tag credit bk kn deep
    fk vc ck next cash panel file stations axes dates names (fun i _=>rates i) κ pt pressed pins test budget
  dsimp only at low reset
  simp only [mode,same,pow_zero,mul_one] at low reset
  have prev:=low Q le_rfl
  let A:=figure R ages κ pt N per K c v cells s w pins test Q θ
  let B:=normalized R ages κ pt N per K c v cells s w pins test Q θ
  let M:=(θ⁻¹)^(base bank debt+mesh T h width*height ages s)
  have rpos:0≤r:=(ρ (Classical.choose nearest)).property.1.le.trans (Classical.choose_spec nearest).le
  have rp:0≤r^(height ages s):=pow_nonneg rpos _
  have income:r^(height ages s)*‖B‖≤M:=prev
  have compare:r^(height ages s)*‖A-B‖≤M:=reset
  calc _≤r^(height ages s)*(‖A-B‖+‖B‖):=mul_le_mul_of_nonneg_left (by simpa using norm_add_le (A-B) B) rp
       _≤2*M:=by rw [mul_add];linarith only [income,compare]

end YM.Integration.WilsonOlderFreshSoftSocketStationPooledFigures
end
