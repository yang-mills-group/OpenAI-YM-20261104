import YM.Integration.WilsonOriginalObservedRosePublicSum
import YM.Integration.WilsonOlderFreshSoftSocketFigureRoom

/-! The funded kinetic stage, every true digit of the original 6/4/4, and the signed high-order sum on that same trial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicSchool
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

private theorem mass_on (t:Finset (Fin 3)):
    WilsonCoeffUV.Wheel.Mark.mass (WilsonOlderFreshSoftRoseCourse.grade ∘ seat t) Finset.univ=
      WilsonCoeffUV.Wheel.Mark.mass ages t:=by
  change (∑i:t,ages i.val)=∑i∈t,ages i
  exact Finset.sum_coe_sort t _

private theorem restored {L M:Levels G}(h:L=M)(x:Digits M (Fin 3)):
    cast (congrArg (fun q=>Digits q (Fin 3)) h) (show Digits L (Fin 3) from h.symm ▸ x)=x:=by cases h;rfl

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P))
    (funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W):
    ∃bank:ℕ,∀target debt mesh:ℕ,∃U:Set ℝ,U∈trail ∧
    let J₀:=stop target (debt+2*bank) mesh
    ∀Q:ℕ,J₀≤Q → ∀L:ℕ,∀D:Fin 3→ℕ,(∀i,ages i<D i) → ∀X opt tol:ℝ,0≤X → 0≤opt → 0<tol →
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (Q+1) Credit.leanC)(draw:V.draws=P),
    V.paid=R.metals.O ∧ V.y=zz P ∧ V.anchor=v ∧ Covered R D Q v start V draw opt tol ∧
    (∀s:Finset (Fin 3),s.Nonempty → Stock R D Q v start V draw opt tol s) ∧
    ∀r∈U,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),WilsonMovingForkWindowBooks.Priced F B →
    ∀actual:Next.UVStress.Lifts (C) B.k,∀(N per b K c requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N →
    v≤c → c≤K → v+1≤K → σ K-σ v≤L*Real.log (β v) →
    let θ:=g N per v
    r/(a K)≤(θ⁻¹)^mesh →
    ∀(n:ℕ)(face:Fin n→{s:(J).Mode // s.val.Nonempty})(file:Filed R ages K)
      (panel:Fin n→Panel R ages N per b K bk kn requested power tag credit),
    (∀i,(panel i).slot=file.station) → (∀i,(panel i).axis=file.A N per) →
    (∀i j,(panel i).slot j=B.W.k) →
    (∀i j,(panel i).names j=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per j) →
    ∀(κ:Fin n→(i:Fin 3)→Knob (D i))(pt:Fin n→Fin 3→Chamber)(cells:Fin n→Digits (P) (Fin 3))
      (y:Fin n→Fin 3→ Cover)(test:(i:Fin n)→Pen D (face i).val.val→L[ℝ]ℝ)
      (phase:Fin n→ℂ),(∀i,‖test i‖≤X*(θ⁻¹)^debt) →
    let w i:=votes R ages (N:=N) (per:=per) file (panel i).names (panel i).turn
    let row i:=normalized R ages (κ i) (pt i) N per K c v (cells i) (face i).val.val (w i) (y i) (test i)
    let heard j:=∑i:Fin n,phase i*(r:ℂ)^(height ages (face i).val.val)*row i j θ
    ‖heard Q-heard J₀‖≤(∑i:Fin n,‖phase i‖)*θ^target:=by
  obtain ⟨E,received⟩:=WilsonOriginalObservedRosePublicSum.original F Jr Z simple bliss lead obedient slow shop cap upper quote
  refine ⟨E,?_⟩
  intro target debt mesh
  obtain ⟨U,active,calendar⟩:=received target debt mesh
  refine ⟨U,active,?_⟩
  intro J₀ Q retained L D fits X opt tol xp op tp
  obtain ⟨start,school⟩:=WilsonOlderFreshSoftSocketFigureRoom.original R funded D fits Q opt tol op tp
  refine ⟨start,?_⟩
  filter_upwards [school,calendar Q retained L D X xp] with v bought prices
  obtain ⟨V,draw,scheme,heat,anchor,complete,covered,issued⟩:=bought
  refine ⟨V,draw,scheme,heat,anchor,covered,issued,?_⟩
  intro r hr T B book actual N per b K c requested power tag credit bk kn deep vc ck next span θ top n face file panel stations axes homes names κ pt cells y test phase capFee w row heard
  have scale:(a B.W.k)≤r:=(WilsonReflectedPublicBulbBerth.mesh R B.W B.checked).trans B.active.le
  let lifted (i:Fin n):Digits V.draws (Fin 3):=draw.symm ▸ cells i
  have same (i:Fin n):cast (congrArg (fun q=>Digits q (Fin 3)) draw) (lifted i)=cells i:=restored draw _
  have bound:=prices V draw scheme heat anchor.le r hr B book actual N per b K c requested power tag credit bk kn deep vc ck next span
    ((div_le_div_of_nonneg_right scale ((C).S.a_pos K).le).trans top) top n face file panel stations axes homes names
    (fun i=>mass_on (face i).val.val ▸ complete (face i).val.val) κ pt lifted y test phase capFee
  simpa only [same] using bound

end YM.Integration.WilsonOriginalObservedRosePublicSchool
end
