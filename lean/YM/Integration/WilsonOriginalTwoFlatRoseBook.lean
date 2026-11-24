import YM.Integration.WilsonOriginalTwoFlatRosePhase
import YM.Integration.WilsonOriginalTwoFlatRoseNominated

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseBook
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
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonOriginalTwoFlatRosePhase (fields)

def group {T:ℕ}{r:ℝ}(B:Book F (l:=l) H z 6 T r)(actual:Next.UVStress.Lifts C B.k):Group C 6 where
  horizon:=B.k
  fits:=B.fits
  station:=B.W
  lift:=actual
  change j:=(homogeneous F Jr Z r j).trans (B.V j).symm

theorem same {T:ℕ}{δ:ℝ}(books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (r:{s:ℝ // 0<s ∧ s<δ})(actual:Next.UVStress.Lifts C (books r).k)(N per:ℕ)(i:Fin 3):
    fields F Jr Z books r (fun _=>true) N per i=
      WilsonNeutralOffsetCutoff.named R (group F Jr Z (books r) actual) N per i:=
  ((books r).rows (grade i)).weak _ _

theorem selected (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    {T:ℕ}{M η δ:ℝ}(one:1≤M)(ep:0<η)(dp:0<δ)
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J u:ℕ,Stop C 0 J u ∧ ∀q:ℕ,∃A₀:ℝ,0≤A₀ ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,∀o:Fin 3 → Cover,
      (∀i,‖(C).S.gridPoint f (o i)‖≤M*r) → 
      (Pairwise fun i j=>η*r≤‖(C).S.gridPoint f (o i)-(C).S.gridPoint f (o j)‖) → 
      ∀(actual:Next.UVStress.Lifts C (books ⟨r,inside⟩).k)(E:Finset (Fin 3)),E.Nonempty →
        let A:=group F Jr Z (books ⟨r,inside⟩) actual
        let pins:=fun i=>((C).S.toDepth live.le per).embed (snap C f per o i)
        let fig:=face R A (pins 1,pins 2) E
        pins 0=0 →
        ‖gap R N per u (uf.trans live.le) fig‖ ≤ A₀*(wilson z r)^q ∧
          Heard R fac.simpleGate N per u fig (A₀*(wilson z r)^q):=by
  obtain ⟨J,u,stop,quotes⟩:=WilsonOriginalTwoFlatRosePhase.selected F Jr Z fac bliss slow lead paid one ep dp books window
  refine ⟨J,u,stop,fun q=>?_⟩
  obtain ⟨A₀,non,quoted⟩:=quotes q
  refine ⟨A₀,non,?_⟩
  filter_upwards [quoted] with r elected
  obtain ⟨inside,data⟩:=elected
  let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
  let f:=berth R 5 h
  change ∃uf:u≤f, _ at data
  obtain ⟨uf,enrolled⟩:=data
  refine ⟨inside,uf,?_⟩
  intro N per live o shape apart actual E nonempty A pins fig center
  have hear:=enrolled N per live o shape apart (fun _=>true) E nonempty
  have atOrigin:WilsonThermometerAlignedCells.atOrigin (pins 1,pins 2)=pins:=by
    funext i
    fin_cases i <;> simp [WilsonThermometerAlignedCells.atOrigin,center]
  have agree:(fun U=>∏i∈E,(C).O N per (fields F Jr Z books ⟨r,inside⟩ (fun _=>true) N per i) (pins i) U)=fig:=by
    funext U
    dsimp only [fig,face]
    rw [atOrigin]
    apply Finset.prod_congr rfl
    intro i _
    rw [same F Jr Z books ⟨r,inside⟩ actual N per i]
    rfl
  rw [←agree]
  exact hear

end YM.Integration.WilsonOriginalTwoFlatRoseBook
end
