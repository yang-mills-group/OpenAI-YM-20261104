import YM.Integration.WilsonOriginalTwoFlatIRSocketAbsolute
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseAbsoluteTest
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

open WilsonOriginalTwoFlatRoseBook (group)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonOriginalTwoFlatRoseNominated (face)

open WilsonOriginalTwoFlatRoseRelativePhase (nodes recenter translated)

theorem original {J u:ℕ}(stop:Stop C 0 J u)(fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    {T:ℕ}{M η δ:ℝ}(one:1≤M)(ep:0<η)(dp:0<δ)
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)) (φ:Test 3)(q:ℕ):
    ∃A₀:ℝ,0≤A₀ ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,(∀i:Fin 3,(C).ref (grade i).val ≤ N) →
      ∀(actual:Next.UVStress.Lifts C (books ⟨r,inside⟩).k)
        (s:(Stock.census (Fin 3)).Mode),s.val.Nonempty →
      ∀K:ℕ,∀fk:f≤K,∀kn:K≤N,
      let D:=WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)
      ∀(o:D → Fin 3 → Cover),(∀y,snap C f per (o y)=y.val) →
        (∀y i,‖(C).S.gridPoint f (o y i)‖ ≤ M*r) →
        (∀y,Pairwise fun i j=>η*r ≤ ‖(C).S.gridPoint f (o y i)-(C).S.gridPoint f (o y j)‖) →
        ∀(Y:(y:D) → (i:Fin 3) → (C).label (grade i).val)(turn:D → Fin 3 → Motion),
        let A:=group F Jr Z (books ⟨r,inside⟩) actual
        (∀y i,displayed R (grade i).val (Y y i) (turn y i)=WilsonNeutralOffsetCutoff.named R A N per i) →
        let w:=fun y:D=>WilsonMeasuredPublicEntranceCellWords.physical R (fun i:Fin 3=>(grade i).val)
          (Y y) (turn y) y.val s (N:=N)
        let high:=fun y:D=>(C).omega N per (w y)
        let held:=fun y:D=>WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit C N per 0 (w y) K kn) u (uf.trans fk)
        (∀y:D,high y=(C).omega N per (face R A
          ((nodes (R:=R) live.le per (recenter (o y))) 1,(nodes (R:=R) live.le per (recenter (o y))) 2) s.val)) ∧
        (∀y:D,‖high y-held y‖≤A₀*(wilson z r)^q) ∧
        ‖WilsonReceivedChronologicalFixedRoseVariation.signed R φ r (f,per) (fun y=>high y-held y)‖
          ≤ (∫x,‖φ x‖)*(A₀*(wilson z r)^q):=by
  classical
  obtain ⟨A₀,pos,uniform⟩:=WilsonOriginalTwoFlatIRSocketAbsolute.original F Jr Z stop fac bliss slow lead paid
    one ep dp books window q
  refine ⟨A₀,pos,?_⟩
  filter_upwards [uniform,(wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive] with r issued gp
  obtain ⟨inside,uf,seen⟩:=issued
  refine ⟨inside,uf,?_⟩
  intro N per live ready actual s used K fk kn D o places housed separated Y turn A printed w high held
  have atSite(y:D):=seen N per live ready (o y) (housed y) (separated y) actual s used
    (Y y) (turn y) (printed y) K fk kn
  have point(y:D):‖high y-held y‖≤A₀*(wilson z r)^q:=by
    have x:=atSite y
    dsimp only at x
    rw [places y] at x
    exact (congrArg (fun (t:ℂ)=>‖t-held y‖) x.1).le.trans x.2
  refine ⟨?_,point,?_⟩
  · intro y
    have x:=atSite y
    dsimp only at x
    rw [places y] at x
    exact x.1
  · apply WilsonReceivedChronologicalFixedRoseVariation.original R φ r _ _ _ _ point
    exact mul_nonneg pos (pow_nonneg gp.le _)

end YM.Integration.WilsonReceivedChronologicalFixedRoseAbsoluteTest
end
