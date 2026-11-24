import YM.Integration.WilsonOriginalTwoFlatRoseBook
import YM.Integration.WilsonOriginalTwoFlatRoseCentered

/-! Translate the unrestricted physical product first. The original flat
and its K trial both use the resulting centered tuple of real grid sites. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseRelativePhase
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

def recenter (o:Fin 3 → Cover)(i:Fin 3):Cover:=o i-o 0

def nodes {j N:ℕ}(hn:j≤N)(per:ℕ)(o:Fin 3 → Cover)(i:Fin 3):Site ((C).side N per):=
  ((C).S.toDepth hn per).embed (snap C j per o i)

private theorem displacement {j N:ℕ}(hn:j≤N)(per:ℕ)(o:Fin 3 → Cover)(i):
    nodes (R:=R) hn per (recenter o) i = nodes (R:=R) hn per o i-nodes (R:=R) hn per o 0:=by
  unfold nodes RG16.Literal.snap recenter
  rw [Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap,smul_sub,map_sub]

private theorem grid_sub (ss:Schedule)(j:ℕ)(x y:Cover):
    ss.gridPoint j (x-y)=ss.gridPoint j x-ss.gridPoint j y:=by
  ext i
  change ss.a j*((x i-y i:ℤ):ℝ)=ss.a j*(x i:ℝ)-ss.a j*(y i:ℝ)
  push_cast
  ring

theorem translated (A:WilsonPositionThermometerCapStation.Group C 6){j N:ℕ}(hn:j≤N)(per:ℕ)
    (ready:∀i:Fin 3,(C).ref (grade i).val≤N)(o:Fin 3 → Cover)(E:Finset (Fin 3)):
    let pins:=nodes (R:=R) hn per (recenter o)
    pins 0=0 ∧ WilsonOriginalTwoFlatRoseCentered.ordinary R A N per (nodes (R:=R) hn per o) E=
      (C).omega N per (face R A (pins 1,pins 2) E):=by
  intro pins
  have zero:pins 0=0:=by simp [pins,displacement]
  have home:atOrigin (pins 1,pins 2)=pins:=by
    funext i; fin_cases i <;> simp [atOrigin,zero]
  refine ⟨zero,?_⟩
  have restored:(fun i=>pins i+nodes (R:=R) hn per o 0)=nodes (R:=R) hn per o:=by
    funext i; simp [pins,displacement]
  have sale:=WilsonOriginalTwoFlatRoseCentered.translated R A N per ready pins (nodes (R:=R) hn per o 0) E
  rw [restored] at sale
  rw [sale]
  unfold WilsonOriginalTwoFlatRoseCentered.ordinary face
  rw [home]

theorem selected (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    {T:ℕ}{M η δ:ℝ}(one:1≤M)(ep:0<η)(dp:0<δ)
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J u:ℕ,Stop C 0 J u ∧ ∀q:ℕ,∃A₀:ℝ,0≤A₀ ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,(∀i:Fin 3,(C).ref (grade i).val ≤ N) → ∀o:Fin 3 → Cover,
      (∀i,‖(C).S.gridPoint f (o i)‖≤M*r) → 
      (Pairwise fun i j=>η*r≤‖(C).S.gridPoint f (o i)-(C).S.gridPoint f (o j)‖) → 
      ∀(actual:Next.UVStress.Lifts C (books ⟨r,inside⟩).k)(E:Finset (Fin 3)),E.Nonempty →
        let A:=group F Jr Z (books ⟨r,inside⟩) actual
        let pins:=nodes (R:=R) live.le per (recenter o)
        let fig:=face R A (pins 1,pins 2) E
        let physical:=WilsonOriginalTwoFlatRoseCentered.ordinary R A N per (nodes (R:=R) live.le per o) E
        pins 0=0 ∧ physical=(C).omega N per fig ∧
          ‖physical-WilsonThermometerUnitFilingCoarse.reading R (N:=N)
            (credit C N per 0 fig u (uf.trans live.le)) u le_rfl‖ ≤ A₀*(wilson z r)^q ∧
          Heard R fac.simpleGate N per u fig (A₀*(wilson z r)^q):=by
  obtain ⟨J,u,stop,quotes⟩:=WilsonOriginalTwoFlatRoseBook.selected F Jr Z fac bliss slow lead paid
    (M:=2*M) (by linarith) ep dp books window
  refine ⟨J,u,stop,fun q=>?_⟩
  obtain ⟨A₀,nonneg,fees⟩:=quotes q
  refine ⟨A₀,nonneg,?_⟩
  filter_upwards [fees] with r submitted
  obtain ⟨inside,uf,ear⟩:=submitted
  refine ⟨inside,uf,?_⟩
  intro N per live ready o small separated lift E occupied A pins fig physical
  let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k))
  have near(i:Fin 3):‖(C).S.gridPoint f (recenter o i)‖ ≤ ((2*M)*r):=by
    rw [recenter,grid_sub]
    exact (norm_sub_le ..).trans (by nlinarith [small i, small 0])
  have apart:Pairwise fun i j=>η*r≤‖(C).S.gridPoint f (recenter o i)-(C).S.gridPoint f (recenter o j)‖:=by
    intro i j hij
    simp only [recenter,grid_sub]
    convert separated hij using 2
    abel
  have original:=translated (R:=R) A live.le per ready o E
  have bound:=ear N per live (recenter o) near apart lift E occupied original.1
  refine ⟨original.1,original.2,?_,bound.2⟩
  dsimp only [physical]
  rw [original.2]
  exact bound.1

end YM.Integration.WilsonOriginalTwoFlatRoseRelativePhase
end
