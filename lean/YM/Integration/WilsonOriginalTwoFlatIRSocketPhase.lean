import YM.Integration.WilsonOriginalTwoFlatRoseFixedCourse
import YM.Integration.WilsonMeasuredPublicEntranceCellWords

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketPhase
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
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)) (q:ℕ):
    ∃A₀:ℝ,0≤A₀ ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,(∀i:Fin 3,(C).ref (grade i).val ≤ N) → ∀o:Fin 3 → Cover,
      (∀i,‖(C).S.gridPoint f (o i)‖≤M*r) → 
      (Pairwise fun i j=>η*r≤‖(C).S.gridPoint f (o i)-(C).S.gridPoint f (o j)‖) → 
      ∀(actual:Next.UVStress.Lifts C (books ⟨r,inside⟩).k)(s:(Stock.census (Fin 3)).Mode),s.val.Nonempty →
        let A:=group F Jr Z (books ⟨r,inside⟩) actual
        let pins:=nodes (R:=R) live.le per (recenter o)
        let fig:=face R A (pins 1,pins 2) s.val
        let physical:=WilsonOriginalTwoFlatRoseCentered.ordinary R A N per (nodes (R:=R) live.le per o) s.val
        pins 0=0 ∧ physical=(C).omega N per fig ∧
          ∀(Y:(i:Fin 3) → (C).label (grade i).val)(turn:Fin 3 → Motion),
          (∀i,displayed R (grade i).val (Y i) (turn i)=WilsonNeutralOffsetCutoff.named R A N per i) →
          ∀K:ℕ,∀fk:f≤K,∀kn:K≤N,
          let word:=WilsonMeasuredPublicEntranceCellWords.physical R (fun i:Fin 3=>(grade i).val) Y turn
            (snap C f per (recenter o)) s (N:=N)
          fig=word ∧
            ‖physical-WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit C N per 0 word K kn) u (uf.trans fk)‖
              ≤ A₀*(wilson z r)^q:=by
  classical
  obtain ⟨A₀,nn,uniform⟩:=WilsonOriginalTwoFlatRoseFixedCourse.original F Jr Z stop fac bliss slow lead paid one ep dp books window q
  refine ⟨A₀,nn,?_⟩
  filter_upwards [uniform] with r atR
  obtain ⟨inside,uf,ears⟩:=atR
  refine ⟨inside,uf,?_⟩
  intro N per live enrolled o shape apart actual s nonempty A pins fig physical
  obtain ⟨center,value,fee,_⟩:=ears N per live enrolled o shape apart actual s.val nonempty
  refine ⟨center,value,?_⟩
  intro Y turn equal K fk kn word
  let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k))
  have zero:pins 0=0:=center
  have atOrigin:WilsonThermometerAlignedCells.atOrigin (pins 1,pins 2)=pins:=by
    funext i; fin_cases i <;> simp [WilsonThermometerAlignedCells.atOrigin,zero]
  have same:fig=word:=by
    funext U
    change (∏i∈s.val,(C).O N per (WilsonNeutralOffsetCutoff.named R A N per i)
      (WilsonThermometerAlignedCells.atOrigin (pins 1,pins 2) i) U)=_
    rw [atOrigin]
    unfold word WilsonMeasuredPublicEntranceCellWords.physical
    apply Finset.prod_congr rfl
    intro i hi
    rw [equal i]
    congr 1
    simp only [pins,WilsonOriginalTwoFlatRoseRelativePhase.nodes,anchorAt,Mix.camp,dif_pos live.le]
  refine ⟨same,?_⟩
  rw [←same]
  have cont:=WilsonOriginalTwoFlatRoseNominated.paid R A (N:=N) (per:=per) (pins 1,pins 2) s.val
  simpa only [WilsonThermometerUnitFilingCoarse.reading,
    WilsonThermometerUnitFilingCoarse.cutoff R kn (uf.trans fk) fig cont,gust_base] using fee

end YM.Integration.WilsonOriginalTwoFlatIRSocketPhase
end
