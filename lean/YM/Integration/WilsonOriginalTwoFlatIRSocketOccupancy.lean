import YM.Integration.WilsonOriginalTwoFlatIRSocketAbsolute
import YM.Integration.WilsonCenteredReaderDomain
import YM.Integration.WilsonMeasuredPublicEntranceProfileSites
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketOccupancy
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
    {T:ℕ}{δ:ℝ}(dp:0<δ)
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)) (φ:Test 3)(q:ℕ):
    ∃A₀:ℝ,0≤A₀ ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,(∀i:Fin 3,(C).ref (grade i).val ≤ N) →
        ∃site:WilsonCenteredPhysicalPanel.Sites R (f,per) 3 → Fin 3 → Cover,
        (∀p,snap C f per (site p)=p) ∧ ∀p:WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per),
      ∀(actual:Next.UVStress.Lifts C (books ⟨r,inside⟩).k)(s:(Stock.census (Fin 3)).Mode),s.val.Nonempty →
        let A:=group F Jr Z (books ⟨r,inside⟩) actual
        let relative:=nodes (R:=R) live.le per (recenter (site p.val))
        let observed:=(C).omega N per (face R A (relative 1,relative 2) s.val)
        ∀(Y:(i:Fin 3) → (C).label (grade i).val)(turn:Fin 3 → Motion),
        (∀i,displayed R (grade i).val (Y i) (turn i)=WilsonNeutralOffsetCutoff.named R A N per i) →
        ∀K:ℕ,∀fk:f≤K,∀kn:K≤N,
          let word:=WilsonMeasuredPublicEntranceCellWords.physical R (fun i:Fin 3=>(grade i).val) Y turn
            p.val s (N:=N)
          (C).omega N per word=observed ∧
            ‖observed-WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit C N per 0 word K kn) u (uf.trans fk)‖
              ≤ A₀*(wilson z r)^q:=by
  classical
  obtain ⟨M,mp,η,ep,housed⟩:=WilsonCenteredReaderDomain.room φ
  have shape:∀x:Points 3,φ x≠0 → (∀i,‖x i‖≤M) ∧ Pairwise fun i j=>η≤‖x i-x j‖:=by
    intro x hit
    have housed₁:=housed 1 zero_lt_one x (subset_closure hit)
    exact ⟨fun i=>by simpa using housed₁.span i,fun i j ne=>by simpa using housed₁.spaced i j ne⟩
  obtain ⟨A₀,apos,school⟩:=WilsonOriginalTwoFlatIRSocketAbsolute.original F Jr Z stop fac bliss slow lead paid
    (by linarith:1≤M+1) (half_pos ep) dp books window q
  have HG:=wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies
  have thresh:(0:ℝ)^2 < min 1 (η/4)/12:=by rw [zero_pow (by decide:2≠0)]; exact div_pos (lt_min zero_lt_one (by positivity)) (by norm_num)
  have small:=((HG.conforms fac.simpleGate).pow 2).eventually (ge_mem_nhds thresh)
  have mesh:=WilsonOriginalTwoFlatPublicMixedMesh.original F fac.simpleGate bliss slow 6 T 0 (fun i:Fin 3=>grade i) books
  refine ⟨A₀,apos,?_⟩
  filter_upwards [school,small,mesh] with r took thin table
  obtain ⟨inside,uf,node⟩:=took
  let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k))
  have width:(C).S.a f/r≤(wilson z r)^2:=(table (fun _=>⟨r,inside⟩)
    (fun _=>⟨le_rfl,by simp [outer]⟩) ⟨0,rfl⟩).1
  have debt:(C).S.a f ≤ min 1 (η/4)/12*r:=(div_le_iff₀ inside.1).mp (width.trans thin)
  have first:=mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (η/4)) inside.1.le
  have second:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (η/4)) inside.1.le
  have small₁:4*(3:ℝ)*(C).S.a f≤r:=by linarith only [debt,first]
  have small₂:4*(3:ℝ)*(C).S.a f≤η/4*r:=by linarith only [debt,second]
  refine ⟨inside,uf,?_⟩
  intro N per live ready
  obtain ⟨site,registered,licence⟩:=WilsonMeasuredPublicEntranceProfileSites.lifted R φ (per:=per) inside.1 shape small₁ small₂
  refine ⟨site,registered,?_⟩
  intro p
  have receipt:=licence p.val (WilsonReceivedChronologicalFixedRoseVariation.charged R φ r (f,per) p)
  have pay:=node N per live ready (site p.val) receipt.1 receipt.2
  intro actual s used A relative observed Y turn axes K fk kn word
  let upper:=WilsonMeasuredPublicEntranceCellWords.physical R (fun i:Fin 3=>(grade i).val) Y turn
    (snap C f per (site p.val)) s (N:=N)
  have earned:(C).omega N per upper=observed ∧
      ‖observed-WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit C N per 0 upper K kn) u (uf.trans fk)‖
        ≤ A₀*(wilson z r)^q:=pay actual s used Y turn axes K fk kn
  have same:upper=word:=congrArg (fun (placed:WilsonCenteredPhysicalPanel.Sites R (f,per) 3) =>
    WilsonMeasuredPublicEntranceCellWords.physical R (fun i:Fin 3=>(grade i).val) Y turn placed s (N:=N)) (registered p.val)
  exact same ▸ earned

end YM.Integration.WilsonOriginalTwoFlatIRSocketOccupancy
end
