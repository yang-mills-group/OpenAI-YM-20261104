import YM.Integration.WilsonOlderFreshSoftSocketStationPair
import YM.Integration.WilsonOriginalObservedRoseVanePurse

/-! The originally filed weak Rose book, including its actual common field change. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicWages
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
open private wrapped from YM.Integration.WilsonOriginalObservedRoseVanePurse

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P)):
    ∃(W:Fin 3→ℝ)(e:Fin 3→ℕ),(∀i,0≤W i) ∧ ∀ᶠr in trail,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),
    WilsonMovingForkWindowBooks.Priced F B → ∀actual:Next.UVStress.Lifts (C) B.k,
    ∀N per K:ℕ,B.W.k<N → B.W.k≤K → ∀i:Fin 3,
    variation R ages B.W.k N per i (WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i)*(a B.W.k)^ages i≤W i*(β K)^(e i+1):=by
  obtain ⟨M,e,one,booked⟩:=WilsonOlderFreshSoftSocketStationPair.original F Jr Z simple bliss lead obedient shop cap quote
  have wrapped_fee(i:Fin 3):=wrapped R simple slow upper (ages i)
  choose width widthpos enrolled using wrapped_fee
  obtain ⟨floor,allWidths⟩:=eventually_atTop.mp (Filter.eventually_all.mpr enrolled)
  let orb i:=orbitCost ((C).labels.level (ages i))
  have orbpos(i:Fin 3):0≤orb i:=zero_le_one.trans (orbitCost_one_le _)
  refine ⟨fun i=>2*orb i*(width i*M i),e,fun i=>mul_nonneg (mul_nonneg (by norm_num) (orbpos i)) (mul_nonneg (widthpos i) (zero_le_one.trans (one i))),?_⟩
  filter_upwards [booked 0 (show (0:ℝ)<1 by norm_num),(ge_mem_nhds ((C).S.a_pos floor)).filter_mono nhdsWithin_le_nhds] with r registers tiny
  intro T B paid actual N per K deep before i
  let k:=B.W.k
  have late:floor≤k:=by
    by_contra! earlier
    have mesh:a k≤r:=(WilsonReflectedPublicBulbBerth.mesh R B.W B.checked).trans B.active.le
    exact (not_le_of_gt ((C).S.strictAnti earlier)) (mesh.trans tiny)
  let y:=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i
  let v:=homogeneous F Jr Z r (grade i) (source (C) univ i)
  have price:=(WilsonReflectedPublicStationFare.original F (B.rows (grade i)) B.checked true v).2 N per deep
  rw [(B.rows (grade i)).weak] at price
  have physical:Next.UVStress.quota (C) (ages i) k N per y≤amount F Jr Z B i:=price
  have quota:Next.UVStress.quota (C) (ages i) k N per y≤M i*β K^e i:=
    physical.trans ((registers B paid actual).2.2 K before i)
  have nonnegative:0≤Next.UVStress.quota R.family (ages i) k N per y:=by
    unfold Next.UVStress.quota Frame.coeffSize;exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  obtain ⟨wn,wb⟩:=allWidths k late i K before
  have mesh:0≤a k^(ages i):=(pow_pos ((R.family).S.a_pos k) _).le
  calc variation R ages k N per i y*(a k)^ages i=
        |2*orb i*((1+wrapCost R (ages i) k)*
            (Next.Rank.Spindle.paid R.family (ages i) k N per y*(a k)^ages i))|:=by
           unfold WilsonOriginalObservedRoseMeshHeight.variation
           rw [←abs_of_nonneg mesh,←abs_mul]
           congr 1;simp only [orb,abs_of_nonneg mesh];ring
       _=2*orb i*((1+wrapCost R (ages i) k)*Next.UVStress.quota R.family (ages i) k N per y):=by
          rw [WilsonMatrixTicketLanesQuota.quota,abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (orbpos i)) (mul_nonneg wn nonnegative))]
       _≤2*orb i*((width i*β K)*(M i*β K^e i)):=mul_le_mul_of_nonneg_left
          (mul_le_mul wb quota nonnegative (mul_nonneg (widthpos i) (zero_lt_one.trans ((P).fits.delayed K)).le)) (mul_nonneg (by norm_num) (orbpos i))
       _=(2*orb i*(width i*M i))*(β K)^(e i+1):=by rw [pow_succ];ring

end YM.Integration.WilsonOriginalObservedRosePublicWages
end
