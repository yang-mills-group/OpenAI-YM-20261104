import YM.Integration.WilsonAddressedMixedRawTrial
import YM.Integration.WilsonAddressedMixedNamedIncome
import YM.Integration.WilsonAddressedMixedStationPayment
import YM.Integration.WilsonAddressedPublicGuardCapital
import YM.Integration.WilsonAddressedPublicSourceWage
import YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedTrialTwoIncome
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
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
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



open WilsonAddressedMixedStationRange (width)
open WilsonMeasuredPublicEntranceGridDebit (fitted bill settled)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedPublicSignedFare (amplitude)
open WilsonAddressedPublicGuardFare (word)
open OPE.Therm (Poetry)


open WilsonAddressedMixedRawTrial (power)

theorem joint {I:Type} [Fintype I][Nonempty I] (M W E' X:I→ℝ)(e:I→ℕ)(s:ℕ){H₀ H₁:ℝ}
    (base:1 ≤ H₀)(rising:H₀ ≤ H₁)(one:∀i,1 ≤ M i)(paid:∀i,W i/E' i ≤ M i*H₀^(e i))
    (raw:∀i,X i ≤ 4*(W i/E' i)*H₁^s):
    ∀i,X i ≤ max 1 (4*∑i,M i)*H₁^((∑i,e i)+s):=by
  intro i
  have first:0 ≤ H₀:=zero_le_one.trans base
  have second:1 ≤ H₁:=base.trans rising
  have M₀:0 ≤ M i:=zero_le_one.trans (one i)
  have total:M i ≤ ∑j,M j:=Finset.single_le_sum (fun k _=>zero_le_one.trans (one k)) (Finset.mem_univ i)
  have degree:e i ≤ ∑j,e j:=Finset.single_le_sum (fun k _=>Nat.zero_le _) (Finset.mem_univ i)
  have shift:H₀^(e i) ≤ H₁^(∑j,e j):=(pow_le_pow_left₀ first rising _).trans (pow_le_pow_right₀ second degree)
  calc
    _  ≤  _:=raw i
    _  ≤  4*(M i*H₀^(e i))*H₁^s:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (paid i) (by norm_num))
      (pow_nonneg (zero_le_one.trans second) _)
    _  ≤  4*((∑j,M j)*H₁^(∑j,e j))*H₁^s:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul total shift (pow_nonneg first _) (M₀.trans total)) (by norm_num)) (pow_nonneg (zero_le_one.trans second) _)
    _ = (4*∑j,M j)*H₁^((∑j,e j)+s):=by rw [pow_add];ring
    _  ≤  _:=mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans second) _)

omit [DecidableEq I] in
/-- Raw guard funding, in the form accepted by the original counted two-source
    hearing, for independently dated members of the actual public family. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (D T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃B:ℝ,0<B ∧ ∃e:ℕ,∀t:ℕ,∀ᶠ r in trail,
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R t f
      ∀(branch:I→Bool)(target N p:ℕ)(live:K ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let v:=fun i=>chosen F Jr Z (ρ i).val ((books (ρ i)).V (d i)) (branch i) (y i) (x i)
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (L i) (branch i)
      let Y:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      ∀(before:∀i,j i ≤ K)(A:(i:I)→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i q,Arrived R (d i).val (j i) K N p target (before i) live (1/32) (A i) q) →
      ∀χ:I→ℝ,(∀i,1 ≤ χ i)→∀i,let w:=(A i).symm (fitted R (d i).val (j i) N p (Y i))
        ((C).labels.level (d i).val).coeffSize
          ((((χ i:ℝ):ℂ)⁻¹*((a K:ℂ)^(d i).val)⁻¹) • w)  ≤  B*(β K)^(e+power T h t D):=by
  classical
  obtain ⟨M,E,one,fields⟩:=WilsonAddressedMixedNamedIncome.original F Jr Z simple bliss slow lead paid D T h d y x books
  refine ⟨max 1 (4*∑i,M i),zero_lt_one.trans_le (le_max_left ..),∑i,E i,?_⟩
  intro t
  filter_upwards [fields,WilsonAddressedMixedRawTrial.original F simple bliss slow D T h t d books] with r arrived registered
  intro ρ span near m f K branch target N p live L v j Y before A fits χ cp
  let W:=fun i=>WilsonReflectedPublicStationFare.fee F (L i) (branch i) (v i)
  have hired:=arrived ρ span near branch
  have raw:=registered ρ span near branch v target N p live before A fits χ cp
  have bill' (i:I):W i/χ i ≤ M i*(β f)^(E i):=(div_le_self (hired i).1 (cp i)).trans (hired i).2.1
  exact joint M W χ _ E _ ((P).fits.delayed f).le (WilsonReflectedOpticalStock.monotone R simple
    (WilsonInvariantActionPosition.arrival R t f).1.le) one bill' raw

end YM.Integration.WilsonAddressedMixedTrialTwoIncome
end
