import YM.Integration.WilsonAddressedMixedStationPayment
import YM.Integration.WilsonAddressedPublicFiledFee
import YM.Integration.WilsonAddressedPublicSignedFare
import YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedRawTrial
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


open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators


open WilsonAddressedPublicSignedFare WilsonAddressedPublicGuardFare WilsonAddressedPublicFiledFee
open WilsonMeasuredPublicEntranceGridDebit WilsonReflectedOpticalRate
open WilsonAddressedMixedStationRange (width)


def power (T h t D:ℕ):ℕ:=(width T h+t+1)*(D+1)

omit [DecidableEq I] in
/-- Raw trial capital for any already measured inverse. Both independent layers
    of the branch selection may be made after the window is fixed. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R t f
      ∀ (branch:I→Bool)(v:(i:I)→S.Field (d i).val)(target N per:ℕ)(live:K ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (L i) (branch i)
      let Y:=fun i=>((L i).arm (branch i) (v i)).source (N,per)
      let W:=fun i=>WilsonReflectedPublicStationFare.fee F (L i) (branch i) (v i)
      ∀(before:∀i,j i ≤ K)(A:(i:I)→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i e,Arrived R (d i).val (j i) K N per target (before i) live (1/32) (A i) e) →
      ∀χ:I→ℝ,(∀i,1 ≤ χ i) → ∀i,
        let w:=(A i).symm (fitted R (d i).val (j i) N per (Y i))
        ((C).labels.level (d i).val).coeffSize (word R (d i).val K (χ i) w)  ≤ 
          4*(W i/χ i)*(β K)^(power T h t D):=by
  classical
  have opened:∀e:Fin (D+1),∀ᶠ j:ℕ in atTop,∀p,Opened C e.val j p:=fun e=>open_late C simple e.val
  obtain ⟨gate,when⟩:=eventually_atTop.mp ((Filter.eventually_all.mpr opened).and
    (WilsonAddressedCollarWindow.original R simple slow t (by norm_num:0<(1:ℝ))))
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books] with r enrolled
  intro ρ span near m f K branch v target N per live L j Y W before A fittedAt χ cp i w
  have course:=enrolled ρ span near
  have lodged:=course.2 i (branch i)
  have schedule:=(when f course.1).2
  have inTime:j i<N:=(lodged.2.1.trans_lt schedule.1).trans_le live
  let e:=(d i).val
  let x:=((C).factory e N per).terminal.symm (Y i)
  let q:=((C).factory e N per).entries (j i) x
  have received:((C).labels.level e).coeffSize q.x  ≤  a (j i)^e*W i:=
    (WilsonReflectedPublicStationFare.original F (L i) (books (ρ i)).checked (branch i) (v i)).2 N per inTime
  have pagePrice:=(size_gap e N per (j i) R.makes ((when (j i) lodged.1).1 (d i) per) inTime.le x).1
  have coast:0<stretch R (1/32) (j i) K:=by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  have head:((C).labels.level e).coeffSize w  ≤  stretch R (1/32) (j i) K*(2*(a (j i)^e*W i)):=
    ((fittedAt i (fitted R e (j i) N per (Y i))).1).trans
      (mul_le_mul_of_nonneg_left (pagePrice.trans (mul_le_mul_of_nonneg_left received zero_le_two)) coast.le)
  have enough:0 ≤ W i:=nonneg_of_mul_nonneg_right
      ((show 0 ≤ ((C).labels.level e).coeffSize q.x from Finset.sum_nonneg fun _ _=>norm_nonneg _).trans received)
      (pow_pos ((C).S.a_pos _) _)
  have base:1 ≤ β f:=((P).fits.delayed f).le
  have positive:0<χ i:=zero_lt_one.trans_le (cp i)
  have ratio:1 ≤ a (j i)/a K:=(one_le_div ((C).S.a_pos K)).mpr ((C).S.strictAnti.antitone (before i))
  have rise: a (j i)/a K ≤ (β f)^(width T h+t+1):=by
    calc
      _ = (a (j i)/a f)*(a f/a K):=by field_simp [((C).S.a_pos f).ne']
      _  ≤  (β f)^(width T h)*((β f)^t*(β f)^((1:ℝ))):=
        mul_le_mul lodged.2.2 schedule.2.2 (div_nonneg ((C).S.a_pos f).le ((C).S.a_pos K).le)
          (pow_nonneg (zero_le_one.trans base) _)
      _ = _:=by rw [Real.rpow_one,pow_succ,pow_add];ring
  have exp:((e:ℝ)+1/32) ≤ ((D+1:ℕ):ℝ):=by
    have degree:e ≤ D:=Nat.le_of_lt_succ (d i).isLt
    have de:(e:ℝ) ≤ (D:ℝ):=by exact_mod_cast degree
    push_cast;linarith
  refine (WilsonAddressedPublicGuardFare.cost R positive head).trans
    (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (div_nonneg enough positive.le)))
  calc
    _  ≤  (a (j i)/a K)^((D+1:ℕ):ℝ):=Real.rpow_le_rpow_of_exponent_le ratio exp
    _ = (a (j i)/a K)^(D+1):=Real.rpow_natCast .. 
    _  ≤  ((β f)^(width T h+t+1))^(D+1):=pow_le_pow_left₀ (zero_le_one.trans ratio) rise _
    _ = (β f)^(power T h t D):=by rw [power,pow_mul]
    _  ≤  _:=pow_le_pow_left₀ (zero_le_one.trans base) (WilsonReflectedOpticalStock.monotone R simple schedule.1.le) _

end YM.Integration.WilsonAddressedMixedRawTrial
end
