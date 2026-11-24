import YM.Integration.WilsonAddressedMixedEnrolledTrial
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonReflectedMixedThermalElection
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


omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1 ≤ ((P).budget i).supportExponent)
    (quote:Poetry (P))(D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (M:I→ℝ)(E:I→ℕ)(one:∀i,1 ≤ M i)(pwr target:ℕ):
    let t:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R t f
      ∃upper:f<K,∀(branch:I→Bool)(v:(i:I)→S.Field (d i).val),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (L i) (branch i)
      let W:=fun i=>WilsonReflectedPublicStationFare.fee F (L i) (branch i) (v i)
      (∀i,W i ≤ M i*(β f)^(E i)) → ∀N p(live:K ≤ N),WilsonAddressedMixedEnrolledTrial.Funded (R:=R) (fun i=>(d i).val) j target N p f K
        ((∑i,E i)+WilsonAddressedMixedRawTrial.power T h t D) upper live
        (fun i=>((L i).arm (branch i) (v i)).source (N,p)) M (((β f)^(2*pwr))⁻¹):=by
  classical
  intro t
  let Q:=2*pwr+∑i,E i
  filter_upwards [WilsonAddressedMixedStationPayment.original F simple bliss slow shop wide quote D target Q T h d books,
    WilsonAddressedMixedRawTrial.original F simple bliss slow D T h t d books] with r rows capital
  intro ρ span near m f K
  have beta:1 ≤ β f:=((P).fits.delayed f).le
  obtain ⟨upper,issued⟩:=rows ρ span near
  refine ⟨upper,?_⟩
  intro branch v L j W salary N p live
  obtain ⟨before,A,invs,held,earned⟩:=issued branch v N p live
  let Y:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
  let w:=fun i=>(A i).symm (fitted R (d i).val (j i) N p (Y i))
  refine ⟨before,A,invs,held,?_⟩
  intro χ cp
  have nonnegative(i:I):0 ≤ W i:=by
    have paid:=(WilsonReflectedPublicStationFare.original F (L i) (books (ρ i)).checked (branch i) (v i)).2
      N p (((before i).trans_lt upper).trans_le live)
    have nn:0 ≤ Next.UVStress.quota C (d i).val (j i) N p (Y i):=by
      unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
    exact nonneg_of_mul_nonneg_right (nn.trans paid) (pow_pos ((C).S.a_pos _) _)
  have restored(i:I):W i/χ i ≤ M i*(β f)^(E i):=(div_le_self (nonnegative i) (cp i)).trans (salary i)
  have positive(i:I):0<χ i:=zero_lt_one.trans_le (cp i)
  have cash(i:I):8*(W i/χ i)*((β f)^Q)⁻¹ ≤ 8*M i*((β f)^(2*pwr))⁻¹ :=
    WilsonAddressedPublicSourceWage.debit beta (zero_le_one.trans (one i)) (Finset.single_le_sum
      (fun k _=>Nat.zero_le (E k)) (Finset.mem_univ i)) (restored i) le_rfl
  refine ⟨?_,?_⟩
  · intro i B σ fare
    have returns:=earned i (χ i) (positive i)
    have ep:0 ≤ 8*(W i/χ i):=mul_nonneg (by norm_num) (div_nonneg (nonnegative i) (positive i).le)
    have smaller:((β f)^(Q+1))⁻¹  ≤  ((β f)^Q)⁻¹:=
      inv_anti₀ (pow_pos (zero_lt_one.trans_le beta) _) (pow_le_pow_right₀ beta (Nat.le_succ _))
    refine ⟨returns.2.1.trans ((mul_le_mul_of_nonneg_left smaller ep).trans (cash i)),?_⟩
    intro bounded
    have weight:0 ≤ WilsonAddressedPublicFiledFee.price R (d i).val:=by unfold WilsonAddressedPublicFiledFee.price;positivity
    have close:WilsonAddressedPublicFiledFee.price R (d i).val*(8*(W i/χ i))*((β f)^Q)⁻¹  ≤ 
        WilsonAddressedPublicFiledFee.price R (d i).val*fare:=by
      rw [mul_assoc];exact mul_le_mul_of_nonneg_left (cash i) weight
    obtain ⟨reg,finite,hard⟩:=returns.2.2 bounded
    exact ⟨reg.trans close,finite.trans close,hard.trans close⟩
  · have raw:=capital ρ span near branch v target N p live (fun i=>(before i).trans upper.le) A invs χ cp
    exact WilsonAddressedMixedTrialTwoIncome.joint M W χ _ E _ beta
      (WilsonReflectedOpticalStock.monotone R simple upper.le) one restored raw

end YM.Integration.WilsonReflectedMixedThermalElection
end
