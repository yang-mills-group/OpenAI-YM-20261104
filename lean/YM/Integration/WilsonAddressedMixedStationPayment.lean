import YM.Integration.WilsonAddressedMixedStationPages
import YM.Integration.WilsonAddressedPublicFiledFee
import YM.Integration.WilsonAddressedPublicSignedFare
import YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedStationPayment
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

omit [DecidableEq I] in
/-- The genuine numerical inverse and the signed lower return for every printed
    or weak arm on the same finite moving roster. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1 ≤ ((P).budget i).supportExponent)(quote:Poetry (P))
    (D target q T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R (depth (q+1) (width T h) D) f
      ∃upper:f<K,∀(branch:I→Bool)(v:(i:I)→S.Field (d i).val)(N p:ℕ)(live:K ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (L i) (branch i)
      let Y:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      let W:=fun i=>WilsonReflectedPublicStationFare.fee F (L i) (branch i) (v i)
      ∃ (before:∀i,j i ≤ f)(A:(i:I)→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i x,Arrived R (d i).val (j i) K N p target ((before i).trans upper.le) live (1/32) (A i) x) ∧
      let w:=fun i=>(A i).symm (fitted R (d i).val (j i) N p (Y i))
      (∀i o,settled R (d i).val (j i) f (K-f) N p (by rw [Nat.add_sub_of_le upper.le];exact live)
        (A i) (Y i) o) ∧
      ∀i(χ:ℝ),0<χ →
        let B:=bill R (d i).val K f (w i)
        let σ:=amplitude R (d i).val f χ
        ((C).labels.level (d i).val).coeffSize (word R (d i).val K χ (w i))  ≤ 
          4*(W i/χ)*(a (j i)/a K)^(((d i).val:ℝ)+1/32) ∧
        ‖σ‖*B  ≤  8*(W i/χ)*((β f)^(q+1))⁻¹ ∧
        (((P).budget f).supportExponent ≤ 100 →
          let pay:=WilsonAddressedPublicFiledFee.price R (d i).val*(8*(W i/χ))*((β f)^q)⁻¹
          ‖σ‖*((1+4*stock C f)*B) ≤ pay ∧ ‖σ‖*((invoice («C»:=R.family) (d i).val f p+4)*B) ≤ pay ∧ ‖σ‖*(2*B) ≤ pay):=by
  classical
  obtain ⟨low,register⟩:=WilsonAddressedMixedStationPages.original F simple shop wide quote D target (by norm_num:0<(1/32:ℝ))
  obtain ⟨k,entered⟩:=eventually_atTop.mp ((WilsonReflectedOpticalRate.original R simple slow (q+1) (width T h) D
      (by norm_num:0<(1:ℝ))).and (WilsonAddressedPublicFiledFee.original R simple slow))
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h (max low k) d books] with r range
  intro ρ span near m f K
  obtain ⟨late,placed⟩:=range ρ span near
  obtain ⟨clock,refund⟩:=entered f ((le_max_right ..).trans late)
  have upper:f<K:=clock.1
  have spanK:f+(K-f)=K:=Nat.add_sub_of_le upper.le
  refine ⟨upper,?_⟩
  intro branch v N p live L j Y W
  have before:∀i,j i ≤ f:=fun i=>(placed i (branch i)).2.1
  obtain ⟨A,invs,rows⟩:=register T d books ρ branch v f (K-f) N p (spanK.symm ▸ live)
    (fun i=>(le_max_left ..).trans (placed i (branch i)).1) before (fun i=>((before i).trans_lt upper).trans_le live)
  refine ⟨before,A,(fun i x=>by simpa only [spanK] using invs i x),fun i o=>(rows i).2 o,?_⟩
  intro i χ hp cash σ
  let e:=(d i).val
  let w:=(A i).symm (fitted R e (j i) N p (Y i))
  have head:((C).labels.level e).coeffSize w  ≤  stretch R (1/32) (j i) K*(2*(a (j i)^e*W i)):=by
    simpa only [spanK] using (rows i).1
  have hk:=hike_pos C K f rate
  have core:0 ≤ 1+4*stock C K:=by have hh:=((P).params K).columns_ge;change 1 ≤ stock C K at hh;linarith
  have thick:0<stretch R (1/32) (j i) K:=by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  have positive:0 ≤ W i:=by
    have cap:0 ≤ (stretch R (1/32) (j i) K*2*a (j i)^e)*W i:=by
      have nn:0 ≤ ((C).labels.level e).coeffSize w:=Finset.sum_nonneg fun _ _=>norm_nonneg _
      simpa only [mul_assoc] using nn.trans head
    exact nonneg_of_mul_nonneg_right cap (mul_pos (mul_pos thick (by norm_num)) (pow_pos ((C).S.a_pos _) _))
  have one:1 ≤ a (j i)/a f:=(one_le_div ((C).S.a_pos f)).mpr ((C).S.strictAnti.antitone (before i))
  have contraction:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ one (Nat.le_of_lt_succ (d i).isLt)) hk.le) core) thick.le).trans
        (clock.2.2.2 (j i) (placed i (branch i)).2.2)
  have charge:‖σ‖*cash ≤ 8*(W i/χ)*((β f)^(q+1))⁻¹:=calc
    _  ≤  _ :=WilsonAddressedPublicSignedFare.cost R hp head
    _  ≤  (2*(W i/χ))*(4*((β f)^(q+1))⁻¹):=
        mul_le_mul_of_nonneg_left contraction (mul_nonneg zero_le_two (div_nonneg positive hp.le))
    _ = _:=by ring
  refine ⟨WilsonAddressedPublicGuardFare.cost R hp head,charge,?_⟩
  intro limited
  apply refund limited e p q cash (8*(W i/χ)) σ _ charge
  have nn:0 ≤ ((C).labels.level e).coeffSize w:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  exact mul_nonneg hk.le (mul_nonneg core nn)

end YM.Integration.WilsonAddressedMixedStationPayment
end
