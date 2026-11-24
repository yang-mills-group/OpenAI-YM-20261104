import YM.Integration.WilsonMovingForkWeakPrice
import YM.Integration.WilsonAddressedMixedNamedIncome
import YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkHomeIncome
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


omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (D T h:ℕ)(d:I→Fin (D+1))
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃amount:I→ℝ,∃expo:I→ℕ,(∀i,1 ≤ amount i) ∧
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∀(branch:I→Bool)(i:I),let L:=(books (ρ i)).rows (d i)
        let v:=WilsonPositionHomogeneousFrame.homogeneous F Jr Z (ρ i).val (d i).val (x i)
        let W:=WilsonReflectedPublicStationFare.fee F L (branch i) v
        0 ≤ W ∧ W ≤ amount i*(β f)^(expo i) ∧
          WilsonOriginalTwoFlatPublicFare.charge F L f (branch i) v ≤ amount i*(β f)^(expo i):=by
  classical
  obtain ⟨M₀,e₀,mp,pooled⟩:=WilsonAddressedMixedNamedIncome.original F Jr Z simple bliss slow lead paid D T h d (fun _=>0) x books
  choose M₁ e₁ xp filed using fun i:I=>WilsonMovingForkWeakPrice.original F Jr Z simple bliss lead paid (d i).val (x i)
  let reach(i:I):=WilsonAddressedMixedStationRange.width T h*((d i).val+1)
  let M(i:I):=max (M₀ i) (2*M₁ i)
  let expo(i:I):=max (e₀ i) (reach i+e₁ i)
  have mpos(i:I):1≤M i:=(mp i).trans (le_max_left ..)
  refine ⟨M,expo,mpos,?_⟩
  obtain ⟨ε,ep,arrives⟩:=Metric.mem_nhdsWithin_iff.mp (eventually_all.mpr filed)
  filter_upwards [pooled,WilsonAddressedMixedStationRange.original F simple bliss slow D T h 0 d books,
    (longer F simple bliss h).eventually ((gt_mem_nhds ep).filter_mono nhdsWithin_le_nhds)] with r pool crop small
  intro ρ span near m f branch i L v W
  have beta:1≤β f:=((P).fits.delayed f).le
  have bp:0≤β f:=zero_le_one.trans beta
  obtain ⟨_,_,sizes⟩:=
    ((crop ρ span near).2 i (branch i))
  cases flag:branch i with
  | false =>
    obtain ⟨nn,raw,converted⟩:=pool ρ span near (fun _=>false) i
    have larger:M₀ i*(β f)^(e₀ i)≤M i*(β f)^(expo i):=
      mul_le_mul (le_max_left ..) (pow_le_pow_right₀ beta (le_max_left ..)) (pow_nonneg bp _) (zero_le_one.trans (mpos i))
    exact ⟨by simpa only [flag,W,v,L,WilsonOriginalTwoFlatPublicNamedFare.chosen,Bool.false_eq_true,reduceIte] using nn,
      by simpa only [flag,W,v,L,WilsonOriginalTwoFlatPublicNamedFare.chosen,Bool.false_eq_true,reduceIte] using raw.trans larger,
      by simpa only [flag,W,v,L,WilsonOriginalTwoFlatPublicNamedFare.chosen,Bool.false_eq_true,reduceIte] using converted.trans larger⟩
  | true =>
    have fine:(ρ i).val∈Metric.ball (0:ℝ) ε ∩ Ioi 0:=⟨by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i).property.1] using (span i).2.trans_lt small,(ρ i).property.1⟩
    have late:(books (ρ i)).W.k≤f:=by
      simpa only [flag,WilsonReflectedPublicStationFare.station,if_true] using ((crop ρ span near).2 i (branch i)).2.1
    have weak:=arrives fine i L (books (ρ i)).checked (books (ρ i)).active (window _ (d i)) f late
    have pos:0≤W:=by
      have tapped:=(WilsonReflectedPublicStationFare.original F L (books (ρ i)).checked true v).2
        (f+1) 0 (late.trans_lt (Nat.lt_succ_self _))
      have norm:0≤Next.UVStress.quota C (d i).val (books (ρ i)).W.k (f+1) 0 ((L.arm true v).source (f+1,0)):=by
        unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
      rw [show W=WilsonReflectedPublicStationFare.fee F L true v by simp only [W,flag]]
      exact nonneg_of_mul_nonneg_right (norm.trans tapped) (pow_pos ((C).S.a_pos _) _)
    have rel:=pow_le_pow_left₀ (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) sizes ((d i).val+1)
    rw [←pow_mul] at rel
    have sum:M₁ i*(β f)^(e₁ i)≤M i*(β f)^(expo i):=
      mul_le_mul ((show M₁ i≤2*M₁ i by linarith [xp i]).trans (le_max_right ..))
        (pow_le_pow_right₀ beta ((Nat.le_add_left _ _).trans (le_max_right ..))) (pow_nonneg bp _) (zero_le_one.trans (mpos i))
    refine ⟨pos,by simpa only [W,flag] using weak.trans sum,max_le ?_ ?_⟩
    · exact one_le_mul_of_one_le_of_one_le (mpos i) (one_le_pow₀ beta)
    · rw [←flag]
      change 2*(a (WilsonReflectedPublicStationFare.station F L (branch i))/a f)^((d i).val+1)*W≤_
      have wb:W≤M₁ i*(β f)^(e₁ i):=by simpa only [W,flag] using weak
      calc
        _≤(2*(β f)^(reach i))*(M₁ i*(β f)^(e₁ i)):=mul_le_mul (mul_le_mul_of_nonneg_left rel zero_le_two) wb pos (by positivity)
        _=(2*M₁ i)*(β f)^(reach i+e₁ i):=by rw [pow_add];ring
        _≤_:=mul_le_mul (le_max_right ..) (pow_le_pow_right₀ beta (le_max_right ..)) (pow_nonneg bp _) (zero_le_one.trans (mpos i))

end YM.Integration.WilsonMovingForkHomeIncome
end
