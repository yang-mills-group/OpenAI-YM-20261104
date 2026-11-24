import YM.Integration.WilsonAddressedMixedStationRange
import YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedNamedIncome
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
    (D T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃amount:I→ℝ,∃expo:I→ℕ,(∀i,1 ≤ amount i) ∧
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∀(branch:I→Bool)(i:I),let L:=(books (ρ i)).rows (d i)
        let v:=chosen F Jr Z (ρ i).val ((books (ρ i)).V (d i)) (branch i) (y i) (x i)
        let W:=WilsonReflectedPublicStationFare.fee F L (branch i) v
        0 ≤ W ∧ W ≤ amount i*(β f)^(expo i) ∧
          WilsonOriginalTwoFlatPublicFare.charge F L f (branch i) v ≤ amount i*(β f)^(expo i):=by
  classical
  choose amount power one offered using fun i=>WilsonOriginalTwoFlatPublicNamedFare.original F Jr Z simple bliss lead paid
    (d i).val T (y i) (x i)
  let k:=2*T+11+2*h
  obtain ⟨ε,ep,ask⟩:=Metric.mem_nhdsWithin_iff.mp (Filter.eventually_all.mpr offered)
  refine ⟨amount,fun i=>(2*T+3+k)*((d i).val+1)+power i,one,?_⟩
  filter_upwards [(longer F simple bliss h).eventually ((gt_mem_nhds ep).filter_mono nhdsWithin_le_nhds),
    WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books] with r close supplied
  intro ρ span near m f branch i L v W
  have small:(ρ i).val∈Metric.ball (0:ℝ) ε ∩ Set.Ioi 0:=⟨by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i).property.1] using (span i).2.trans_lt close,
    (ρ i).property.1⟩
  have house:=((supplied ρ span near).2 i)
  have original:=ask small i L (books (ρ i)).checked (books (ρ i)).active f k house.1 house.2 (branch i)
  let j:=WilsonReflectedPublicStationFare.station F L (branch i)
  have born:j ≤ f:=by
    have left:j ≤ max (books (ρ i)).stock.j (books (ρ i)).W.k:=by
      cases value : branch i <;> simp [j,WilsonReflectedPublicStationFare.station,value]
    exact left.trans house.1
  have sale:=(WilsonReflectedPublicStationFare.original F L (books (ρ i)).checked (branch i) v).2
      (f+1) 0 (born.trans_lt (Nat.lt_succ_self _))
  have nn:0 ≤ Next.UVStress.quota C (d i).val j (f+1) 0 ((L.arm (branch i) v).source (f+1,0)):=by
    unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
  have enough:0 ≤ W:=nonneg_of_mul_nonneg_right (nn.trans sale) (pow_pos ((C).S.a_pos j) _)
  have ratio:1 ≤ a j/a f:=(one_le_div ((C).S.a_pos f)).mpr ((C).S.strictAnti.antitone born)
  have reserve:1 ≤ 2*(a j/a f)^((d i).val+1):=one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ ratio)
  have originalW:W ≤ WilsonOriginalTwoFlatPublicFare.charge F L f (branch i) v:=
    (le_mul_of_one_le_left enough reserve).trans (le_max_right ..)
  exact ⟨enough,originalW.trans original,original⟩

end YM.Integration.WilsonAddressedMixedNamedIncome
end
