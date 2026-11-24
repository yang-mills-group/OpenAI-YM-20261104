import YM.Integration.WilsonSeparatedPrefixCellProfile
import YM.Integration.WilsonMovingForkClearance
import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan
import YM.Integration.WilsonOriginalTwoFlatPublicOuter
import YM.Integration.WilsonOriginalTwoFlatGridRadius

noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCellHousing
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare WilsonMovingForkRawSeed
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolShell (radius)
open WilsonThermometerUnitFilingFourPoolClock (invoice longer)
open GapsContact.Seams GapsContact.Ascent WilsonMeasuredPublicSlots
local notation "a_" => R.family.S.a


open MergeProof
open Ribbons Accent Cells Extra.Histories
open WilsonThermometerReflectedTrajectory


open WilsonAddressedPhysicalCells
open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff

omit [DecidableEq I] in
/-- For all occupied cells of the correlated profile the same bounded older
housing date is fixed before the period and microscopic cutoff. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h n:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(L:ℝ)(lp:0<L):
    ∃window:ℕ,∀gate:ℕ,∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∃j:ℕ,gate≤j ∧ j+2≤f ∧ (a_ j)/(a_ f)≤(β f)^window ∧
        8*(L*outer z h r+4*(n:ℝ)*(a_ f))≤a_ (j+1):=by
  classical
  let cap:=8*(L+4*(n:ℝ))+2
  have capOne:1<cap:=by dsimp [cap];nlinarith only [lp,show 0≤(n:ℝ) by positivity]
  have capPos:0<cap:=zero_lt_one.trans capOne
  obtain ⟨floor,quote⟩:=eventually_atTop.mp ((hat_rate (C).path.levels simple).eventually_ge_atTop cap)
  let b:=2*T+11+2*h
  refine ⟨b+2*h+3,?_⟩
  intro gate
  have eventualSmall:∀ᶠr in trail,outer z h r≤(a_ (gate+3))/cap:=
    (longer F simple bliss h).eventually ((ge_mem_nhds (div_pos ((C).S.a_pos _) capPos)).filter_mono nhdsWithin_le_nhds)
  have rFine:∀ᶠr in trail,r≤a_ floor:=(ge_mem_nhds ((C).S.a_pos floor)).filter_mono nhdsWithin_le_nhds
  filter_upwards [WilsonOriginalTwoFlatPublicMixedSpan.original (I:=I) F simple bliss slow D T h d books,
    WilsonOriginalTwoFlatPublicOuter.original F simple bliss h,eventualSmall,rFine] with r mesh clock small₀ tiny ρ band hits f
  obtain ⟨i,eq⟩:=hits
  obtain ⟨ar,panel⟩:=mesh ρ band ⟨i,eq⟩
  have young:a_ f≤r:=ar
  have rate:r≤(β f)^b*(a_ f):=by rw [←eq];exact (panel i).2
  have hot:cap≤β f:=quote f ((C).S.strictAnti.le_iff_ge.mp (young.trans tiny))
  let reach:=outer z h r
  have rp:0<reach:=clock.1.trans_le clock.2.1
  have weighted:reach≤(β f)^(2*h)*r:=clock.2.2 f young
  have bp:0≤β f:=capPos.le.trans hot
  have toll:cap*reach≤(β f)^(b+2*h+1)*(a_ f):=calc
    cap*reach≤β f*((β f)^(2*h)*r):=mul_le_mul hot weighted rp.le bp
    _ ≤ β f*((β f)^(2*h)*((β f)^b*(a_ f))):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left rate (pow_nonneg bp _)) bp
    _ = _:=by rw [pow_succ,pow_add];ring
  have tiny':cap*reach≤a_ (gate+3):=by simpa only [mul_comm cap] using (le_div_iff₀ capPos).mp small₀
  have fine:a_ f<cap*reach:=calc
    a_ f≤reach:=young.trans clock.2.1
    _ < cap*reach:=by simpa only [one_mul] using (mul_lt_mul_of_pos_right capOne rp)
  obtain ⟨before,after,contained,price⟩:=WilsonOriginalTwoFlatGridRadius.fitted R simple slow (u:=gate) (j:=f) (B:=b+2*h+1)
    (mul_pos capPos rp) tiny' fine toll
  refine ⟨_,before,by omega,(div_le_iff₀ ((C).S.a_pos f)).mpr price,?_⟩
  apply le_trans _ contained
  have bill:=mul_le_mul_of_nonneg_left (young.trans clock.2.1) (show 0≤4*(n:ℝ) by positivity)
  dsimp [cap,reach] at *
  nlinarith only [bill,rp.le]

end YM.Integration.WilsonSeparatedPrefixCellHousing
end
