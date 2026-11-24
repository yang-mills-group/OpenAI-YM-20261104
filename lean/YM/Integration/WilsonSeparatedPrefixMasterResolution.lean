import YM.Integration.WilsonMovingForkClearance

/-! The genuine reporter resolves the minimum physical separation independently of the absolute translation. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMasterResolution
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

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T:ℕ){δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) H z D T s.val)
    {η:ℝ}(ep:0<η):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∃i,(ρ i).val=r) →
    let j:=reporter F book ρ
    2*a_ j*(((C).path.levels.budget j).B:ℝ)^2 < η*r:=by
  classical
  obtain ⟨gate,room⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatPublicGeometry.clearance (R:=R) simple slow (η:=η/2) (half_pos ep))
  filter_upwards [self_mem_nhdsWithin (a:=0), (ge_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds]
    with r rp past ρ near j
  obtain ⟨i,anchor⟩:=near
  let m:=univ.sup fun i=>max (book (ρ i)).stock.j (book (ρ i)).W.k
  have fine:(book (ρ i)).W.k ≤ m:=(le_max_right ..).trans
    (Finset.le_sup (f:=fun k:I=>max (book (ρ k)).stock.j (book (ρ k)).W.k) (mem_univ i))
  have tight:a_ m ≤ r:=((C).S.strictAnti.antitone fine).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (book (ρ i)).checked).trans (book (ρ i)).active.le).trans anchor.le)
  have high:gate ≤ m:=by
    by_contra! early;exact (not_lt_of_ge (tight.trans past)) ((C).S.strictAnti early)
  have clear:=room m high
  exact lt_of_le_of_lt (room m high) ((mul_le_mul_of_nonneg_left tight (half_pos ep).le).trans_lt (mul_lt_mul_of_pos_right (half_lt_self ep) rp))

end YM.Integration.WilsonSeparatedPrefixMasterResolution
end
