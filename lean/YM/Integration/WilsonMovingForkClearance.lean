import YM.Integration.WilsonMovingForkSlotDate
import YM.Integration.WilsonAddressedPublicGridRooms
import YM.Integration.WilsonOriginalTwoFlatGrid

noncomputable section
namespace YM.Integration.WilsonMovingForkClearance
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

/-- Strict torus separation for the deposited original joint record, at every
admissible period and on the very same points used by the continuum optical node. -/
theorem snapped {E:Type}{j N p:ℕ}(deep:j ≤ N)(o:E → Lattice.Cover)
    (insideRoot:∀i,‖(C).S.gridPoint j (o i)‖≤1/8)
    (apart:Pairwise fun i k=>2*a_ j*(((C).path.levels.budget j).B:ℝ)^2 <
       ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o k)‖):
    ∀i k:E,i≠k→((C).path.levels.budget j).B^2 <
      separation (point R (N:=N) 0 (1,false) (snap C j p o i) j)
        (point R (N:=N) 0 (1,false) (snap C j p o k) j):=by
  intro i k distinct
  rw [WilsonAddressedPublicGridRooms.position R deep,WilsonAddressedPublicGridRooms.position R deep]
  have cost:=(normC (C) j p (wrap ((C).side j p) (o i-o k))).2
  have compact:‖(C).S.gridPoint j (o i-o k)‖≤1:=by
    rw [Frontier6.Road.grid_sub (C) j]
    exact (norm_sub_le ..).trans ((add_le_add (insideRoot i) (insideRoot k)).trans (by norm_num))
  rw [inside (C) j p compact,Frontier6.Road.grid_sub (C) j,map_sub] at cost
  simp only [separation,sub_zero] at cost
  exact_mod_cast (lt_of_mul_lt_mul_left ((apart distinct).trans_le cost) (mul_nonneg zero_le_two ((C).S.a_pos j).le))

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ){δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {M η:ℝ}(_mp:0<M)(ep:0<η):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
    (∃i,(ρ i).val=r) →
    let j:=reporter F book ρ
    ∀{E:Type}{N p:ℕ},j ≤ N → ∀o:E → Lattice.Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
    (Pairwise fun i k=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o k)‖) →
    ∀i k:E,i≠k→((C).path.levels.budget j).B^2 <
      separation (point R (N:=N) 0 (1,false) (snap C j p o i) j)
        (point R (N:=N) 0 (1,false) (snap C j p o k) j):=by
  classical
  obtain ⟨gate,room⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatPublicGeometry.clearance (R:=R) simple slow (η:=η/2) (half_pos ep))
  have long:=longer F simple bliss h
  have tail:Tendsto (fun r=>M*outer z h r) trail (𝓝 (0:ℝ)):=by
    simpa using (tendsto_const_nhds (x:=M)).mul (tendsto_nhdsWithin_iff.mp long).1
  filter_upwards [self_mem_nhdsWithin (a:=0), (ge_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds,
    tail.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/8))] with r rp past small
  intro ρ bounds near j E N p deep o placed apart
  obtain ⟨i,anchor⟩:=near
  let m:=univ.sup fun i=>max (book (ρ i)).stock.j (book (ρ i)).W.k
  have fine:(book (ρ i)).W.k ≤ m:=(le_max_right ..).trans
    (Finset.le_sup (f:=fun k:I=>max (book (ρ k)).stock.j (book (ρ k)).W.k) (mem_univ i))
  have tight:a_ m ≤ r:=((C).S.strictAnti.antitone fine).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (book (ρ i)).checked).trans (book (ρ i)).active.le).trans anchor.le)
  have high:gate ≤ m:=by
    by_contra! early;exact (not_lt_of_ge (tight.trans past)) ((C).S.strictAnti early)
  have clear:=room m high
  apply snapped deep o (fun i=>(placed i).trans small)
  intro i k diff
  refine lt_of_le_of_lt clear ((lt_of_le_of_lt (mul_le_mul_of_nonneg_left tight (half_pos ep).le) ?_).trans_le (apart diff))
  exact mul_lt_mul_of_pos_right (half_lt_self ep) rp

end YM.Integration.WilsonMovingForkClearance
end
