import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan
import YM.Integration.WilsonReflectedPublicStationLate
import YM.Integration.WilsonReflectedPublicStationSpan
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedStationRange
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


def width (T h:ℕ):ℕ:=2*T+3+(2*T+11+2*h)

omit [DecidableEq I] in
/-- Either branch of every issued pair, at its own physical radius, is priced
    on the same tilted outer grid. The gate precedes every finite regulator. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h gate:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      gate ≤ j ∧ ∀i b,let source:=(books (ρ i)).rows (d i)
        let k:=station F source b
        gate ≤ k ∧ k ≤ j ∧ a k/a j  ≤  (β j)^(width T h):=by
  classical
  obtain ⟨ε,ep,check⟩:=Metric.mem_nhdsWithin_iff.mp
    ((WilsonReflectedPublicStationLate.original F simple bliss T gate).and
      (WilsonReflectedPublicStationSpan.original F simple bliss T))
  have near:=longer F simple bliss h
  filter_upwards [near.eventually ((gt_mem_nhds ep).filter_mono nhdsWithin_le_nhds),
    WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books] with r thin charged
  intro ρ span close m j
  have payments:=charged ρ span close
  have each (i:I)(b:Bool):
      let book:=books (ρ i)
      let M:=max book.stock.j book.W.k
      let k:=station F (book.rows (d i)) b
      gate ≤ k ∧ k ≤ j ∧ a k/a j  ≤  (β j)^(width T h):=by
    intro book M k
    have small:=check ((show (ρ i).val∈Metric.ball (0:ℝ) ε ∩ Set.Ioi 0 from ⟨by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i).property.1] using
        ((span i).2.trans_lt thin), (ρ i).property.1⟩))
    have born:=small.1 (book.rows (d i)) book.checked book.active b
    have ratio:=small.2 (book.rows (d i)) book.checked book.active b
    have km:k ≤ M:=by cases b<;>simp [k,M,WilsonReflectedPublicStationFare.station]
    have mj:M ≤ j:=(payments.2 i).1
    have atR:a M ≤ (ρ i).val:=((C).S.strictAnti.antitone (le_max_right ..)).trans
      ((WilsonReflectedPublicBulbBerth.mesh R book.W book.checked).trans book.active.le)
    have pj:0<a j:=(C).S.a_pos _
    have pos:0 ≤ β j:=(zero_lt_one.trans ((P).fits.delayed j)).le
    have grow:β M ≤ β j:=WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le mj
    refine ⟨born,km.trans mj,?_⟩
    calc
      a k/a j = (a k/a M)*(a M/a j):=by field_simp [(C).S.a_pos M |>.ne']
      _  ≤  (β j)^(2*T+3)*(β j)^(2*T+11+2*h):=by
        apply mul_le_mul (ratio.trans (pow_le_pow_left₀ (zero_lt_one.trans ((P).fits.delayed M)).le grow _))
          ((div_le_iff₀ pj).mpr (atR.trans ((payments.2 i).2))) (div_nonneg ((C).S.a_pos _).le pj.le) (pow_nonneg pos _)
      _ = _:= (pow_add ..).symm
  obtain ⟨i,_⟩:=close
  exact ⟨(each i false).1.trans (each i false).2.1,each⟩

end YM.Integration.WilsonAddressedMixedStationRange
end
