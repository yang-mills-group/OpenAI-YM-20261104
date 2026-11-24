import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

noncomputable section
namespace YM.Integration.WilsonMovingForkSlotDate
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
local notation "a" => R.family.S.a

def slot {s:ℝ}{D T:ℕ}(b:Book F (l:=l) H z D T s)(d:Fin (D+1))(v:S.Field d.val):
    WilsonMeasuredPublicSlots.Slot F l d.val v (radius z T s) (dock (radius z T s)^T):=
  (b.stock.department d.val (Nat.le_of_lt_succ d.isLt)).print v

theorem source {s:ℝ}{D T:ℕ}(b:Book F (l:=l) H z D T s)(d:Fin (D+1))(v:S.Field d.val):
    (slot F b d v).j=b.stock.j ∧ (slot F b d v).arm=(b.rows d).arm false v:=
  ⟨((b.stock.department d.val _).dated v).1,((b.rows d).pooled v).symm⟩

theorem berth_width (simple:G.Simple)(bliss:Bliss F l z H)(T:ℕ):
   ∀ᶠs in trail,∀{D:ℕ}(b:Book F (l:=l) H z D T s)(d:Fin (D+1))(v:S.Field d.val),a (slot F b d v).j ≤ s:=by
  obtain ⟨B,_,fee⟩:=invoice F simple bliss T
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small:Tendsto (fun s=>B*(wilson z s)^4) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=B)).mul ((link.conforms simple).pow 4)
  filter_upwards [fee,small.eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin] with s money fit sp
  intro D b d v
  let L:=slot F b d v
  calc
    _ ≤ a L.m:=(C).S.strictAnti.antitone L.fore
    _ ≤ radius z T s*dock (radius z T s)^T:=L.front.le
    _ = s*((dock (radius z T s)^T*(wilson z s)^(2*T))*(wilson z s)^4):=by
      rw [radius,pow_add];ring
    _ ≤ s*(B*(wilson z s)^4):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right money.2 (by positivity)) sp.le
    _ ≤ s:=mul_le_of_le_one_right sp.le fit

omit [DecidableEq I] in
/-- Every slot is placed on the original common optical date, before an arbitrary
later canonical trial depth.  The dated quota below is for this very finite-cutoff
public source, including its actual unit and lower coordinates. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h gate:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
    (∃i,(ρ i).val=r) → ∀v:(i:I)→S.Field (d i).val,
    let f₀:=reporter F books ρ
    ∀i,let L:=slot F (books (ρ i)) (d i) (v i)
       gate ≤ L.j ∧ L.j ≤ f₀ ∧ a L.j/a f₀ ≤ (β f₀)^(2*T+11+2*h) ∧
       L.arm=((books (ρ i)).rows (d i)).arm false (v i):=by
  obtain ⟨ε,ep,shrunk⟩:=Metric.mem_nhdsWithin_iff.mp (berth_width F simple bliss T)
  have late:=longer F simple bliss h
  filter_upwards [WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    late.eventually ((gt_mem_nhds ep).filter_mono nhdsWithin_le_nhds),
    late.eventually ((gt_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds)] with r span small old
  intro ρ range near v f₀ i L
  have rates:=(span ρ range near).2 i
  have chosen:=source F (books (ρ i)) (d i) (v i)
  have width:=shrunk (show (ρ i).val∈Metric.ball (0:ℝ) ε ∩ Set.Ioi 0 from ⟨by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i).property.1];exact (range i).2.trans_lt small,(ρ i).property.1⟩)
    (books (ρ i)) (d i) (v i)
  refine ⟨?_,chosen.1.trans_le ((le_max_left ..).trans rates.1),?_,chosen.2⟩
  · by_contra! low
    exact (not_lt_of_ge (width.trans ((range i).2.trans old.le))) ((C).S.strictAnti low)
  · exact (div_le_iff₀ ((C).S.a_pos f₀)).mpr (width.trans rates.2)

end YM.Integration.WilsonMovingForkSlotDate
end
