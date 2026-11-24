import YM.Integration.WilsonSeparatedOriginalSlabUniform
import YM.Integration.WilsonSeparatedOriginalProfileTest

/-! An original smooth three-source receipt with the older observation fixed before the radius; the cutoff and period follow the genuine nuclear toll. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabUniformRun
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open WilsonAllDateHarvestHistoricalEntry WilsonAllDateHarvestNuclearProgram WilsonSeparatedOriginalSlabCubicInvoice
open RG05Readout.Nuclear RG05Readout.Pulse Push.GridApprox
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}(R:Run G)(simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T)
  {δ:ℝ}(fund:FundedOriginalProperties.{u} simple δ W)(book:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
  (portfolio:Funding R)(slow:WilsonWindowReportingPace.Slow R.kit)
variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
  {J:ℝ→FamilyBasis (C:=R.family) table}{l:Filter (ℕ×ℕ)}(B:Mantle F l)(E:OPE.Services R.family order table)
  (paid:Pier.Lair.Present F J)(pegs:Pegs B L)
  (near:∀ᶠr in trail,R.family.S.a (L.level r) ≤ r ∧ r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)
local notation "C"=>R.family
local notation "stopAt"=>WilsonMeasuredWindow.stop R.family.path.levels simple

def testRank (s:Fin 3→ℕ):ℕ:=(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)
def Earned (K d h:ℕ)(s:Fin 3 → ℕ)(w:(r:ℝ) → (i:Fin 3) → (C).label (s i)):Prop:=
  ∀η:ℝ,0<η → η≤1 → ∀cap:ℝ,0≤cap → ∀ᶠb:ℕ in atTop,∃hb:(C).ref 0 ≤ b,∀ᶠr in trail,∃nm:b+1 ≤ stopAt K r,
    ∀X:ℝ,0≤X → ∀g:Body,∀σ:ℝ,0<σ →
      WilsonSeparatedOriginalSlabUniform.Settled R simple portfolio L K d h b s r η X cap (w r) hb nm (testRank s) g σ

include W fund book slow B pegs near in
theorem chosen (K d:ℕ)(hk:5 ≤ K)(s:Fin 3 → ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3) → Free C (s i))
    (h:ℕ)(w:(r:ℝ) → (i:Fin 3) → (C).label (s i))
    (selected:∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r))
    (k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k):
    Earned R simple portfolio L K d h s w:=by
  intro η ep small cap cp
  obtain ⟨b0,capture⟩:=WilsonSeparatedOriginalSlabChildCentered.chosen R simple W fund book portfolio slow L B pegs near
    K d ⌈cap+2⌉₊ hk ep s degree v h w selected k warm 1 zero_lt_one 0
  filter_upwards [eventually_ge_atTop b0,eventually_ge_atTop ((C).ref 0)] with b hb old
  refine ⟨old,?_⟩
  have low:∀ᶠr:ℝ in trail,r<(C).S.a (b+1):=(tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ((C).S.a_pos _))
  have late:∀ᶠr:ℝ in trail,b+1 ≤ stopAt K r:=(WilsonMeasuredWindow.stop_tendsto (C).path.levels simple K (by omega:0<K)).eventually_ge_atTop _
  have pos:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  filter_upwards [capture,late,low,pos] with r issued nm room rp
  exact ⟨nm,fun X xp g σ sp=>WilsonSeparatedOriginalSlabUniform.purchased R simple portfolio L K d h b s (w r) old nm rp room.le
    ep small (testRank s) (Nat.lt_succ_self _) xp cp (issued b hb nm) g sp⟩


include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K)(s:Fin 3 → ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3) → Free C (s i)):
    ∃(h:ℕ)(w:(r:ℝ) → (i:Fin 3) → (C).label (s i)),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      Earned R simple portfolio L K d h s w:=by
  obtain ⟨h,w,selected,_⟩:=WilsonReportHarvestReplayPrescribed.original R simple W fund book portfolio slow L B E paid pegs near K d (by omega) s degree v
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  exact ⟨h,w,selected,chosen R simple W fund book portfolio slow L B pegs near K d hk s degree v h w selected k warm⟩

end YM.Integration.WilsonSeparatedOriginalSlabUniformRun
