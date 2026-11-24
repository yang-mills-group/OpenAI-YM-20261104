import YM.Integration.WilsonMovingForkPredecessorStops

/-! The wider physical stop also pays the duration from its preceding date at the
true clock of the stop itself. The source and the independent capture keep their dates. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMovingForkPredecessorCalendar
open Function Filter Set Lattice RG Wilson Org PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open MS MS.Land Trace.Pilot Next.Rank Next.Rank.Station MergeProof.East
open Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "a" => R.family.S.a
open WilsonInvariantActionPosition (berth)

open private step from YM.Integration.WilsonMovingForkPredecessorStops

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(reserve window depth:ℕ):
    ∃width floor:ℕ,∀f c:ℕ,floor≤f→floor≤c→let K:=berth R reserve f
      ∀v N per:ℕ,0<v→c≤f→v≤c→c≤N→a c/a f≤(H f)^window→
        σ c-σ v≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹→
        a (v-1)/a K≤(H (v-1))^width ∧ σ K-σ (v-1)≤(width:ℝ)*(1+Real.log (H v)):=by
  obtain ⟨width,sale⟩:=WilsonMovingForkOpticalStops.original R simple slow reserve window (depth+1)
  obtain ⟨fromF,oldF⟩:=eventually_atTop.mp sale
  obtain ⟨fromC,oldC⟩:=eventually_atTop.mp ((hat_rate L simple).eventually_ge_atTop 4)
  refine ⟨width,max fromF fromC,?_⟩
  intro f c mature lateC K v N per vp cf vc live wide span
  have opened:=oldF f ((le_max_left ..).trans mature)
  have late:=oldC c ((le_max_right ..).trans lateC)
  have prev:v-1+1=v:=by omega
  have diff:σ v=σ (v-1)+Real.log ((R.family.S.block (v-1)).val:ℝ):=by
    convert R.family.S.scale_succ (v-1) using 1
    rw [prev]
  have d:=step R simple slow (i:=v-1) (per:=per) late (by omega) live
  have logp:0≤Real.log (regulatorRun R.family N per c)⁻¹:=by
    have one:1≤((R.family.S.block (v-1)).val:ℝ):=by exact_mod_cast (R.family.S.block (v-1)).pos
    linarith [Real.log_nonneg one]
  have billed:=opened c (v-1) N per cf (by omega) live wide
  rw [prev] at billed
  apply billed
  push_cast
  nlinarith only [d,span,diff,logp]

end YM.Integration.WilsonMovingForkPredecessorCalendar
