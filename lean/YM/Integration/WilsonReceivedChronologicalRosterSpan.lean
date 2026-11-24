import YM.Integration.WilsonMovingForkOpticalStops

/-! The wider physical stop also pays the duration from its preceding date at the
true clock of the stop itself. The source and the independent capture keep their dates. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterSpan
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

private theorem step (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {i c N per:ℕ}(late:4≤H c)(ic:i≤c)(live:c≤N):
    Real.log ((R.family.S.block i).val:ℝ) ≤ 4*Real.log (regulatorRun R.family N per c)⁻¹:=by
  let β:=R.family.path.β N per c
  have born:1≤H i:=((L).fits.delayed i).le
  have hp:0<H i:=zero_lt_one.trans_le born
  have logp:0≤Real.log (H i):=Real.log_nonneg born
  have raw:((R.family.S.block i).val:ℝ)≤Real.log (2+Real.log (H i)):=slow.2 i
  have block:((R.family.S.block i).val:ℝ)≤H c:=by
    apply le_trans _ (WilsonStartup.Timing.hat_mono L (Gauge.slopeConstant_pos simple).le ic)
    linarith [Real.log_le_sub_one_of_pos hp,Real.log_le_sub_one_of_pos (by linarith:0<2+Real.log (H i))]
  have half:H c / 2≤β:=(R.makes.wilson.represents N per c live).band.1
  have two:2≤β:=by linarith
  have gross:H c≤β^2:=by nlinarith [mul_nonneg (by linarith:0≤β) (by linarith:0≤β-2)]
  have root:0<Real.sqrt β:=Real.sqrt_pos.2 (by linarith)
  have square:(Real.sqrt β)^4=β^2:=by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt (by linarith)]
  have pos:0<((R.family.S.block i).val:ℝ):=by exact_mod_cast (R.family.S.block i).pos
  have log:=Real.log_le_log pos (block.trans (gross.trans square.ge))
  rw [Real.log_pow] at log
  simpa only [regulatorRun,one_div,inv_inv,Nat.cast_ofNat,β] using log

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(reserve window depth:ℕ):
    ∃width cut:ℕ,∀f c:ℕ,cut≤f→cut≤c→let K:=berth R reserve f
      ∀v N per:ℕ,0<v→c≤f→v≤c→c≤N→a c/a f≤(H f)^window→
        σ c-σ v≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹→
        a (v-1)/a K≤(H (v-1))^width ∧ σ K-σ (v-1)≤(width:ℝ)*(1+Real.log (H v)):=by
  obtain ⟨width,sale⟩:=WilsonMovingForkOpticalStops.original R simple slow reserve window (depth+1)
  obtain ⟨fromFine,fine⟩:=eventually_atTop.mp sale
  obtain ⟨fromCoarse,coarse⟩:=eventually_atTop.mp ((hat_rate L simple).eventually_ge_atTop 4)
  refine ⟨width,max fromFine fromCoarse,?_⟩
  intro f c cutFine cutCoarse
  have opened:=fine f ((le_max_left ..).trans cutFine)
  have late:=coarse c ((le_max_right ..).trans cutCoarse)
  intro K v N per vp cf vc live wide span
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

end YM.Integration.WilsonReceivedChronologicalRosterSpan
