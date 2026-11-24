import YM.Integration.WilsonOlderFreshSoftSocketStationCalendar
import YM.Integration.WilsonMovingForkPredecessorCalendar

/-! The separately chosen independent date lies above the physical stop at
the same actual captured offset. Its uniform date quotation may be read at
the captured date before the later ultraviolet cutoff is chosen. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharedCapture
open Filter Function Set Lattice RG Wilson Org PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open MS MS.Land Trace.Pilot Next.Rank Next.Rank.Station MergeProof.East Pert.Asymptotics
open WilsonPositionProgramReporterBand (Band)
open WilsonIndependentCapturedPages (Stop)
open WilsonOlderFreshSoftSocketStationCalendar (date)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "g" => regulatorRun R.family

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (width:ℕ)(loss:ℝ)(nonneg:0≤loss)
    (world:XSpace.Run){stage u infrared:ℕ}(B:Band R world stage)(v:Stop R world B u infrared)
    (depth:8*(2*⌈loss⌉₊+1)≤2*infrared):
    ∀ᶠt:ℕ in atTop,let c:=B.reporter+t
      v.date t≤date R width loss c ∧ date R width loss c≤c ∧
      ∀K N per:ℕ,c≤K→K≤N→a c/a K≤(H c)^width→
        a c/a (date R width loss c)≤Real.exp (-loss*Real.log (g N per K)⁻¹):=by
  have dated: Tendsto (fun t:ℕ=>B.reporter+t) atTop atTop:=by
    refine tendsto_atTop.2 fun m=>?_
    filter_upwards [eventually_ge_atTop m] with t late
    omega
  have stations:=(WilsonOlderFreshSoftSocketStationCalendar.original R simple slow width loss nonneg).2
  filter_upwards [v.heard,dated.eventually stations] with t accepted issued
  let c:=B.reporter+t
  let w:=date R width loss c
  change v.date t≤w ∧ w≤c ∧ _
  obtain ⟨wu,allK⟩:=issued
  have original:=accepted.2 c 0 le_rfl
  have market:0<g c 0 c:=original.1
  have small:g c 0 c≤1:=original.2.1
  have slope:=Real.log_le_log (div_pos (R.family.S.a_pos c) (R.family.S.a_pos (v.date t))) original.2.2.1
  rw [WilsonReflectedRelativeDate.ratio R,Real.log_pow,Real.log_pow] at slope
  have one:1≤(H c)^width:=one_le_pow₀ ((R.family.path.levels.fits.delayed c).le)
  have captured:=allK c c 0 le_rfl le_rfl (by
    change a c / a c ≤ (H c)^width
    simpa only [div_self (R.family.S.a_pos c).ne'] using one)
  have charged:=captured.2.2
  have lp:0≤Real.log (g c 0 c)⁻¹:=Real.log_nonneg ((one_le_inv₀ market).2 small)
  have money:(8*((2*⌈loss⌉₊:ℕ)+1):ℝ)≤2*(infrared:ℝ):=by exact_mod_cast depth
  have bill:=mul_le_mul_of_nonneg_right money lp
  rw [Real.log_inv] at bill charged
  have earlier:v.date t≤w:=by
    by_contra! late
    have later:σ w<σ (v.date t):=OPE.scale_mono R.family.S late
    dsimp only [c,w] at later slope bill charged
    push_cast at slope charged bill
    linarith only [later,slope,charged,bill]
  exact ⟨earlier,wu,fun K N per ck live reach=>(allK K N per ck live reach).1⟩
end YM.Integration.WilsonMovingForkSharedCapture
