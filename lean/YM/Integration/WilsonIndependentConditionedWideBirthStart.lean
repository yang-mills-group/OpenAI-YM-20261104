import YM.Integration.WilsonIndependentConditionedStoppedCalendar
import YM.Integration.WilsonOriginalOpticalCouplingBand

/-! The universal physical stopping appointment applied to the wide capture. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedWideBirthStart
open Filter Set Wilson RG Lattice PhysMS PhysicalNext.Repeat.Legato Next.Rank
open WilsonPositionProgramReporterBand WilsonReceivedChronologicalFixedCellFee
open WilsonOriginalTwoFlatIRCapturedCross Pert.Asymptotics
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "trail" => nhdsWithin (0:ℝ) (Set.Ioi 0)

def Held {world:XSpace.Run}{stage u depth:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u depth)(P floor:ℕ){n:ℕ}(φ:Test n)(hi lam:ℝ):Prop:=
  let c:=capture R φ lam
  ∃w:ℕ,∃_center:c=run.reporter+w,∃uc:u≤c,∃vc:v.date w≤c,
    v.date w-1+1=v.date w ∧ u≤v.date w ∧ stage≤v.date w ∧ v.date w<c ∧ floor+1≤c ∧ factor R φ*lam≤a 0 ∧
    (max 1 (max hi (factor R φ)))*lam<a (v.date w) ∧
    (∀N per:ℕ,c≤N → σ c-σ (v.date w)≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹) ∧
    ∀N per:ℕ,c<N → Quote R N per u (v.date w) c P depth uc vc

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    {world:XSpace.Run}{stage u depth:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u depth)(positive:0<stage)(deep:0<depth)
    (cu:R.family.ref 0≤u)(P floor:ℕ){n:ℕ}(φ:Test n)(hi:ℝ):
    ∀ᶠ lam in trail,Held R run v P floor φ hi lam:=by
  obtain ⟨k,earned⟩:=eventually_atTop.mp v.heard
  obtain ⟨rad,rp,booked⟩:=WilsonOriginalTwoFlatIRSocketAppointment.original
    R simple slow.2 ready world run v cu P φ (max floor (run.reporter+k))
  let size:=max 1 (max hi (factor R φ))
  have sp:0<size:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have shrinks:=WilsonAddressedPublicFirstRoseMovingDate.outer R simple world run v φ deep
  filter_upwards [Ioc_mem_nhdsGT rp,shrinks.eventually_lt_const (inv_pos.mpr sp),
    (WilsonAddressedPublicFirstRoseMovingDate.cofinal R φ).eventually (WilsonOriginalOpticalCouplingBand.cold R simple 2)] with lam live outside cold
  let c:=capture R φ lam
  obtain ⟨w,eq,uc,vc,above,initial,quote⟩:=booked lam live.1 live.2
  have center:c=run.reporter+w:=eq
  have kw:k≤w:=by
    have co:run.reporter+k≤c:=(le_max_right ..).trans (Nat.le_of_succ_le above)
    omega
  have epoch:stage≤v.date w:=(run.ready w).trans (v.lower w)
  have same:c-run.reporter=w:=by omega
  have aperture:size*lam<a (v.date w):=by
    change lam/a (v.date (c-run.reporter))<size⁻¹ at outside
    rw [same] at outside
    have cap:=mul_lt_mul_of_pos_left ((div_lt_iff₀ (R.family.S.a_pos _)).mp outside) sp
    simpa only [←mul_assoc,mul_inv_cancel₀ sp.ne',one_mul] using cap
  let g:=regulatorRun R.family c 0 c
  have pos:0<g:=ActualRunKernelPackets.regulator_pos R c 0 c le_rfl
  have cheap:(2:ℝ)≤g⁻¹:=cold c 0 le_rfl
  have less:g<1:=by rw [le_inv_comm₀ (by norm_num) pos] at cheap; linarith
  have gain:=((earned w kw).2 c 0 center.ge).2.2.1
  have before:v.date w<c:=by
    apply lt_of_le_of_ne vc
    intro equal
    rw [←center,equal,div_self (R.family.S.a_pos c).ne'] at gain
    exact not_lt_of_ge gain (pow_lt_one₀ (pow_nonneg pos.le _) (pow_lt_one₀ pos.le less deep.ne') (by decide))
  refine ⟨w,center,uc,vc,Nat.sub_add_cancel (positive.trans_le epoch), (earned w kw).1,epoch,before,
    (Nat.succ_le_succ (le_max_left ..)).trans above,initial,aperture,?_,quote⟩
  intro N per liveN
  change σ c-σ (v.date w)≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹
  change c≤N at liveN
  rw [center] at liveN ⊢
  exact ((earned w kw).2 N per liveN).2.2.2

end YM.Integration.WilsonIndependentConditionedWideBirthStart
