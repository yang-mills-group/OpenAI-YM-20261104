import YM.Integration.WilsonAddressedPublicFirstRoseGeometry
import YM.Integration.WilsonOriginalTwoFlatIRSocketAppointment
import YM.Integration.WilsonThermometerUnitFilingCaptureCoupling

/-! The infrared stop for the physical test and its measured public mesh
qualify both actual compact support radii before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseMovingDate
open Function Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open Analysis Table Spec Extraction Next.UVStress OPE OPE.Orbits OPE.Nesting Trace.Pilot PhysMS
open WilsonPositionProgramReporterBand
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "g" => regulatorRun R.family

private theorem cold (simple:G.Simple):Tendsto (fun k:ℕ=>g k 0 k) atTop (𝓝 0):=by
  have runs:Tendsto (fun k:ℕ=>R.family.path.β k 0 k) atTop atTop:=by
    apply tendsto_atTop.2
    intro x
    filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2*x)] with k late
    have bound: R.family.path.levels.clock.hatBeta k/2 ≤ R.family.path.β k 0 k:=
      (R.makes.wilson.represents k 0 k le_rfl).band.1
    linarith only [late,bound]
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp runs)

theorem cofinal {n:ℕ}(φ:Test n):Tendsto (capture R φ) trail atTop:=by
  have hp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  apply tendsto_atTop.2
  intro k
  filter_upwards [Ioc_mem_nhdsGT (div_pos (R.family.S.a_pos k) hp)] with r small
  have close:factor R φ*r ≤ a k:=by simpa only [mul_comm] using (le_div_iff₀ hp).mp small.2
  have origin:=close.trans (R.family.S.strictAnti.antitone (Nat.zero_le _))
  have side: a (capture R φ r+1) < factor R φ*r:=(WilsonCloseCaptureDate.bracket R.family.S
    (mul_pos hp small.1) origin).1
  by_contra! bad
  exact (not_lt_of_ge (close.trans (R.family.S.strictAnti.antitone (Nat.succ_le_of_lt bad)))) side

variable (simple:G.Simple)(D:XSpace.Run){stage u d:ℕ}(B:Band R D stage)
  (v:WilsonIndependentCapturedPages.Stop R D B u d)

include simple in
theorem outer {n:ℕ}(φ:Test n)(dp:0<d):
    Tendsto (fun r=>r/a (v.date (capture R φ r-B.reporter))) trail (𝓝 0):=by
  let c:=capture R φ
  let h:ℝ→ℕ:=fun r=>c r-B.reporter
  have hp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  have grow:Tendsto c trail atTop:=cofinal R φ
  have up:Tendsto h trail atTop:=by
    apply tendsto_atTop.2
    intro k
    filter_upwards [grow.eventually_ge_atTop (B.reporter+k)] with r late
    dsimp only [h];omega
  have bound:Tendsto (fun r=>(g (c r) 0 (c r)^d)^2/factor R φ) trail (𝓝 0):=by
    simpa only [Function.comp_apply,zero_pow dp.ne',zero_pow (by decide:2 ≠ 0),zero_div] using
      ((((cold R simple).comp grow).pow d).pow 2).div_const (factor R φ)
  have start:=Ioc_mem_nhdsGT (div_pos (R.family.S.a_pos 0) hp)
  apply squeeze_zero' _ _ bound
  · filter_upwards [start] with r pos
    exact (div_pos pos.1 (R.family.S.a_pos _)).le
  · filter_upwards [start,up.eventually v.heard,grow.eventually_ge_atTop B.reporter] with r small stop rest
    have ink:c r=B.reporter+h r:=by dsimp only [h];omega
    have live:B.reporter+h r ≤ c r:=ink.ge
    have chart:factor R φ*r ≤ a 0:=by simpa only [mul_comm] using (le_div_iff₀ hp).mp small.2
    have near:factor R φ*r ≤ a (c r):=(WilsonCloseCaptureDate.bracket R.family.S (mul_pos hp small.1) chart).2
    have cost:a (c r)/a (v.date (h r)) ≤ (g (c r) 0 (c r)^d)^2:=by
      simpa only [←ink] using (stop.2 (c r) 0 live).2.2.1
    calc r/a (v.date (h r)) = ((factor R φ*r)/a (v.date (h r)))/(factor R φ):=by
          field_simp [hp.ne',(R.family.S.a_pos _).ne']
         _ ≤ _:=div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right near
           (R.family.S.a_pos _).le).trans cost) hp.le

include simple in
theorem original {n:ℕ}(φ:Test n)(dp:0<d){g₀:ℝ→ℝ}(law:Coupling G g₀)
    {x y:ℝ}(xp:0<x)(yp:0<y):
    ∀ᶠ r:ℝ in trail,∀m f:ℕ,m+1=v.date (capture R φ r-B.reporter) →
      a f/r ≤ g₀ r^2 → Fits R.family.S x r m f ∧ Fits R.family.S y r m f:=by
  have top:0 < max x y:=xp.trans_le (le_max_left ..)
  have bottom:0 < min x y:=lt_min xp yp
  have curve:Tendsto g₀ trail (𝓝 0):=tendsto_order.2 ⟨fun b hb=>law.positive.mono (fun _ pos=>hb.trans pos),
    fun b hb=>(WilsonThermometerUnitFilingCaptureCoupling.small simple law (half_pos hb)).mono
      (fun _ paid=>paid.trans_lt (half_lt_self hb))⟩
  have square:Tendsto (fun r=>g₀ r^2) trail (𝓝 0):=by simpa using curve.pow 2
  filter_upwards [self_mem_nhdsWithin,(outer R simple D B v φ dp).eventually_lt_const (inv_pos.mpr top),
    square.eventually_lt_const (div_pos bottom (by norm_num:0<(8:ℝ)))] with r pos before close
  intro m f paid fine
  have inner:a f < min x y/8*r:=(div_lt_iff₀ pos).mp (fine.trans_lt close)
  apply WilsonAddressedPublicFirstRoseGeometry.original R.family.S xp yp pos
  · rw [paid]
    have good:r<(max x y)⁻¹*a (v.date (capture R φ r-B.reporter)):=(div_lt_iff₀ (R.family.S.a_pos _)).mp before
    simpa only [←mul_assoc,mul_inv_cancel₀ top.ne',one_mul] using mul_le_mul_of_nonneg_left good.le top.le
  · linarith only [inner]

end YM.Integration.WilsonAddressedPublicFirstRoseMovingDate
end
