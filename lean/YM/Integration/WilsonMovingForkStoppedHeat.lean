import YM.Integration.WilsonMovingForkPaidHousing
import YM.Integration.WilsonReflectedRelativeDate

/-! The running public clock bounds the actual inverse square root of the
Wilson action at the older stop on the purchased optical interval. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonMovingForkStoppedHeat
open Function Filter Set Lattice RG Wilson Org PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open MS MS.Land Trace.Pilot Next.Rank Next.Rank.Station MergeProof.East
open Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "a" => R.family.S.a

private theorem short (simple:G.Simple)(w:ℝ)(wp:0≤w):
    ∀ᶠ j:ℕ in atTop,2 ≤ H j ∧ ∀v:ℕ,σ j-σ v≤w*Real.log (2*H j) → H j≤2*H v:=by
  let charge:=G.slopeConstant*(2*w)
  have cp:0≤charge:=mul_nonneg (Gauge.slopeConstant_pos simple).le (by positivity)
  have rate:=hat_rate L simple
  have toll:0<4*(1+charge):=by linarith
  filter_upwards [rate.eventually_ge_atTop 2,rate.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr toll))]
    with j warm balance
  refine ⟨warm,?_⟩
  intro v span
  have hp:0<H j:=by linarith
  have logpos:0≤Real.log (H j):=Real.log_nonneg (by linarith)
  have tiny:Real.log (H j)≤(4*(1+charge))⁻¹*(H j):=by
    simpa only [Real.norm_eq_abs,id_eq,abs_of_pos hp,abs_of_nonneg logpos] using balance
  have collected:Real.log (H j)*(4*(1+charge))≤H j:=
    (le_div_iff₀ toll).mp (by simpa [div_eq_mul_inv,mul_comm] using tiny)
  have roof:Real.log (2*H j)≤2*Real.log (H j):=by
    rw [Real.log_mul (by norm_num) hp.ne']
    linarith only [Real.log_le_log (by norm_num:0<(2:ℝ)) warm]
  have delta:H j-H v=G.slopeConstant*(σ j-σ v):=by
    unfold Calendar.hatBeta
    change _+_*σ j-(_+_*σ v)=_
    ring
  have spent:=mul_le_mul_of_nonneg_left
    (span.trans (mul_le_mul_of_nonneg_left roof wp)) (Gauge.slopeConstant_pos simple).le
  change H j-H v=G.slopeConstant*(σ j-σ v) at delta
  have bound:H j-H v≤charge*Real.log (H j):=delta.le.trans (by dsimp [charge]; nlinarith only [spent])
  nlinarith only [bound,collected,logpos,hp.le]

/-- The exponent and stopping depth are fixed before the numerical order or
either original regulator. The same constant works on all ultraviolet prefixes. -/
theorem original (simple:G.Simple){θ:ℝ → ℝ}(clock:Coupling G θ)(window depth:ℕ):
    ∀ᶠ r in trail,∀ j c v N per:ℕ,a j≤r → c≤j → v≤c → c≤N →
      a c/a j≤(H j)^window → σ c-σ v≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹ →
      0<regulatorRun R.family N per v ∧ regulatorRun R.family N per v≤4*θ r:=by
  let w:ℝ:=(window:ℝ)+4*(2*(depth:ℝ)+1)
  have sp:=Gauge.slopeConstant_pos simple
  obtain ⟨j₀,after⟩:=eventually_atTop.mp (short R simple w (by dsimp [w];positivity))
  have half:G.slopeConstant⁻¹/2<G.slopeConstant⁻¹:=half_lt_self (inv_pos.mpr sp)
  filter_upwards [self_mem_nhdsWithin,clock.positive,clock.running.eventually (le_mem_nhds half),
    (ge_mem_nhds (R.family.S.a_pos j₀)).filter_mono nhdsWithin_le_nhds] with r rp gp origin late
  change 0<r at rp
  change G.slopeConstant⁻¹/2≤LogV r*(θ r)^2 at origin
  intro j c v N per inBox cj vc live wide span
  have jbig:j₀≤j:=by by_contra! h;exact (not_le_of_gt (R.family.S.strictAnti h)) (inBox.trans late)
  have wk:=after j jbig
  have jp:0<H j:=lt_of_lt_of_le (by norm_num) wk.1
  have shift:σ j-σ c≤(window:ℝ)*Real.log (H j):=by
    have priced:=Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) wide
    rwa [WilsonReflectedRelativeDate.ratio R,Real.log_pow] at priced
  have hatOrder:H c≤H j:=WilsonStartup.Timing.hat_mono L sp.le cj
  have βc:R.family.path.β N per c≤2*H j:=(R.makes.wilson.represents N per c live).band.2.trans
    (mul_le_mul_of_nonneg_left hatOrder (by norm_num))
  have βcp:0<R.family.path.β N per c:=by
    exact lt_of_lt_of_le (half_pos (zero_lt_one.trans ((L).fits.delayed c))) (R.makes.wilson.represents N per c live).band.1
  have mask:Real.sqrt (R.family.path.β N per c)≤2*H j:=(Real.sqrt_le_iff).2
    ⟨by linarith,βc.trans (by nlinarith only [wk.1,mul_nonneg (sub_nonneg.mpr wk.1) jp.le])⟩
  have cCost:Real.log (regulatorRun R.family N per c)⁻¹≤Real.log (2*H j):=by
    simpa only [regulatorRun,inv_inv] using Real.log_le_log (Real.sqrt_pos.2 βcp) mask
  have jCost:Real.log (H j)≤Real.log (2*H j):=Real.log_le_log jp (by linarith)
  have jv:H j≤2*H v:=wk.2 v (by
    dsimp [w]
    linarith only [shift.trans (mul_le_mul_of_nonneg_left jCost (Nat.cast_nonneg window)),
      span.trans (mul_le_mul_of_nonneg_left cCost (by positivity:0≤4*(2*(depth:ℝ)+1)))])
  have energy:R.family.path.β N per v≥H v/2:=(R.makes.wilson.represents N per v (vc.trans live)).band.1
  have βvp:0<R.family.path.β N per v:=lt_of_lt_of_le (half_pos (zero_lt_one.trans ((L).fits.delayed v))) energy
  have lg:LogV r≤σ j:=Real.log_le_log (inv_pos.mpr rp) (inv_anti₀ (R.family.S.a_pos _) inBox)
  have money:G.slopeConstant*σ j≤H j:=le_add_of_nonneg_left (L).clock.bar_pos.le
  have coin:G.slopeConstant*(G.slopeConstant⁻¹/2)≤H j*(θ r)^2:=
    (mul_le_mul_of_nonneg_left origin sp.le).trans (by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left lg sp.le).trans money) (sq_nonneg _))
  have unit:G.slopeConstant*(G.slopeConstant⁻¹/2)=1/2:=by field_simp
  rw [unit] at coin
  have ratio:H j≤4*R.family.path.β N per v:=by linarith
  have wall:1≤(4*θ r*Real.sqrt (R.family.path.β N per v))^2:=by
    rw [mul_pow,Real.sq_sqrt βvp.le]
    nlinarith only [coin.trans (mul_le_mul_of_nonneg_right ratio (sq_nonneg _))]
  have squared:0≤4*θ r*Real.sqrt (R.family.path.β N per v):=by positivity
  have one:1≤4*θ r*Real.sqrt (R.family.path.β N per v):=
    (sq_le_sq₀ zero_le_one squared).mp (by simpa only [one_pow] using wall)
  exact ⟨inv_pos.mpr (Real.sqrt_pos.2 βvp), (by
    unfold regulatorRun
    rw [←one_div]
    exact (div_le_iff₀ (Real.sqrt_pos.2 βvp)).mpr one)⟩

end YM.Integration.WilsonMovingForkStoppedHeat
