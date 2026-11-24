import YM.Integration.WilsonCloseCaptureDate
import YM.Integration.WilsonThermometerUnitFilingSpan
import YM.Pert.Asymptotics.RawAxis

/-! The original finite coupling and the measured continuum clock at true geometric capture. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCaptureCoupling
open Filter Function Lattice Overlay Wilson RG RG16 PhysMS OPE OPE.Orbits OPE.Nesting Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) {g:ℝ→ℝ} (law:Coupling G g)
local notation "C" => R.family
local notation "H" => R.family.path

theorem bracket (j:ℕ) : ∀ᶠ r:ℝ in trail, let b:=WilsonCloseCaptureDate.level (C).S r
    j ≤ b ∧ (C).S.a (b+1) < r ∧ 0 < r ∧ r ≤ (C).S.a b:=by
  filter_upwards [Ioc_mem_nhdsGT ((C).S.a_pos j)] with r small
  let b:=WilsonCloseCaptureDate.level (C).S r
  have geometry:=WilsonCloseCaptureDate.bracket (C).S small.1
    (small.2.trans ((C).S.strictAnti.antitone (Nat.zero_le j)))
  refine ⟨?_,geometry.1,small.1,geometry.2⟩
  by_contra! early
  have scale:= (C).S.strictAnti.antitone (Nat.succ_le_of_lt early)
  exact (not_lt_of_ge scale) (geometry.1.trans_le small.2)

include simple law in
theorem physical : ∀ᶠ r:ℝ in trail, let b:=WilsonCloseCaptureDate.level (C).S r
    0 < g r ∧ ∀ N p:ℕ,b<N → 0 < regulatorRun C N p (b+1) ∧ regulatorRun C N p (b+1) ≤ 2*g r:=by
  let s:=G.slopeConstant
  have sp:0 < s:=Gauge.slopeConstant_pos simple
  have ip:0 < s⁻¹:=inv_pos.mpr sp
  have hp:s⁻¹/2 < s⁻¹:=by linarith only [ip]
  filter_upwards [bracket R 0,law.positive,law.running.eventually (lt_mem_nhds hp)] with r slot gp paid
  let b:=WilsonCloseCaptureDate.level (C).S r
  refine ⟨gp,?_⟩
  intro N p live
  let β:=((H).rep N p (b+1)).beta
  have bp:0 < β:=Overlay.beta_positive R.makes.wilson live
  have norm:regulatorRun C N p (b+1)=(Real.sqrt β)⁻¹:=rfl
  have lb:(H).levels.clock.hatBeta (b+1)/2 ≤ β:=(R.makes.wilson.represents N p (b+1) live).band.1
  have clock:(H).levels.clock.hatBeta (b+1)=(H).levels.clock.bar+s*(C).S.scale (b+1):=rfl
  have logScale:LogV r ≤ (C).S.scale (b+1):=
    Real.log_le_log (inv_pos.mpr slot.2.2.1) (inv_anti₀ ((C).S.a_pos _) slot.2.1.le)
  have lower:s*LogV r ≤ 2*β:=by
    have base:=((H).levels.clock.bar_pos).le
    have advance:=mul_le_mul_of_nonneg_left logScale sp.le
    linarith only [base,clock,lb,advance]
  have thermal:1 ≤ (2*s)*(LogV r*g r^2):=by
    calc 1=(2*s)*(s⁻¹/2):=by field_simp
         _ ≤ (2*s)*(LogV r*g r^2):=mul_le_mul_of_nonneg_left paid.le (by positivity)
  have units:1 ≤ β*(2*g r)^2:=calc
    1 ≤ (2*s)*(LogV r*g r^2):=thermal
    _=(s*LogV r)*(2*g r^2):=by ring
    _ ≤ (2*β)*(2*g r^2):=mul_le_mul_of_nonneg_right lower (by positivity)
    _=β*(2*g r)^2:=by ring
  have product:1 ≤ (Real.sqrt β)*(2*g r):=by
    apply (sq_le_sq₀ zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mp
    rw [one_pow,mul_pow,Real.sq_sqrt bp.le]
    exact units
  rw [norm];refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr bp),?_⟩
  rw [←one_div,div_le_iff₀ (Real.sqrt_pos.mpr bp)]
  simpa only [mul_comm] using product

include simple law in
theorem small {k:ℝ} (kp:0 < k):∀ᶠ r in trail, g r ≤ k:=by
  let D:=G.slopeConstant⁻¹+1
  have upper:G.slopeConstant⁻¹ < D:=by dsimp [D];linarith
  have dp:0 < D:=by dsimp [D];have :=Gauge.slopeConstant_pos simple;positivity
  have divisor:0 < k^2:=by positivity
  filter_upwards [law.running.eventually (gt_mem_nhds upper),PhysMS.to_log_zoom.eventually_gt_atTop (D/k^2),
    law.positive] with r curve time pos
  have lp:0 < LogV r:=(div_pos dp divisor).trans time
  have clock: D ≤ LogV r*k^2:=(div_le_iff₀ divisor).mp time.le
  apply (sq_le_sq₀ pos.le kp.le).mp
  exact le_of_mul_le_mul_left (curve.le.trans clock) lp

include simple law in
theorem every_order (q:ℕ) {A ε:ℝ} (an:0 ≤ A) (ep:0 < ε):∀ᶠ r:ℝ in trail,
    let b:=WilsonCloseCaptureDate.level (C).S r
    ∀ N p:ℕ,b<N → A*(regulatorRun C N p (b+1))^(q+1) ≤ ε*(g r)^q:=by
  let D:=A*2^(q+1)
  have dn:0 ≤ D:=by dsimp [D];positivity
  have pos:0 < 1+D:=by linarith only [dn]
  filter_upwards [physical R simple law,small simple law (div_pos ep pos)] with r live cheap
  intro b N p here
  obtain ⟨kp,ks⟩:=live.2 N p here
  have finish:D*g r ≤ ε:=by
    have hh: g r*(1+D) ≤ ε := (le_div_iff₀ pos).mp cheap
    linarith only [hh,live.1]
  calc _ ≤ A*(2*g r)^(q+1):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ kp.le ks (q+1)) an
       _=(D*g r)*(g r)^q:=by rw [mul_pow,pow_succ (g r)];dsimp [D];ring
       _ ≤ ε*(g r)^q:=mul_le_mul_of_nonneg_right finish (pow_nonneg live.1.le _)

end YM.Integration.WilsonThermometerUnitFilingCaptureCoupling
