import YM.Integration.WilsonLocalCompactHistory
import YM.Integration.WilsonCloseCaptureCalendar

/-! The number of retained transitions and every actual finite coupling
are controlled on the logarithmic capture window of the original calendar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactClock
open Filter Set Finset Lattice RG Wilson RG16 Precision Pert.Asymptotics PhysicalNext.Repeat.Legato RG05Readout
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)

private theorem log_small {D:ℝ} (dp:0≤D):∀ᶠx:ℝ in atTop,D*(1+Real.log x)≤x/2:=by
  have high : 0 < 4*(D+1):=by linarith
  have little:=Real.isLittleO_log_id_atTop.bound (show 0<(1:ℝ)/(4*(D+1)) from one_div_pos.mpr high)
  filter_upwards [little,eventually_ge_atTop (4*(D+1)),eventually_ge_atTop (1:ℝ)] with x small large one
  have xp:0<x:=zero_lt_one.trans_le one
  have lp:0≤Real.log x:=Real.log_nonneg one
  change ‖Real.log x‖≤1/(4*(D+1))*‖x‖ at small
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg lp,abs_of_pos xp,one_div,inv_mul_eq_div] at small
  have out:=(le_div_iff₀ high).1 small
  nlinarith only [out,large,lp,dp]

private theorem log_bound {x:ℝ} (xp:1≤x):Real.log (2+Real.log x)≤1+Real.log x:=by
  have lp:=Real.log_nonneg xp
  linarith only [Real.log_le_sub_one_of_pos (show 0<2+Real.log x by linarith)]

private theorem calendar (simple:G.Simple) {B:ℝ} (bp:0<B):
    ∀ᶠb:ℕ in atTop,let A:=R.family.path.levels
    let β:=A.clock.hatBeta b
    4≤β ∧ ∀j:ℕ,j≤b→R.family.S.scale b-R.family.S.scale j≤B*Real.log (RG16.Lambda A b)→
      ((b-j:ℕ):ℝ)≤B*β ∧ (∀ i : ℕ, j ≤ i → i ≤ b → β / 2 ≤ A.clock.hatBeta i) := by
  let A:=R.family.path.levels
  let D:=G.slopeConstant*B
  have sp:=Gauge.slopeConstant_pos simple
  have grow:=Next.Rank.Station.hat_rate A simple
  filter_upwards [grow.eventually_ge_atTop 4,grow.eventually (log_small (D:=D) (mul_nonneg sp.le bp.le))]
    with b high score
  let β:=A.clock.hatBeta b
  refine ⟨high,fun j jb stage=>?_⟩
  have raised:Real.log (RG16.Lambda A b)≤1+Real.log β:=log_bound (by linarith only [high])
  have cutoff:1+Real.log β≤β:=by linarith only [Real.log_le_sub_one_of_pos (show 0<β by linarith only [high])]
  refine ⟨((RG05Readout.Many.tall (C:=R.family) j b jb).trans stage).trans (mul_le_mul_of_nonneg_left (raised.trans cutoff) bp.le),fun i ji ib=>?_⟩
  have inc : R.family.S.scale j≤R.family.S.scale i:=by
    have wide:=RG05Readout.Many.tall (C:=R.family) j i ji
    have positive:0≤((i-j:ℕ):ℝ):=by positivity
    linarith
  have geom:R.family.S.scale b-R.family.S.scale i≤B*(1+Real.log β):=
    (sub_le_sub_left inc _).trans (stage.trans (mul_le_mul_of_nonneg_left raised bp.le))
  have diff:β-A.clock.hatBeta i=G.slopeConstant*(R.family.S.scale b-R.family.S.scale i):=by
    dsimp [β,A,Calendar.hatBeta];ring
  have dob:=mul_le_mul_of_nonneg_left geom sp.le
  change (G.slopeConstant*B)*(1+Real.log β)≤β/2 at score
  linarith only [diff,dob,score]

private theorem square {N per i:ℕ} (put:i≤N):
    regulatorRun R.family N per i^2=1/(R.family.path.β N per i):=by
  have pos:0<R.family.path.β N per i:=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed i))).trans_le (R.makes.wilson.represents N per i put).band.1
  change (Real.sqrt (R.family.path.β N per i))⁻¹^2=1/_
  rw [inv_pow,Real.sq_sqrt pos.le,one_div]

theorem prices (simple:G.Simple) {B:ℝ} (bp:0<B):
    ∀ᶠb:ℕ in atTop,let A:=R.family.path.levels
    let β:=A.clock.hatBeta b
    ∀j:ℕ,j≤b→R.family.S.scale b-R.family.S.scale j≤B*Real.log (RG16.Lambda A b)→
    ∀N:ℕ,b≤N→∀per:ℕ,let g:=regulatorRun R.family N per
    ((b-j:ℕ):ℝ)≤B*β ∧ β*g b^2≤2 ∧ (∀ i : ℕ, j ≤ i → i ≤ b → g i ≤ 1 ∧ g i ≤ 3*g b) := by
  filter_upwards [calendar R simple bp] with b bought
  intro A β j jb stage N top per g
  obtain ⟨len,toll⟩:=bought.2 j jb stage
  let base:=R.family.path.β N per b
  have bpair:= (R.makes.wilson.represents N per b top).band
  change β/2≤base ∧ base≤2*β at bpair
  have bg:4≤β:=bought.1
  have b0:0<base:= (half_pos (zero_lt_one.trans (A.fits.delayed b))).trans_le bpair.1
  have conv:g b^2=1/base:=square R top
  refine ⟨len,?_,fun i ji ib=>?_⟩
  · rw [conv,one_div,←div_eq_mul_inv]
    exact (div_le_iff₀ b0).2 (by linarith only [bpair.1])
  · let a:=R.family.path.β N per i
    have apair:=(R.makes.wilson.represents N per i (ib.trans top)).band
    change A.clock.hatBeta i/2≤a ∧ a≤2*A.clock.hatBeta i at apair
    have gap:β/2≤A.clock.hatBeta i:=toll i ji ib
    have a0:1≤a:=by linarith only [bg,gap,apair.1]
    have ap:0<a:=zero_lt_one.trans_le a0
    have comp:base≤9*a:=by linarith only [gap,apair.1,bpair.2,bg]
    have g0 (l):0≤g l:=inv_nonneg.mpr (Real.sqrt_nonneg _)
    have shift:g i^2=1/a:=square R (ib.trans top)
    refine ⟨(sq_le_sq₀ (g0 i) zero_le_one).1 ?_,(sq_le_sq₀ (g0 i) (mul_nonneg (by norm_num) (g0 b))).1 ?_⟩
    · rw [shift,one_pow];exact (div_le_one ap).2 a0
    · rw [mul_pow,shift,conv,show (3:ℝ)^2*(1/base)=9/base by ring]
      exact (div_le_div_iff₀ ap b0).2 (by simpa only [one_mul] using comp)

end YM.Integration.WilsonLocalCompactClock
