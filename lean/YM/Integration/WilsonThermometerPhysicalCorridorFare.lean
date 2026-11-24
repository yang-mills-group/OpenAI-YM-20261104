import YM.Integration.WilsonThermometerMixedColdShoulder
import YM.Integration.WilsonCloseCaptureDate

/- Each physical re-enrollment costs a fixed power of the actual upper clock per
   occupied label. The separation gain at the real fine date pays the whole number
   of such purchases up to the original enclosing cell, uniformly in both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPhysicalCorridorFare
open Filter Lattice Wilson RG Source PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

private theorem logFee (C D:ℝ)(cc:0≤C)(dd:0≤D) :
    ∀ᶠ z:ℝ in atTop, 16*(C*Real.log z+D)≤ z-2 := by
  have ep:0<1/(64*(C+1)):=by positivity
  have little:=Real.isLittleO_log_id_atTop.bound ep
  filter_upwards [little,eventually_ge_atTop (64*(D+1)),eventually_ge_atTop (1:ℝ)]
    with z small big one
  have zp:0≤z:=zero_le_one.trans one
  change ‖Real.log z‖≤(1/(64*(C+1)))*‖z‖ at small
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg one),abs_of_nonneg zp] at small
  have r:0<64*(C+1):=by positivity
  have paid:Real.log z*(64*(C+1))≤z:=by
    apply (le_div_iff₀ r).mp
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using small
  nlinarith only [paid,big,Real.log_nonneg one,cc,dd]

private theorem absorb {x:ℝ}{b:ℕ}(d q:ℕ)(xp:0<x)(thick:(Real.log x)^2≤(b:ℝ))
    (invoice:16*((d:ℝ)+(q:ℝ)+1)≤Real.log x):
    Real.exp (-(b/8:ℕ):ℝ)*x^d ≤ (x^q)⁻¹:=by
  have rounded:b≤8*(b/8)+7:=by omega
  have rounded':(b:ℝ)≤8*((b/8:ℕ):ℝ)+7:=by exact_mod_cast rounded
  have lp:0≤Real.log x:=by linarith only [invoice,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) q]
  have both:=mul_le_mul_of_nonneg_right invoice lp
  have nonneg:=mul_nonneg (add_nonneg (Nat.cast_nonneg (α:=ℝ) d) (Nat.cast_nonneg (α:=ℝ) q)) lp
  have cover:((d+q:ℕ):ℝ)*Real.log x≤(b/8:ℕ):=by
    push_cast
    nlinarith only [thick,rounded',both,invoice,nonneg,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) q]
  rw [←one_div];apply (le_div_iff₀ (pow_pos xp _)).mpr
  calc
    _ = Real.exp (-(b/8:ℕ):ℝ)*x^(d+q):=by rw [pow_add];ring
    _ = Real.exp (-((b/8:ℕ):ℝ)+((d+q:ℕ):ℝ)*Real.log x):=by
      rw [Real.exp_add,←Real.log_pow,Real.exp_log (pow_pos xp _)]
    _ ≤ 1:=Real.exp_le_one_iff.mpr (by linarith only [cover])

include simple in
theorem original (c k d q:ℕ):∀ᶠ f:ℕ in atTop, ∀n:ℕ,
    (n:ℝ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 → ∀N per:ℕ,f≤N →
    Real.exp (-((((A).budget f).B/8:ℕ):ℝ))*(H f)^(k*n+d)≤(regulatorRun R.family N per f)^q:=by
  let C:ℝ:=(k:ℝ)*c
  let D:ℝ:=2*(k:ℝ)+d+q+1
  have grows:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have rises:Tendsto (fun f:ℕ=>2+Real.log (H f)) atTop atTop:=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp grows)
  filter_upwards [rises.eventually (logFee C D (by dsimp [C];positivity) (by dsimp [D];positivity)),
    grows.eventually_ge_atTop (2:ℝ)] with f price hot n span N per top
  let x:=H f
  let g:=regulatorRun R.family N per f
  have xp:0<x:=by dsimp [x];linarith only [hot]
  have taxed:16*(((k*n+d:ℕ):ℝ)+(q:ℝ)+1)≤Real.log x:=by
    change 16*(C*Real.log (2+Real.log x)+D)≤2+Real.log x-2 at price
    change (n:ℝ)≤(c:ℝ)*Real.log (2+Real.log x)+2 at span
    have step:=mul_le_mul_of_nonneg_left span (Nat.cast_nonneg (α:=ℝ) k)
    dsimp [C,D] at price
    push_cast
    nlinarith only [price,step]
  have fee:=absorb (b:=((A).budget f).B) (k*n+d) q xp (Nat.le_ceil _) taxed
  have gp:=ActualRunKernelPackets.regulator_pos R N per f top
  have cap:= (R.makes.wilson.represents N per f top).band.2
  let β:=R.family.path.β N per f
  change β≤2*x at cap
  have bcap:β≤x^2:=by
    change 2≤x at hot
    nlinarith only [cap,mul_nonneg (show 0≤x-2 by linarith only [hot]) xp.le]
  have tip:0<Real.sqrt β:=inv_pos.mp gp
  have bound:x⁻¹≤g:=(inv_le_inv₀ xp tip).mpr ((Real.sqrt_le_iff).mpr ⟨xp.le,bcap⟩)
  exact fee.trans ((inv_pow ..).symm.le.trans (pow_le_pow_left₀ (inv_nonneg.mpr xp.le) bound _))

theorem calendar (slow:WilsonWindowReportingPace.Slow R.kit) (v:ℕ)(vp:0<v)(k d q:ℕ):
    ∀ᶠ r:ℝ in 𝓝[>]0, let b:=WilsonCloseCaptureDate.level R.family.S r
    let f:=WilsonMeasuredWindow.stop (A) simple v r
    b<f ∧ r≤R.family.S.a b ∧ ∀N per:ℕ,f≤N →
      Real.exp (-((((A).budget f).B/8:ℕ):ℝ))*(H f)^(k*(f-(b-1))+d)≤(regulatorRun R.family N per f)^q:=by
  have go:=WilsonMeasuredWindow.stop_tendsto (A) simple v vp
  filter_upwards [go.eventually (original R simple (v+2) k d q),self_mem_nhdsWithin,
    (show Set.Iio (R.family.S.a 0) ∈ 𝓝[>] (0:ℝ) from nhdsWithin_le_nhds (Iio_mem_nhds (R.family.S.a_pos 0)))] with r charge pos small
  have span:=WilsonCloseCaptureDate.window R slow simple vp pos (le_of_lt small)
  dsimp only
  dsimp only at span
  obtain ⟨bf,_,room,_,legs,scale⟩:=span
  refine ⟨bf,room,charge _ ?_⟩
  have extra:WilsonMeasuredWindow.stop (A) simple v r-(WilsonCloseCaptureDate.level R.family.S r-1)≤
      (WilsonMeasuredWindow.stop (A) simple v r-WilsonCloseCaptureDate.level R.family.S r)+1:=by omega
  have extra':(((WilsonMeasuredWindow.stop (A) simple v r-(WilsonCloseCaptureDate.level R.family.S r-1):ℕ)):ℝ)≤
      ((WilsonMeasuredWindow.stop (A) simple v r-WilsonCloseCaptureDate.level R.family.S r:ℕ):ℝ)+1:=by exact_mod_cast extra
  linarith only [extra',legs.trans scale]
end YM.Integration.WilsonThermometerPhysicalCorridorFare
end
