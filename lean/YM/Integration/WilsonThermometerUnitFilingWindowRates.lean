import YM.Integration.WilsonThermometerUnitFilingSpan

/-! Convert the one-mark fee, reported one date before its deposition, on the short actual stationary window. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWindowRates
open Function Filter Finset MeasureTheory Real Lattice Wilson RG RG16
open PhysicalNext PhysicalNext.Repeat Legato Pert.Asymptotics
open Overlay OPE OPE.Orbits OPE.Nesting Trace.Pilot RG17 Spec
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "hat!" i:max => R.family.path.levels.clock.hatBeta i
local notation "σ" => R.family.S.scale

private theorem small {D:ℝ} (dp:0≤D):∀ᶠ x:ℝ in atTop,D*(1+Real.log x)≤x/2:=by
  have high : 0 < 4*(D+1):=by linarith
  have little:=Real.isLittleO_log_id_atTop.bound (show 0<(1:ℝ)/(4*(D+1)) from one_div_pos.mpr high)
  filter_upwards [little,eventually_ge_atTop (4*(D+1)),eventually_ge_atTop (1:ℝ)] with x bound large one
  have xp:0<x:=zero_lt_one.trans_le one
  have lp:0≤Real.log x:=Real.log_nonneg one
  change ‖Real.log x‖≤1/(4*(D+1))*‖x‖ at bound
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg lp,abs_of_pos xp,one_div,inv_mul_eq_div] at bound
  have out:=(le_div_iff₀ high).1 bound
  nlinarith only [out,large,lp,dp]

private theorem count (a b:ℕ) (h:a≤b):
    ((Finset.Ico a b).card:ℝ)*Real.log 2 ≤ σ b-σ a:=by
  let f:=fun j:ℕ=>σ j-(j:ℝ)*Real.log 2
  have mono:Monotone f:=by
    apply monotone_nat_of_le_succ
    intro j
    have large:2 ≤ ((C).S.block j).val:=(by decide:2≤3).trans ((C).S.block_large j)
    have bigger:=Real.log_le_log (by norm_num:0<(2:ℝ)) (show (2:ℝ)≤((C).S.block j).val by exact_mod_cast large)
    dsimp [f];rw [(C).S.scale_succ,Nat.cast_add_one];linarith
  have bound:=mono h
  dsimp [f] at bound
  rw [Nat.card_Ico,Nat.cast_sub h];linarith

include simple in
theorem increasing:Monotone (fun i:ℕ=>hat! i):=by
  apply monotone_nat_of_le_succ
  intro i
  have positive:=Real.log_pos (show (1:ℝ)<((C).S.block i).val by
    exact_mod_cast (by omega:(1:ℕ)<3).trans_le ((C).S.block_large i))
  have slope:=Gauge.slopeConstant_pos simple
  change _+G.slopeConstant*σ i ≤ _+G.slopeConstant*σ (i+1)
  rw [(C).S.scale_succ];nlinarith only [mul_nonneg slope.le positive.le]

private theorem span {K:ℝ} (kp:0≤K) {x:ℝ} (xp:1≤x):
    K*Real.log (4*x)+(1+Real.log x) ≤ (5*K+2)*(1+Real.log x):=by
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le xp).ne']
  have logp:=Real.log_nonneg xp
  have four:=Real.log_le_self (by norm_num:0≤(4:ℝ))
  nlinarith [mul_nonneg kp logp,mul_le_mul_of_nonneg_left four kp]

include simple in
theorem original : ∃ u:ℕ,∀ K:ℝ,0≤K → ∀ᶠ b:ℕ in atTop,∀v:ℕ,u ≤ v → v ≤ b →
    σ b-σ v ≤ K*Real.log (4*(hat! b))+(1+Real.log (hat! b)) →
    ∀ N per:ℕ,b < N →
      let g:=regulatorRun C N per (b+1)
      0<g ∧ (hat! b)*g^2 ≤ 2 ∧
        ((Finset.Ico v b).card:ℝ) ≤ (2*(5*K+2)/Real.log 2)*(hat! b) ∧
        ∀j∈Finset.Ico v b,0 ≤ regulatorRun C N per (j-1) ∧ regulatorRun C N per (j-1) ≤ 8*g:=by
  obtain ⟨j₀,next⟩:=eventually_atTop.1 (RG01.Physical.nextHat simple R.alloy.B.a)
  refine ⟨j₀+1,?_⟩
  intro K kp
  have slope:=Gauge.slopeConstant_pos simple
  have kd:0 ≤ G.slopeConstant*(5*K+2):=by positivity
  have rate:=Next.Rank.Station.hat_rate (C).path.levels simple
  filter_upwards [rate (small kd),eventually_ge_atTop j₀] with b enough late
  change G.slopeConstant*(5*K+2)*(1+Real.log (hat! b)) ≤ (hat! b)/2 at enough
  intro v fresh vb short N per above
  have jp:1≤hat! b:=((C).path.levels.fits.delayed b).le
  have sub:σ b-σ v ≤ (5*K+2)*(1+Real.log (hat! b)):=short.trans (span kp jp)
  have affine:(hat! b)-(hat! v)=G.slopeConstant*(σ b-σ v):=by dsimp [Calendar.hatBeta];ring
  have prior:(hat! b)/2 ≤ hat! v:=by
    have scaled:=mul_le_mul_of_nonneg_left sub slope.le
    rw [←affine] at scaled
    nlinarith only [scaled,enough]
  have theCount:=count R v b vb
  have two:0 < Real.log 2:=Real.log_pos (by norm_num)
  have census:((Finset.Ico v b).card:ℝ) ≤ (2*(5*K+2)/Real.log 2)*(hat! b):=by
    have pay:=mul_le_mul_of_nonneg_left (Real.log_le_self (zero_le_one.trans jp)) (show 0 ≤ 5*K+2 by positivity)
    have extra:=mul_le_mul_of_nonneg_left jp (show 0 ≤ 5*K+2 by positivity)
    rw [div_mul_eq_mul_div,(le_div_iff₀ two)]
    nlinarith only [theCount,sub,pay,extra]
  let beta:=fun i=>(C).path.rep N per i |>.beta
  have band:((hat! (b+1))/2 ≤ beta (b+1)) ∧ beta (b+1) ≤ 2*(hat! (b+1)):=
    (R.makes.wilson.represents N per (b+1) above).band
  have upper:0 < beta (b+1):=(half_pos (zero_lt_one.trans ((C).path.levels.fits.delayed (b+1)))).trans_le band.1
  have mono:=increasing R simple
  have arrival:(hat! (b+1))≤2*(hat! b):=next b late
  have hpos:=Real.sqrt_pos.mpr upper
  have gpos:0<regulatorRun C N per (b+1):=inv_pos.mpr hpos
  have thermal:(hat! b)*(regulatorRun C N per (b+1))^2 ≤ 2:=by
    change (hat! b)*(Real.sqrt (beta (b+1)))⁻¹^2 ≤ 2
    rw [inv_pow,Real.sq_sqrt upper.le,←div_eq_mul_inv,(div_le_iff₀ upper)]
    linarith only [band.1,mono (Nat.le_succ b)]
  refine ⟨gpos,thermal,census,?_⟩
  intro j joined
  obtain ⟨vj,jb⟩:=mem_Ico.mp joined
  have realj:j-1+1=j:=by omega
  have jbefore:j-1 ≤ N:=by omega
  have start:(hat! j) ≤ 2*(hat! (j-1)):=by
    have bought:=next (j-1) (by omega)
    change (hat! (j-1+1)) ≤ 2*(hat! (j-1)) at bought
    rwa [realj] at bought
  have lower:(hat! (j-1))/2 ≤ beta (j-1):=(R.makes.wilson.represents N per (j-1) jbefore).band.1
  have early:0<beta (j-1):=(half_pos (zero_lt_one.trans ((C).path.levels.fits.delayed (j-1)))).trans_le lower
  have central:beta (b+1) ≤ 64*beta (j-1):=by linarith only [prior,mono vj,arrival,band.2,start,lower,early]
  have roots:=Real.sqrt_le_sqrt central
  rw [Real.sqrt_mul (by norm_num:0 ≤ (64:ℝ))] at roots
  have easy:Real.sqrt (64:ℝ)=8:=by norm_num
  rw [easy] at roots
  have left:=Real.sqrt_pos.mpr early
  refine ⟨(inv_pos.mpr left).le,?_⟩
  change (Real.sqrt (beta (j-1)))⁻¹ ≤ 8*(Real.sqrt (beta (b+1)))⁻¹
  rw [←div_eq_mul_inv,(le_div_iff₀ hpos)]
  rwa [inv_mul_eq_div,(div_le_iff₀ left)]

end YM.Integration.WilsonThermometerUnitFilingWindowRates
