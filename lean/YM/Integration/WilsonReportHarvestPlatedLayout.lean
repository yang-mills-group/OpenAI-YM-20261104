import YM.Integration.WilsonLocalCompactClock
import YM.Integration.WilsonReportHarvestUpperAge
import YM.Integration.WilsonCloseCaptureDate

/-! For the actual near reporting layout, the larger log-temperature
interval from geometric capture still retains comparable physical temperatures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestPlatedLayout
open Filter Set Finset Lattice RG Wilson RG16 Precision Pert.Asymptotics PhysicalNext.Repeat.Legato RG05Readout
open OPE OPE.Log Trace.Pilot
open private log_small square from YM.Integration.WilsonLocalCompactClock
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)(simple:G.Simple)
include simple
local notation "S" => R.family.S
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem clock (level:ℝ→ℕ)(growing:Tendsto level trail atTop)
    (near:∀ᶠr in trail,(S).a (level r)≤r ∧ r≤(S).a (level r)*β (level r)^2):
    ∀ᶠr in trail,let b:=WilsonCloseCaptureDate.level S r
    let j:=level r
    b≤j ∧ ((j-b:ℕ):ℝ)≤3*β j ∧ 4≤β j ∧ (∀ i : ℕ, b ≤ i → i ≤ j → β j / 2 ≤ β i):=by
  let c:=G.slopeConstant
  have cp:0<c:=G.slopeConstant_pos simple
  have hot:=(Next.Rank.Station.hat_rate A simple).comp growing
  have low:=(WilsonCloseCaptureDate.height R).grows
  have small:∀ᶠr in trail,r<(S).a 0:=(eventually_lt_nhds ((S).a_pos 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [near,self_mem_nhdsWithin,small,low.eventually (WilsonReportHarvestUpperAge.block R simple),
    hot.eventually_ge_atTop 4,hot.eventually (log_small (D:=c*3) (by positivity))] with r frame rp rs block high tiny b j
  obtain ⟨past,future⟩:=WilsonCloseCaptureDate.bracket S rp rs.le
  have inc:b≤j:=by
    by_contra! order
    exact (not_lt_of_ge (frame.1.trans future)) ((S).strictAnti order)
  change 4≤β j at high
  have mono {i k:ℕ}(ik:i≤k):β i≤β k:=by
    have tall:=RG05Readout.Many.tall (C:=R.family) i k ik
    have pos:0≤((k-i:ℕ):ℝ):=by positivity
    have s:(S).scale i≤(S).scale k:=by linarith
    have burn:=mul_le_mul_of_nonneg_left s cp.le
    change G.slopeConstant*(S).scale i≤G.slopeConstant*(S).scale k at burn
    dsimp only [Calendar.hatBeta];linarith only [burn]
  have gp:0<β j:=by linarith only [high]
  have bp:0<((S).block b).val:=((S).block b).pos
  have debit:=Real.log_le_log (show 0<(((S).block b).val:ℝ) by exact_mod_cast bp) (block.trans (mono inc))
  have left:=Real.log_lt_log ((S).a_pos _) past
  have right:=Real.log_le_log rp frame.2
  rw [Real.log_mul ((S).a_pos _).ne' (pow_pos gp _).ne',Real.log_pow] at right
  have la i:Real.log ((S).a i) = -(S).scale i:=by simp [Schedule.scale]
  rw [la,Schedule.scale_succ] at left
  rw [la] at right
  change -((S).scale b+Real.log (((S).block b).val:ℝ)) < Real.log r at left
  change Real.log r≤ -(S).scale j+(2:ℝ)*Real.log (β j) at right
  have duration:(S).scale j-(S).scale b≤3*Real.log (β j):=by linarith only [left,right,debit]
  refine ⟨inc,((RG05Readout.Many.tall (C:=R.family) b j inc).trans duration).trans ?_,high,fun i bi _=>?_⟩
  · linarith only [Real.log_le_sub_one_of_pos gp]
  · have dx:β j-β b=c*((S).scale j-(S).scale b):=by dsimp [c,Calendar.hatBeta];ring
    have up:=mul_le_mul_of_nonneg_left duration cp.le
    have hold:β j/2≤β b:=by
      change (c*3)*(1+Real.log (β j))≤β j/2 at tiny
      linarith only [dx,up,tiny,cp]
    exact hold.trans (mono bi)

theorem prices (level:ℝ→ℕ)(growing:Tendsto level trail atTop)
    (near:∀ᶠr in trail,(S).a (level r)≤r ∧ r≤(S).a (level r)*β (level r)^2):
    ∀ᶠr in trail,let b:=WilsonCloseCaptureDate.level S r
    let j:=level r
    b≤j ∧ ∀N,j≤N→∀per,let g:=regulatorRun R.family N per
      ((j-b:ℕ):ℝ)≤3*β j ∧ β j*g j^2≤2 ∧ (∀ i : ℕ, b ≤ i → i ≤ j → g i ≤ 1 ∧ g i ≤ 3*g j):=by
  filter_upwards [clock R simple level growing near] with r clock b j
  refine ⟨clock.1,?_⟩
  intro N top per g
  let base:=R.family.path.β N per j
  have bpair:=(R.makes.wilson.represents N per j top).band
  change β j/2≤base ∧ base≤2*β j at bpair
  have high:=clock.2.2.1
  have b0:0<base:=by linarith only [bpair.1,high]
  have conv:g j^2=1/base:=square R top
  refine ⟨clock.2.1,?_,fun i bi ij=>?_⟩
  · rw [conv,one_div,←div_eq_mul_inv];exact (div_le_iff₀ b0).2 (by linarith only [bpair.1])
  · let a:=R.family.path.β N per i
    have pair:=(R.makes.wilson.represents N per i (ij.trans top)).band
    change β i/2≤a ∧ a≤2*β i at pair
    have gap:=clock.2.2.2 i bi ij
    have one:1≤a:=by linarith only [pair.1,gap,high]
    have ap:0<a:=zero_lt_one.trans_le one
    have comp:base≤9*a:=by linarith only [gap,pair.1,bpair.2,high]
    have g0 k:0≤g k:=inv_nonneg.mpr (Real.sqrt_nonneg _)
    have shift:g i^2=1/a:=square R (ij.trans top)
    refine ⟨(sq_le_sq₀ (g0 i) zero_le_one).1 ?_,(sq_le_sq₀ (g0 i) (mul_nonneg (by norm_num) (g0 j))).1 ?_⟩
    · rw [shift,one_pow];exact (div_le_one ap).2 one
    · rw [mul_pow,shift,conv,show (3:ℝ)^2*(1/base)=9/base by ring]
      exact (div_le_div_iff₀ ap b0).2 (by simpa only [one_mul] using comp)

end YM.Integration.WilsonReportHarvestPlatedLayout
