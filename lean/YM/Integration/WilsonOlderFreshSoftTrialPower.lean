import YM.Integration.WilsonOlderFreshSoftTrialSalary

/-! Gross income of every original funded face, in the measured planting coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialPower
open Filter Finset Function MeasureTheory Lattice RG Wilson Pert.Asymptotics Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialFigure WilsonOriginalPublicTrialNormalization
open WilsonOriginalPublicTrialInput
open WilsonOriginalMicroscopicGuardedPage WilsonOlderFreshSoftTrialSalary
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "Ĥ" => R.family.path.levels.clock.hatBeta

def exposure (d ℓ:ℕ)(m η D₁ D₂:ℝ):ℝ:=2*(m+2)+ℓ+η*D₁+d*D₂

theorem heat (simple:G.Simple)(N per j K:ℕ)(jk:j≤K)(live:K≤N):
    0<regulatorRun R.family N per K ∧ Ĥ j≤2*Real.exp (2*Real.log (regulatorRun R.family N per K)⁻¹):=by
  have band:=(R.makes.wilson.represents N per K live).band.1
  change Ĥ K/2≤R.family.path.β N per K at band
  have warm:0<R.family.path.β N per K:=(half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed K))).trans_le band
  have mono:=WilsonStartup.Timing.hat_mono L (Gauge.slopeConstant_pos simple).le jk
  have sq:=Real.sq_sqrt warm.le
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr warm),?_⟩
  unfold regulatorRun
  rw [inv_inv,two_mul (Real.log _),Real.exp_add,Real.exp_log (Real.sqrt_pos.mpr warm),←pow_two,sq]
  linarith only [band,mono]

private theorem amount (d ℓ:ℕ)(base H M C paid s m η D₁ D₂ span:ℝ)
    (b0:0≤base)(h0:0≤H)(_p0:0≤paid)(M0:0≤M)(η0:0≤η)
    (h:H≤2*Real.exp (2*s))(salary:M≤C*Real.exp ((2*m)*s))
    (stretch:span≤D₁*s)(position:paid≤Real.exp ((d:ℝ)*D₂*s)):
    paid*(base*H^2*M*Real.exp ((ℓ:ℝ)*s+η*span))≤
      (4*base*C)*Real.exp (exposure d ℓ m η D₁ D₂*s):=by
  have c0:0≤C:=by
    by_contra! hC
    exact (not_lt_of_ge (M0.trans salary)) (mul_neg_of_neg_of_pos hC (Real.exp_pos _))
  calc
    _ ≤ Real.exp ((d:ℝ)*D₂*s)*(base*(2*Real.exp (2*s))^2*(C*Real.exp ((2*m)*s))*
      Real.exp ((ℓ:ℝ)*s+η*(D₁*s))):=by gcongr
    _ = _:=by
      have bill:exposure d ℓ m η D₁ D₂*s=(d:ℝ)*D₂*s+2*s+2*s+(2*m)*s+((ℓ:ℝ)*s+η*(D₁*s)):=by unfold exposure;ring
      rw [bill];simp_rw [Real.exp_add];ring

theorem total {α:Type}[Fintype α](d ℓ:α→ℕ)(base H M C paid m D₁ D₂ span:α→ℝ)(η s:ℝ)
    (b0:∀i,0≤base i)(h0:∀i,0≤H i)(p0:∀i,0≤paid i)(M0:∀i,0≤M i)(η0:0≤η)
    (h:∀i,H i≤2*Real.exp (2*s))(salary:∀i,M i≤C i*Real.exp ((2*m i)*s))
    (stretch:∀i,span i≤D₁ i*s)(position:∀i,paid i≤Real.exp ((d i:ℝ)*D₂ i*s)):
    (∏i,paid i)*(∏i,base i*H i^2*M i*Real.exp ((ℓ i:ℝ)*s+η*span i))≤
      (∏i,4*base i*C i)*Real.exp ((∑i,exposure (d i) (ℓ i) (m i) η (D₁ i) (D₂ i))*s):=by
  rw [←prod_mul_distrib,sum_mul,Real.exp_sum]
  rw [←prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _;exact mul_nonneg (p0 i) (mul_nonneg (mul_nonneg (mul_nonneg (b0 i) (sq_nonneg _)) (M0 i)) (Real.exp_pos _).le)
  · intro i _;exact amount _ _ _ _ _ _ _ _ _ _ _ _ _ (b0 i) (h0 i) (p0 i) (M0 i) η0 (h i) (salary i) (stretch i) (position i)

end YM.Integration.WilsonOlderFreshSoftTrialPower
end
