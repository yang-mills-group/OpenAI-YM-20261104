import YM.Integration.WilsonCenteredReporterClock
import YM.Integration.WilsonIndependentCapturedPages

/-! The measured coupling at the actual captured date pays the adjacent
reporter and the infrared gap of the original and independent common stop. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRClock
open Filter RG Wilson Lattice PhysicalNext.Repeat.Legato Pert.Asymptotics RG16
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "gs" N:max p:max c:max => regulatorRun R.family N p c

theorem adjacent (simple:G.Simple):
    ∀ᶠ c:ℕ in atTop,∀N per,c<N →
      (gs N per (c+1))⁻¹≤3*(gs N per c)⁻¹:=by
  filter_upwards [RG01.Physical.nextHat simple R.alloy.B.a] with c neighbor N per top
  have pos:0<(C).path.β N per c:=Overlay.beta_positive R.makes.wilson top.le
  have base:β c/2≤(C).path.β N per c:=(R.makes.wilson.represents N per c top.le).band.1
  have recent:(C).path.β N per (c+1)≤2*β (c+1):=(R.makes.wilson.represents N per (c+1) top).band.2
  change (Real.sqrt ((C).path.β N per (c+1)))⁻¹⁻¹≤3*(Real.sqrt ((C).path.β N per c))⁻¹⁻¹
  rw [inv_inv,inv_inv]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,Real.sq_sqrt pos.le]
  change β (c+1) ≤ 2*β c at neighbor
  linarith

theorem decay {c v P D:ℕ}{g:ℝ}(gp:0<g)
    (reach:a c/a v≤(g^(4*(P+D)))^2):
    Real.exp (-(σ c-σ v)/8) ≤ g^(P+D):=by
  have price:=Real.log_le_log (div_pos ((C).S.a_pos _) ((C).S.a_pos _)) reach
  rw [WilsonIndependentCapturedDates.mesh, Real.log_pow, Real.log_pow, ←Real.exp_log (pow_pos gp (P+D))] at *
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  push_cast at *
  linarith

theorem spend {c v P D:ℕ}{g M A:ℝ}(gp:0<g)(ap:0≤A)
    (reach:a c/a v≤(g^(4*(P+D)))^2)
    (price:M≤A*(g⁻¹)^D):
    M*Real.exp (-(σ c-σ v)/8)≤A*g^P:=by
  calc _≤(A*(g⁻¹)^D)*g^(P+D):=mul_le_mul price (decay R gp reach) (Real.exp_nonneg _)
        (mul_nonneg ap (pow_nonneg (inv_nonneg.mpr gp.le) _))
       _=A*g^P:=by rw [pow_add,inv_pow];field_simp

end YM.Integration.WilsonOriginalTwoFlatIRClock
