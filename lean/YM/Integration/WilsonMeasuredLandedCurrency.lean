import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonOlderSignedOneMarkBooked

/-! The salary of an independently normalized singleton at its actual date.
Two fixed powers pay both the filed section and its semester bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredLandedCurrency
open Filter RG Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open Lattice Wilson AllOrder PhysicalNext PhysicalNext.Repeat
open Push Push.PriceCompiler Pert.Asymptotics Extra.Histories ConnectedActivityE6
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open scoped Classical Topology

def first {G:Gauge} (R:Run G) (simple:G.Simple) : ℕ :=
  (eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)).choose

theorem native {G:Gauge} (R:Run G) (simple:G.Simple) {j N:ℕ} (per:ℕ)
    (live:j+1 ≤ N) (late:first R simple ≤ j) :
    let z:=R.alloy.B.a.clock.hatBeta ((j+1)+1)
    let g:=regulatorRun R.family N per j
    1 ≤ z ∧ 0 < g ∧ z*g^2 ≤ 8 ∧ g ≤ 3*regulatorRun R.family N per (j+1) := by
  intro z g
  let B:=R.alloy.B.a.clock
  let β:=(R.family.path.rep N per j).beta
  let β₁:=(R.family.path.rep N per (j+1)).beta
  have bj:j ≤ N:=Nat.le_trans (Nat.le_succ _) live
  have δ:0<β:=Overlay.beta_positive R.makes.wilson bj
  have δ₁:0<β₁:=Overlay.beta_positive R.makes.wilson live
  have bound: B.hatBeta j/2 ≤ β := (R.makes.wilson.represents N per j bj).band.1
  have high: β₁ ≤ 2*B.hatBeta (j+1) := (R.makes.wilson.represents N per (j+1) live).band.2
  have step:= (eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)).choose_spec
  have a:B.hatBeta (j+1) ≤ 2*B.hatBeta j := step j late
  have b:z ≤ 2*B.hatBeta (j+1) := step (j+1) (late.trans (Nat.le_succ j))
  have root:0<Real.sqrt β:=Real.sqrt_pos.mpr δ
  have root₁:0<Real.sqrt β₁:=Real.sqrt_pos.mpr δ₁
  have small:β₁ ≤ 8*β:=by linarith only [high,a,bound]
  refine ⟨(R.alloy.B.a.fits.delayed _).le, inv_pos.mpr root,?_,?_⟩
  · change z*((Real.sqrt β)⁻¹)^2 ≤ 8
    rw [inv_pow,Real.sq_sqrt δ.le,← div_eq_mul_inv,div_le_iff₀ δ]
    linarith only [a,b,bound]
  · change (Real.sqrt β)⁻¹ ≤ 3*(Real.sqrt β₁)⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ root₁,inv_mul_eq_div,div_le_iff₀ root]
    have sq:(Real.sqrt β₁)^2 ≤ (3*Real.sqrt β)^2:=by
      rw [mul_pow,Real.sq_sqrt δ.le,Real.sq_sqrt δ₁.le]
      linarith only [small,δ]
    nlinarith only [sq,root,root₁]

/-- Restore the original radius using the separate pre-test square-root
bounds for the actual semester expense and the independently filed roster. -/
theorem restored {q:ℕ} {z g w Ω H D t ε:ℝ}
    (positive:0<w) (base:1 ≤ z) (gp:0<g) (band:z*g^2 ≤ 8) (scale:1 ≤ D)
    (semester:Ω ≤ z^((1:ℝ)/2)) (roster:H ≤ z^((1:ℝ)/2)*D)
    (wallet:w⁻¹ ≤ max 1 Ω*(1+H)) (ep:0 ≤ ε)
    (paid:w*t ≤ (ε/16)*g^(q+2)) : t ≤ (ε*g^q)*D := by
  let a:=Real.sqrt z
  have zn:0 ≤ z:=zero_le_one.trans base
  have floor:1 ≤ a:=by simpa [a] using Real.sqrt_le_sqrt base
  have square:a^2=z:=Real.sq_sqrt zn
  rw [← Real.sqrt_eq_rpow] at semester roster
  have term:0 ≤ a:=floor.trans' zero_le_one
  have radius:w⁻¹ ≤ 2*z*D:=calc
    _ ≤ max 1 Ω*(1+H):=wallet
    _ ≤ max 1 Ω*(1+a*D):=mul_le_mul_of_nonneg_left (by linarith only [roster]) (le_max_left 1 Ω|>.trans' zero_le_one)
    _ ≤ a*(1+a*D):=mul_le_mul_of_nonneg_right (max_le floor semester) (by positivity)
    _ ≤ 2*(a^2)*D:=by nlinarith only [mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le floor scale) term]
    _ = 2*z*D:=by rw [square]
  have priced:=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr positive.le)
  have val:t≤w⁻¹*((ε/16)*g^(q+2)):=by simpa only [← mul_assoc,inv_mul_cancel₀ positive.ne',one_mul] using priced
  calc
    _ ≤ w⁻¹*((ε/16)*g^(q+2)):=val
    _ ≤ (2*z*D)*((ε/16)*g^(q+2)):=mul_le_mul_of_nonneg_right radius (by positivity)
    _ = ((ε*g^q)*D/8)*(z*g^2):=by rw [pow_add];ring
    _ ≤ ((ε*g^q)*D/8)*8:=mul_le_mul_of_nonneg_left band (by positivity)
    _ = _:=by ring

theorem normalized {q:ℕ} {z g w D t ε:ℝ}
    (positive:0<w) (gp:0<g) (band:z*g^2≤8) (scale:0≤D)
    (wallet:w⁻¹≤2*z*D) (ep:0≤ε)
    (paid:w*t≤(ε/16)*g^(q+2)) : t≤ε*g^q*D := by
  have relax:=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr positive.le)
  have val:t≤w⁻¹*((ε/16)*g^(q+2)):=by
    simpa only [←mul_assoc,inv_mul_cancel₀ positive.ne',one_mul] using relax
  calc
    _ ≤ w⁻¹*((ε/16)*g^(q+2)):=val
    _ ≤ (2*z*D)*((ε/16)*g^(q+2)):=mul_le_mul_of_nonneg_right wallet (by positivity)
    _ = (ε*g^q*D/8)*(z*g^2):=by rw [pow_add];ring
    _ ≤ (ε*g^q*D/8)*8:=mul_le_mul_of_nonneg_left band (by positivity)
    _ = _:=by ring

end YM.Integration.WilsonMeasuredLandedCurrency
