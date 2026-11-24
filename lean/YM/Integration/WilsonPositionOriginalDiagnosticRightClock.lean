import YM.Integration.WilsonPositionOriginalDiagnosticRightTariff
import YM.Integration.WilsonPositionOriginalDiagnosticQIntakePrice
import YM.Integration.WilsonMasterCoordinatePrice

/-! The genuine truncated mixed-clock field program on its common reporting mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightClock
open Finset Filter Lattice Wilson RG PhysicalNext.Repeat.Legato
open MS MS.Land MS.Menus MS.Local.Physical WilsonPositionOriginalDiagnosticRightSeries
open WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckPrescriptionGrowth
open private log_cost from YM.Integration.WilsonPositionOriginalDiagnosticQIntakePrice
open scoped Classical Topology BigOperators Real Polynomial
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "g" m "," N "," per => Pert.Asymptotics.regulatorRun R.family N per m

private theorem warmth {N m per:ℕ}(admitted:m≤N):β m*(g m,N,per)^2≤4:=by
  have law:=R.makes.wilson.represents N per m admitted
  have pos:0<R.family.path.β N per m:=Overlay.beta_positive R.makes.wilson (N:=N) (p:=per) admitted
  change β m*(Real.sqrt (R.family.path.β N per m))⁻¹^2≤4
  rw [inv_pow,Real.sq_sqrt pos.le,←div_eq_mul_inv]
  have native:β m/2≤R.family.path.β N per m:=law.band.1
  exact (div_le_iff₀ pos).2 (by linarith only [native,pos])

private theorem budget (simple:G.Simple)(A:ℝ)(hp:0≤A)(d:ℕ):
    ∀ᶠ m:ℕ in atTop,∀N per,m≤N→ A*(1+Λ m)^d *(g m,N,per)^2≤1:=by
  have cost:=log_cost d (4*Real.exp 2*A) 1 (by positivity) zero_lt_one
  have growth:=RG05Readout.lambda_growth simple R.family.path.levels
  filter_upwards [growth.eventually cost] with m pay
  intro N per admitted
  have bp:=WardBin.hot R.family.path.levels m
  have recover:Real.exp (Λ m)=Real.exp 2*β m:=by change Real.exp (2+Real.log (β m))=_;rw [Real.exp_add,Real.exp_log bp]
  change Real.exp (-(Λ m)*1)*(4*Real.exp 2*A*(1+Λ m)^d)≤1 at pay
  simp only [mul_one,Real.exp_neg] at pay
  rw [mul_comm,←div_eq_mul_inv,div_le_one (Real.exp_pos _),recover] at pay
  have bounded:A*(1+Λ m)^d*4 ≤ β m:=by nlinarith only [pay,Real.exp_pos 2]
  have bought:=mul_le_mul_of_nonneg_right bounded (sq_nonneg (g m,N,per))
  nlinarith only [bought,warmth R (per:=per) admitted]

/-- At a chosen reporter, the actual measured coupling pays the whole two-clock
field error for every original relative clock in a fixed polylogarithmic range. -/
theorem original (simple:G.Simple)(A:ℝ)(hp:0≤A)(b p:ℕ):
    ∀ᶠ m:ℕ in atTop,∀ N per,m≤N→∀μ ν:ℝ,
      size μ ν≤A*(1+Λ m)^b→∀i j:Glyph B h,
      let x:ℂ:=g m,N,per
      ‖∑ a:Glyph B h,(sources Q h μ (p+2) i a).eval x*(change Q h μ ν (p+2) a j).eval x
        -(sources Q h ν (p+2) i j).eval x‖ ≤ (g m,N,per)^(p+1):=by
  obtain ⟨C,cp,d,price⟩:=WilsonPositionOriginalDiagnosticRightTariff.original Q h (p+2)
  have cost:=budget R simple (C*A^d) (by positivity) (b*d)
  have cap:=budget R simple 1 zero_le_one 0
  filter_upwards [cost,cap] with m priced capped
  intro N per live μ ν allowed i j
  let y:=g m,N,per
  have yp:0<y:=ActualRunKernelPackets.regulator_pos R N per m live
  have small:y≤1:=by have v:=capped N per live;simp only [pow_zero,one_mul] at v;nlinarith only [v]
  have one:‖(y:ℂ)‖≤1:=by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos yp] using small
  have raw:=price μ ν (y:ℂ) one i j
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos yp] at raw
  have perClock:C*(size μ ν)^d *y^2 ≤1:=by
    calc
      _ ≤ C*(A*(1+Λ m)^b)^d *y^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (size_ge _ _)) allowed d) cp.le) (sq_nonneg y)
      _ = (C*A^d)*(1+Λ m)^(b*d)*y^2 :=by rw [mul_pow,pow_mul];ring
      _ ≤ _ :=priced N per live
  apply raw.trans
  calc
    _ = (C*(size μ ν)^d*y^2)*y^(p+1) :=by ring
    _ ≤ _ :=by simpa only [one_mul] using mul_le_mul_of_nonneg_right perClock (pow_nonneg yp.le (p+1))

end YM.Integration.WilsonPositionOriginalDiagnosticRightClock
