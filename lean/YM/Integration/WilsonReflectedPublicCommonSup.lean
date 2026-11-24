import YM.Integration.WilsonReflectedPublicCommonEstate
import YM.Integration.WilsonThermometerUnitFilingFieldRange

/-! The ordinary part of each of the two actual dosed sources on the canonical Wilson prior. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonSup
open Function Finset Lattice Wilson RG Source Labels Extra.Histories Motion
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonThermometerUnitFilingFieldRange WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family
local notation "P_" => R.family.path.rep N p f
local notation "F_" => R.family.labels.level d
local notation "H_" => R.family.path.levels.clock.hatBeta f
local notation "C_" => 6+basisCost G d
local notation "Ω_" => orbitCost ((C₀).labels.level d)
local notation "wage_" => WilsonReflectedPublicMountedInvoice.wage R f

theorem threshold (cut:f ≤ N):cost G d (P_).p.threshold+1 ≤ (C_)*(H_)^d:=by
  let L:=R.family.path.levels
  let H:=L.clock.hatBeta f
  have one:1 ≤ H:=(L.fits.delayed f).le
  have pos:0 ≤ H:=zero_le_one.trans one
  have monitor:1 ≤ L.clock.monitor f:=Real.one_le_exp (sq_nonneg _)
  have root:Real.sqrt H ≤ H:=by
    have lower:=Real.sqrt_le_sqrt one
    rw [Real.sqrt_one] at lower
    nlinarith only [lower,Real.sqrt_nonneg H,Real.sq_sqrt pos]
  have upper:(L.clock.threshold f)⁻¹ ≤ H:=by
    change ((_ : ℝ)⁻¹ * L.clock.monitor f)⁻¹ ≤ H
    rw [mul_inv_rev,inv_inv]
    exact (mul_le_mul_of_nonneg_right ((inv_le_one₀ (zero_lt_one.trans_le monitor)).mpr monitor)
      (Real.sqrt_nonneg _)).trans ((one_mul _).le.trans root)
  have placed:(P_).p.threshold=L.clock.threshold f:=
    congrArg (fun (w:BudgetPoint)=>w.threshold) (R.makes.wilson.represents N p f cut).vac
  have wk:(max 1 (P_).p.threshold⁻¹)^d ≤ H^d:=
    pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (max_le one (placed ▸ upper)) _
  have basis:0 ≤ basisCost G d:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have bill:=mul_le_mul_of_nonneg_left wk basis
  have ground:1 ≤ H^d:=one_le_pow₀ one
  change 1+basisCost G d*(max 1 (P_).p.threshold⁻¹)^d+1 ≤ (6+basisCost G d)*H^d
  linarith

private theorem wage (f:ℕ):0 ≤ WilsonReflectedPublicMountedInvoice.wage R f ∧
    WilsonReflectedPublicMountedInvoice.wage R f ≤ 2*R.family.path.levels.clock.hatBeta f:=by
  let H:=R.family.path.levels.clock.hatBeta f
  have one:1 ≤ H:=(R.family.path.levels.fits.delayed f).le
  have hp:0 < H:=zero_lt_one.trans_le one
  have lp:0 ≤ Real.log H:=Real.log_nonneg one
  have pos:0 < 2+Real.log H:=by linarith
  have low:0 ≤ Real.log (2+Real.log H):=Real.log_nonneg (by linarith)
  change 0 ≤ 1+Real.log (2+Real.log H) ∧ 1+Real.log (2+Real.log H) ≤ 2*H
  constructor <;> linarith only [low,one,Real.log_le_sub_one_of_pos pos,Real.log_le_sub_one_of_pos hp]

theorem original (A:Arm R d N p f K)(fk:f ≤ K)(kn:K ≤ N)(c:ℂ)(row:Three G ((C₀).side f p))
    (q:ℕ)(X E:Coefficient (F_) ((C₀).side f p))
    (given:Joined R A fk kn c row wage_ (Ω_*(1+wage_)) ((2+Ω_)*((H_)^(q+d))⁻¹) X E):
    ∀U,‖X.exponentialEntry A.o ((C₀).localSection d) (P_) U‖ ≤ 3*Ω_*(C_)*(H_)^(d+1) ∧
      ‖E.exponentialEntry A.o ((C₀).localSection d) (P_) U‖ ≤ (C_)*(2+Ω_)*((H_)^q)⁻¹:=by
  let H:=R.family.path.levels.clock.hatBeta f
  let k:=cost G d (P_).p.threshold
  let C:=6+basisCost G d
  let Ω:=orbitCost ((C₀).labels.level d)
  let w:=wage_
  let a:=(2+Ω)*(H^(q+d))⁻¹
  have one:1 ≤ H:=(R.family.path.levels.fits.delayed f).le
  have hp:0 < H:=zero_lt_one.trans_le one
  have basis:0 ≤ basisCost G d:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have kp:0 ≤ k:=add_nonneg zero_le_one (mul_nonneg basis (pow_nonneg (zero_le_one.trans (le_max_left ..)) _))
  have cp:0 ≤ C:=by dsimp only [C];linarith
  have op:1 ≤ Ω:=orbitCost_one_le _
  have oz:0 ≤ Ω:=zero_le_one.trans op
  have salary:k+1 ≤ C*H^d:=threshold R (fk.trans kn)
  have bill:=wage R f
  have earned:0 ≤ a:=mul_nonneg (by linarith only [oz]) (inv_nonneg.mpr (pow_nonneg hp.le _))
  have fees:Ω*(1+w) ≤ Ω*(3*H):=mul_le_mul_of_nonneg_left (by linarith only [one,bill.2]) oz
  have fit:w ≤ Ω*(1+w):=by
    have h:=le_mul_of_one_le_left (by linarith only [bill.1]:0 ≤ 1+w) op
    linarith only [h]
  intro U
  constructor
  · have shown:=point R d (P_) X A.o given.cash.2 U
    calc
      _ ≤ k*(F_).coeffSize X.x+w:=shown
      _ ≤ k*(Ω*(1+w))+Ω*(1+w):=add_le_add (mul_le_mul_of_nonneg_left given.coordinate kp) fit
      _ = (k+1)*(Ω*(1+w)):=by ring
      _ ≤ (C*H^d)*(Ω*(3*H)):=mul_le_mul salary fees (mul_nonneg oz (by linarith only [bill.1])) (mul_nonneg cp (pow_nonneg hp.le _))
      _ = _:=by change _=3*Ω*C*H^(d+1);rw [pow_succ];ring
  · have shown:=point R d (P_) E A.o given.difference.paid U
    calc
      _ ≤ k*(F_).coeffSize E.x+a:=shown
      _ ≤ k*a+a:=add_le_add (mul_le_mul_of_nonneg_left given.difference.primary kp) (le_refl a)
      _ = (k+1)*a:=by ring
      _ ≤ (C*H^d)*a:=mul_le_mul_of_nonneg_right salary earned
      _ = _:=by change (C*H^d)*((2+Ω)*(H^(q+d))⁻¹)=C*(2+Ω)*(H^q)⁻¹
                rw [pow_add];field_simp [hp.ne']

end YM.Integration.WilsonReflectedPublicCommonSup
end
