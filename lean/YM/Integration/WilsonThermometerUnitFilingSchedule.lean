import YM.Integration.WilsonThermometerUnitFilingPlanted
import YM.Integration.WilsonAdmissionScale
import YM.RG12.Common.Short

/-! Numerical return from the shorter stop on the actual Wilson clock.
The interval length uses the fixed pole of the incoming source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingSchedule
open Filter Lattice Wilson RG Labels Source Work.G08 Next.Foundations
open PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical Trace.Physical.GermGraph
open ConnectedActivityE6 Overlay RG16 RG16.Literal
open scoped Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "H" => R.family.path

private theorem column (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)  ≤  Real.log (Lambda ((H).levels) m)) :
    ∀ᶠ m:ℕ in atTop,(((H).levels).params (m+1)).columns  ≤  2*Real.log (((H).levels).clock.hatBeta (m+1)) := by
  have logs:=(tendsto_add_atTop_nat 1).eventually ((WilsonAdmissionScale.logarithm_tendsto ((H).levels) simple).eventually_ge_atTop 2)
  filter_upwards [logs] with m late
  let s:=Real.log (((H).levels).clock.hatBeta (m+1))
  have pos:0<Lambda ((H).levels) m:=by
    change 0<2+Real.log (((H).levels).clock.hatBeta m)
    linarith only [Real.log_pos (((H).levels).fits.delayed m)]
  have mono:Real.log (((H).levels).clock.hatBeta m)  ≤  s:=WilsonAdmissionScale.logarithm_monotone ((H).levels) simple (Nat.le_succ m)
  have two:(2:ℝ)  ≤  s:=late
  calc
    _  ≤  ((R.family.S.block m).val:ℝ):=RG12.Commission.column_priced ((H).levels) m
    _  ≤  Real.log (Lambda ((H).levels) m):=slow m
    _  ≤  Lambda ((H).levels) m:=Real.log_le_self pos.le
    _  ≤  2*s:=by change 2+Real.log (((H).levels).clock.hatBeta m)  ≤  2*s;linarith only [mono,two]

include simple in
theorem clock (slow : ∀ j, ((C).S.block j).val ≤ Real.log (Lambda (H).levels j)) :
    ∀ᶠ i:ℕ in atTop,∀ N per:ℕ,∀ _:i<N,
      let g:=Coat.gStep ((H).rep N per (i+1)).beta
      0<g ∧ g≤1 ∧ ((H).levels.params i).columns*g^2 ≤ 4 := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp (column R simple slow)
  obtain ⟨k,hk⟩ := eventually_atTop.mp
    ((WilsonAdmissionScale.logarithm_tendsto (H).levels simple).eventually_ge_atTop 2)
  refine eventually_atTop.mpr ⟨max (a+1) k,fun i hi N per cut=>?_⟩
  intro g
  have ai : a + 1 ≤ i := (le_max_left _ _).trans hi
  have ki : k ≤ i + 1 := ((le_max_right _ _).trans hi).trans (Nat.le_succ i)
  have c : ((H).levels.params i).columns ≤ 2*Real.log ((H).levels.clock.hatBeta i) := by
    cases i with
    | zero => omega
    | succ j => exact ha j (by omega)
  have mono := WilsonAdmissionScale.logarithm_monotone (H).levels simple (Nat.le_succ i)
  have hp : 0<((H).levels.clock.hatBeta (i+1)) := zero_lt_one.trans ((H).levels.fits.delayed _)
  have big := (hk (i+1) ki).trans (Real.log_le_self hp.le)
  have band := (R.makes.wilson.represents N per (i+1) (Nat.succ_le_of_lt cut)).band
  have b0 : 0<((H).rep N per (i+1)).beta := Overlay.beta_positive R.makes.wilson (Nat.succ_le_of_lt cut)
  have beta : 1 ≤ ((H).rep N per (i+1)).beta := by
    have low : ((H).levels.clock.hatBeta (i+1))/2 ≤ ((H).rep N per (i+1)).beta := band.1
    linarith only [big,low]
  have root : 1 ≤ Real.sqrt (((H).rep N per (i+1)).beta) := by simpa using Real.sqrt_le_sqrt beta
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr b0)
  have temp : ((H).levels.clock.hatBeta (i+1))*g^2 ≤ 2 := by
    have sq : g^2 = (((H).rep N per (i+1)).beta)⁻¹ := by
      change (Real.sqrt (((H).rep N per (i+1)).beta))⁻¹^2=_
      rw [inv_pow,Real.sq_sqrt b0.le]
    rw [sq,←div_eq_mul_inv];apply (div_le_iff₀ b0).2
    have low : ((H).levels.clock.hatBeta (i+1))/2 ≤ ((H).rep N per (i+1)).beta := band.1
    linarith
  refine ⟨gp,inv_le_one_of_one_le₀ root,?_⟩
  have cc : ((H).levels.params i).columns ≤ 2*((H).levels.clock.hatBeta (i+1)) :=
    c.trans (mul_le_mul_of_nonneg_left (mono.trans (Real.log_le_self hp.le)) (by norm_num))
  calc
    _ ≤ (2*((H).levels.clock.hatBeta (i+1)))*g^2 := mul_le_mul_of_nonneg_right cc (sq_nonneg _)
    _ ≤ 4 := by linarith only [temp]

theorem power {g : ℝ} (gp:0<g) (small:g≤1) (d q:ℕ) {k E σ:ℝ} (k0:0≤k) (e0:0≤E)
    (col:k*g^2≤4) (length:8*((q+d+2:ℕ):ℝ)*(-Real.log g)≤σ) :
    8*(1+k)*(2*(E/g^d)+1)*Real.exp (-σ/8) ≤ 40*(2*E+1)*g^q := by
  have distance : Real.exp (-σ/8) ≤ g^(q+d+2) := by
    calc
      _ ≤ Real.exp (((q+d+2:ℕ):ℝ)*Real.log g) := by apply Real.exp_le_exp.mpr;linarith
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log gp]
  have margin : (1+k)*g^2≤5 := by
    have z : g^2≤1 := pow_le_one₀ gp.le small
    linarith only [col,z]
  have restore : (2*(E/g^d)+1)*g^d ≤ 2*E+1 := by
    rw [add_mul,one_mul,mul_assoc,div_mul_cancel₀ _ (pow_pos gp d).ne']
    linarith only [show g^d ≤ 1 from pow_le_one₀ gp.le small]
  have prod:=mul_le_mul margin restore (mul_nonneg (by positivity) (pow_nonneg gp.le _))
    (by norm_num : (0:ℝ)≤5)
  calc
    _ ≤ 8*(1+k)*(2*(E/g^d)+1)*g^(q+d+2) := mul_le_mul_of_nonneg_left distance (by positivity)
    _ = (8*g^q)*((1+k)*g^2*((2*(E/g^d)+1)*g^d)) := by rw [pow_add,pow_add];ring
    _ ≤ (8*g^q)*(5*(2*E+1)) := mul_le_mul_of_nonneg_left prod (by positivity)
    _ = _ := by ring

end YM.Integration.WilsonThermometerUnitFilingSchedule
