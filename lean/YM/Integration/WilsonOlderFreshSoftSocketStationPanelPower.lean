import YM.Integration.WilsonOlderFreshSoftSocketStationPanelStops
import YM.Integration.WilsonOlderFreshSoftSocketStationCalendar

/-! One before-period width pays all signed ordinary faces of the actual measured panel together. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPanelPower
open Function Filter Finset Lattice RG Wilson PhysicalNext PhysicalNext.Repeat.Legato ActualRunPhysicalPages
open WilsonOlderFreshSoftRoseCourse (grade)
open WilsonOriginalPublicFigureIncome (height)
open WilsonOlderFreshSoftSocketStationCalendar (Offered)
open Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
def rank (pow:ℕ):ℕ:=pow+univ.sup (fun i:Fin 3=>height R (grade i))
def debt (pow:ℕ):ℕ:=3*rank R pow
def loss (pow q:ℕ):ℝ:=4*((q+2*debt R pow+1:ℕ):ℝ)

theorem roster (pow K:ℕ)(s:Finset (Fin 3))(B:ℝ)(b0:0≤B):
    (∏i:s,B*(H K)^(pow+height R (grade i)))≤(max 1 B)^3*(H K)^debt R pow:=by
  have high:1≤H K:=(R.family.path.levels.fits.delayed K).le
  have hr:1≤(H K)^rank R pow:=one_le_pow₀ high
  have wr:1 ≤ max 1 B:=le_max_left ..
  have card:(Fintype.card s)≤3:=by simpa only [Fintype.card_coe,Fintype.card_fin] using s.card_le_univ
  calc
    _≤∏_i:s,max 1 B*(H K)^rank R pow:=by
      apply prod_le_prod (fun _ _=>mul_nonneg b0 (pow_nonneg (zero_le_one.trans high) _))
      intro i _
      apply mul_le_mul (le_max_right ..) _ (pow_nonneg (zero_le_one.trans high) _) (zero_le_one.trans wr)
      exact pow_le_pow_right₀ high (Nat.add_le_add_left (le_sup (f:=fun x:Fin 3=>height R (grade x)) (mem_univ (i:Fin 3))) pow)
    _=(max 1 B*(H K)^rank R pow)^Fintype.card s:=by simp
    _≤(max 1 B*(H K)^rank R pow)^3:=pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le wr hr) card
    _=_:=by rw [mul_pow,debt,Nat.mul_comm 3,pow_mul]

theorem absorbed {g h φ:ℝ}(gp:0<g)(hp:0≤h)(pp:0≤φ)(bank:h*g^2≤2)(d q:ℕ)
    (gap:φ≤Real.exp (-(4*((q+2*d+1:ℕ):ℝ))*Real.log g⁻¹)):
    h^d*(g⁻¹*φ^((4:ℝ)⁻¹))≤(2:ℝ)^d*g^q:=by
  let k:=q+2*d+1
  have returned:φ^((4:ℝ)⁻¹)≤g^k:=by
    calc
      _≤(Real.exp (-(4*(k:ℝ))*Real.log g⁻¹))^((4:ℝ)⁻¹):=Real.rpow_le_rpow pp gap (by norm_num)
      _=Real.exp ((k:ℝ)*Real.log g):=by rw [←Real.exp_mul,Real.log_inv];congr 1;ring
      _=_:=by rw [Real.exp_nat_mul,Real.exp_log gp]
  calc
    _≤h^d*(g⁻¹*g^k):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left returned (inv_nonneg.mpr gp.le)) (pow_nonneg hp _)
    _=(h*g^2)^d*g^q:=by
      dsimp only [k];rw [pow_succ,pow_add,pow_mul,mul_pow];field_simp
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hp (sq_nonneg _)) bank _) (pow_nonneg gp.le _)

theorem opened (width pow q:ℕ){c w:ℕ}(window:Offered R width (loss R pow q) c w)
    {N per K:ℕ}(ck:c≤K)(cut:K≤N)(locality:R.family.S.a c/R.family.S.a K≤(H c)^width)
    (s:Finset (Fin 3))(B:ℝ)(b0:0≤B):
    (∏i:s,B*(H K)^(pow+height R (grade i)))*
      (Real.sqrt (R.family.path.β N per K)*(R.family.S.a c/R.family.S.a w)^((4:ℝ)⁻¹))≤
    ((max 1 B)^3*2^debt R pow)*(regulatorRun R.family N per K)^q:=by
  let g:=regulatorRun R.family N per K
  let β:=R.family.path.β N per K
  let φ:=R.family.S.a c/R.family.S.a w
  have h0:0<H K:=zero_lt_one.trans (R.family.path.levels.fits.delayed K)
  have band:H K/2≤β:=(R.makes.wilson.represents N per K cut).band.1
  have bpos:0<β:=(half_pos h0).trans_le band
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per K cut
  have bp:H K*g^2≤2:=by
    change (H K)*((Real.sqrt β)⁻¹)^2≤2
    rw [inv_pow,Real.sq_sqrt bpos.le,←div_eq_mul_inv,div_le_iff₀ bpos]
    linarith only [band]
  have room:=((window K N per ck cut locality).1)
  have clip:=absorbed gp h0.le (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) bp (debt R pow) q room
  have same:Real.sqrt β=g⁻¹:=by change _=(((Real.sqrt β)⁻¹)⁻¹);rw [inv_inv]
  change _*(Real.sqrt β*φ^((4:ℝ)⁻¹))≤_*g^q
  rw [same]
  calc
    _≤((max 1 B)^3*(H K)^debt R pow)*(g⁻¹*φ^((4:ℝ)⁻¹)):=
      mul_le_mul_of_nonneg_right (roster R pow K s B b0) (mul_nonneg (inv_nonneg.mpr gp.le)
        (Real.rpow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _))
    _≤_:=by
      rw [mul_assoc,mul_assoc]
      exact mul_le_mul_of_nonneg_left clip (pow_nonneg (zero_le_one.trans (le_max_left ..)) _)

end YM.Integration.WilsonOlderFreshSoftSocketStationPanelPower
end
