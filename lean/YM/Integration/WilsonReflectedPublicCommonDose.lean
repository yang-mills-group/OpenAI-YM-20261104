import YM.Integration.WilsonReflectedPublicGuardedColumns

/-! A single positive dose funds the original palette and the independently
fitted signed residual before either group is conditioned. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonDose
open Function Lattice RG Wilson Source Labels Extra.Histories Motion RG05Readout RG05Readout.Address
open PhysicalNext.Repeat.Legato WilsonReflectedFundedHearing Extra.Histories.Relay
open WilsonReflectedPublicGuardedColumns WilsonReflectedPublicSignedFare
open scoped Classical BigOperators

def denominator (χ C V:ℝ) := max (max 1 χ) (C*V)
def dose (χ C V:ℝ):ℝ := (denominator χ C V)⁻¹

theorem positive (χ C V:ℝ):0<dose χ C V:=
  inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_left 1 χ).trans (le_max_left ..)))

theorem smaller (χ C V:ℝ)(hp:1≤χ):
    dose χ C V ≤ 1 ∧ 0≤dose χ C V*χ ∧ dose χ C V*χ≤1 ∧ dose χ C V*(C*V)≤1:=by
  let m:=denominator χ C V
  have grow:1 ≤ m:=(le_max_left 1 χ).trans (le_max_left ..)
  have mp:0 < m :=lt_of_lt_of_le (by norm_num: (0:ℝ)<1) grow
  have fit (s:ℝ)(hs:s ≤ m):m⁻¹*s≤1:=by
    rw [inv_mul_eq_div]
    exact (div_le_one mp).mpr hs
  exact ⟨inv_le_one_of_one_le₀ grow,mul_nonneg (positive ..).le (zero_le_one.trans hp),
    fit χ ((le_max_right 1 χ).trans (le_max_left ..)),fit (C*V) (le_max_right ..)⟩

theorem composed (χ C V:ℝ)(hp:1≤χ):((dose χ C V*χ:ℝ):ℂ)*(χ:ℂ)⁻¹=(dose χ C V:ℂ):=by
  have h:(χ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le (by norm_num:(0:ℝ)<1) hp).ne'
  push_cast
  field_simp

theorem refund (χ C V:ℝ): (dose χ C V)⁻¹=denominator χ C V:=inv_inv _

theorem residual (χ C V a:ℝ)(hp:1≤χ)(cost:0≤a):
    ‖((dose χ C V:ℝ):ℂ)‖*(a*C*V)≤a:=by
  rw [Complex.norm_real,Real.norm_of_nonneg (positive ..).le]
  calc
    _=a*(dose χ C V*(C*V)):=by ring
    _≤_:=mul_le_of_le_one_right cost (smaller χ C V hp).2.2.2

variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family
local notation "F_" => R.family.labels.level d
local notation "P_" => R.family.path.rep N p f

private theorem again {n:Side}{D:ℕ}{F:Frame G D}(a b:ℂ)(q:Coefficient F n):
    stretch a (stretch b q)=stretch (a*b) q:=by
  cases q
  simp only [stretch,smul_smul]

theorem scaled (A:Arm R d N p f K)(hf:f≤K)(top:K≤N)(χ C V:ℝ)(hp:1≤χ)(a:ℝ)(ap:0≤a)
    (q:Coefficient (F_) ((C₀).side f p))(unit:Restored R A hf top 1 (a*C*V) q):
    Restored R A hf top (dose χ C V:ℂ) a (stretch (dose χ C V:ℂ) q):=by
  let c:ℂ:=dose χ C V
  have fare:=residual χ C V a hp ap
  refine ⟨stretch_format c unit.form,rem_mono (stretch_rem c unit.paid) fare,?_,?_,?_⟩
  · change (F_).coeffSize (c • q.x)≤a
    rw [Size.smul]
    exact (mul_le_mul_of_nonneg_left unit.primary (norm_nonneg c)).trans fare
  · obtain ⟨π,present⟩:=unit.origin
    refine ⟨π,?_⟩
    rw [present,again]
    congr 1
    ring
  · intro U
    rw [stretch_density,unit.field]
    ring

end YM.Integration.WilsonReflectedPublicCommonDose
end
