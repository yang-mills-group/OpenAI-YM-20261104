import YM.Integration.WilsonIndependentConditionedBankBerth
import YM.Integration.WilsonIndependentConditionedGramRawHome

/-! The original physical regulator, restored from its own reporting date to
the chosen common spatial station, including the real measured source vector. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSpatialAperture
open Function Finset Lattice RG Wilson Source Labels Extra.Histories Motion PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonIndependentConditionedBankRawUnits (home)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonAddressedTrialPivotUnits (row)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped Classical
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

theorem factor (m f K:ℕ):a K/a m=(a K/a f)*(a f/a m):=by
  field_simp [(R.family.S.a_pos f).ne',(R.family.S.a_pos m).ne']

theorem window {m f K t U:ℕ}{r:ℝ}(host:m ≤ f)(fit:a m ≤ r)(reach:r ≤ (β f)^U*a f)
    (win:(thermal R f)^(2*(t+1)) ≤ a K/a f)(ceiling:a K/a f ≤ (thermal R f)^(2*t)):
    (thermal R f)^(2*U) ≤ a f/a m ∧ a f/a m ≤ 1 ∧
    (thermal R f)^(2*(t+1)+2*U) ≤ a K/a m ∧ a K/a m ≤ (thermal R f)^(2*t):=by
  have bp:0<β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have denom:0<a m/a f:=div_pos (R.family.S.a_pos m) (R.family.S.a_pos f)
  have reverse:a m/a f ≤ (β f)^U:=(div_le_iff₀ (R.family.S.a_pos f)).2 (fit.trans reach)
  have sq:(thermal R f)^2=(β f)⁻¹:=by
    change ((Real.sqrt (β f))⁻¹)^2=(β f)⁻¹
    rw [inv_pow,Real.sq_sqrt bp.le]
  have inset:(thermal R f)^(2*U) ≤ a f/a m:=by
    rw [pow_mul,sq,inv_pow,←inv_div (a m) (a f)]
    exact (inv_le_inv₀ (pow_pos bp _) denom).2 reverse
  have thin:a f/a m ≤ 1:=(div_le_one (R.family.S.a_pos m)).2 (R.family.S.strictAnti.antitone host)
  refine ⟨inset,thin,?_,?_⟩
  · rw [factor R m f K,pow_add]
    exact mul_le_mul win inset (pow_nonneg (inv_pos.mpr (Real.sqrt_pos.mpr bp)).le _) (div_pos (R.family.S.a_pos K) (R.family.S.a_pos f)).le
  · rw [factor R m f K]
    exact (mul_le_of_le_one_right (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)).le thin).trans ceiling

theorem engineering {m f K d:ℕ}{η c H:ℝ}(earned:(a K/a f)^d*c ≤ H*(a K/a f)^(-η)):
    (a K/a m)^d*c ≤ (a f/a m)^((d:ℝ)+η)*H*(a K/a m)^(-η):=by
  let u:=a f/a m
  let v:=a K/a f
  have up:0<u:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have vp:0<v:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have meet:a K/a m=v*u:=factor R m f K
  have paid:=mul_le_mul_of_nonneg_left earned (pow_nonneg up.le d)
  change u^d*(v^d*c) ≤ u^d*(H*v^(-η)) at paid
  rw [meet,mul_pow,Real.mul_rpow vp.le up.le]
  change _ ≤ u^((d:ℝ)+η)*H*(v^(-η)*u^(-η))
  have unit:u^η*u^(-η)=1:=by rw [←Real.rpow_add up,add_neg_cancel,Real.rpow_zero]
  rw [Real.rpow_add up,Real.rpow_natCast]
  calc
    _ = u^d*(v^d*c):=by ring
    _ ≤ u^d*(H*v^(-η)):=paid
    _ = (u^d*u^η)*H*(v^(-η)*u^(-η)):=by
      calc _ = u^d*(H*v^(-η))*(u^η*u^(-η)):=by rw [unit,mul_one]
           _ = _:=by ring

theorem placed {E:Type*}[SeminormedAddCommGroup E][NormedSpace ℝ E] {r s:ℝ}(pos:0<r)(m:ℕ)
    (x y:E)(f:ℕ)(d:ℕ):
    ‖(r/a m) • x-(r/a m) • y‖=(r/a m)*‖x-y‖ ∧
    s/a m=(s/r)*(r/a m) ∧ (r/a m)^d*(a m/a f)^d=(r/a f)^d:=by
  refine ⟨?_,?_,?_⟩
  · rw [←smul_sub,norm_smul,Real.norm_of_nonneg (div_pos pos (R.family.S.a_pos m)).le]
  · field_simp [pos.ne',(R.family.S.a_pos m).ne']
  · rw [←mul_pow]
    congr 1
    field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos f).ne']

variable {d j f K N p target:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
  (A:(R.family.label d)≃ₗ[ℂ](R.family.label d))(Y:R.family.label d){salary:ℝ}
  (cash:Cash (R:=R) d j f K N p target before up live η A Y salary)
  (arm:Arm R d N p f K)(same:arm.w=A.symm (fitted R d j N p Y))

include cash same in
theorem received (m:ℕ)(c:ℂ):
    (a K/a m)^d*(R.family.labels.level d).coeffSize (row R d K N p c (coords R arm)) ≤
    (a f/a m)^((d:ℝ)+η)*home R d j f η c salary*(a K/a m)^(-η):=
  engineering R (WilsonIndependentConditionedBankRawUnits.original R before up live A Y cash arm same c)

end YM.Integration.WilsonIndependentConditionedGramSpatialAperture
