import YM.Integration.WilsonAddressedMixedOpticalMesh
import YM.Integration.WilsonIndependentMatchedReportedRarityMeasured
/-! The designated stable slots spend their actual incoming finite source salary once.
The real width of the position test and the public coupling are measured on this run. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedOpticalFuel
open Function Finset Filter Lattice RG Wilson Source PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonInvariantActionPosition
open scoped BigOperators Classical
variable {G:Gauge}

theorem depth (R:Run G)(m f K t J:ℕ)(older:m ≤ f)(birth:K=berth R t f)
    (room:2*J ≤ t)(g:ℝ)(live:0<g)
    (clock:g⁻¹ ≤ (R.family.path.levels.clock.hatBeta f)^2):
    paceT R.family.S m K ≤ g^J:=by
  let β:=R.family.path.levels.clock.hatBeta f
  have β₁:1 ≤ β:=(R.family.path.levels.fits.delayed f).le
  have h₁:(g⁻¹)^J ≤ β^t:=by
    exact (pow_le_pow_left₀ (inv_pos.mpr live).le clock J).trans
      ((show (β^2)^J=β^(2*J) from (pow_mul ..).symm).le.trans (pow_le_pow_right₀ β₁ room))
  have h₂:=WilsonInvariantActionPosition.arrival R t f
  rw [←birth] at h₂
  have step:=h₂.2.trans (R.family.S.strictAnti.antitone older)
  have small:=((mul_le_mul_of_nonneg_left h₁ (R.family.S.a_pos K).le).trans step)
  unfold paceT
  rw [inv_pow,←div_eq_mul_inv,div_le_iff₀ (pow_pos live J)] at small
  exact (div_le_iff₀ (R.family.S.a_pos m)).mpr (small.trans_eq (mul_comm ..))

theorem rebate (δ g x η M:ℝ)(p b P:ℕ)(positive:0<δ)(narrow:δ≤1)(live:0<g)
    (paid:δ ≤ g^(8*(P+p+2*b)))(real₀:0≤x)(margin:0≤η)(reserve:η≤1/8)
    (ticket:1≤M^b*(g⁻¹)^(2*b))(borne:x≤M^b*(g⁻¹)^(2*b)):
    δ^((1:ℝ)/4)*((g⁻¹)^p*(x/δ)^η) ≤ M^b*g^P:=by
  let J:=P+p+2*b
  have change:δ^((1:ℝ)/4)*((g⁻¹)^p*(x/δ)^η)=
      δ^((1:ℝ)/4-η)*((g⁻¹)^p*x^η):=by
    rw [Real.div_rpow real₀ positive.le,Real.rpow_sub positive]
    ring
  have power:(g^(8*J))^((1:ℝ)/8)=g^J:=by
    rw [show 8*J=J*8 by omega,pow_mul,←Real.rpow_natCast (g^J) 8,
      ←Real.rpow_mul (pow_nonneg live.le J)]
    norm_num
  have gain:δ^((1:ℝ)/4-η) ≤ g^J:=by
    refine (Real.rpow_le_rpow_of_exponent_ge positive narrow (show (1:ℝ)/8≤1/4-η by linarith)).trans ?_
    exact (Real.rpow_le_rpow positive.le paid (by norm_num:(0:ℝ)≤1/8)).trans_eq power
  have hom:x^η ≤ M^b*(g⁻¹)^(2*b):=
    (Real.rpow_le_rpow real₀ borne margin).trans
      ((Real.rpow_le_rpow_of_exponent_le ticket (show η≤1 by linarith)).trans_eq (Real.rpow_one _))
  rw [change]
  refine (mul_le_mul gain (mul_le_mul_of_nonneg_left hom (pow_nonneg (inv_pos.mpr live).le _))
    (mul_nonneg (pow_nonneg (inv_pos.mpr live).le _) (Real.rpow_nonneg real₀ _))
    (pow_nonneg live.le J)).trans_eq ?_
  dsimp only [J]
  rw [pow_add,pow_add]
  simp only [inv_pow]
  field_simp [live.ne']

theorem original (R:Run G)(simple:G.Simple)(m f K t b p P:ℕ)(older:m≤f)(birth:K=berth R t f)
    (room:2*(8*(P+p+2*b)) ≤ t)(g r η M:ℝ)(live:0<g)(radius:0<r)(margin:0≤η)(reserve:η≤1/8)
    (clock:g⁻¹ ≤ (R.family.path.levels.clock.hatBeta f)^2)
    (reach:r≤(R.family.path.levels.clock.hatBeta f)^b*R.family.S.a f)
    (gross:R.family.path.levels.clock.hatBeta K*g^2≤M):
    (paceT R.family.S m K)^((1:ℝ)/4)*((g⁻¹)^p*(r/R.family.S.a K)^η) ≤ M^b*g^P:=by
  let a:=R.family.S.a
  let β:=R.family.path.levels.clock.hatBeta
  let δ:=paceT R.family.S m K
  have early:f≤K:=birth ▸ (WilsonInvariantActionPosition.arrival R t f).1.le
  have dp:0<δ:=div_pos (R.family.S.a_pos K) (R.family.S.a_pos m)
  have d₁:δ≤1:=(div_le_one (R.family.S.a_pos m)).mpr (R.family.S.strictAnti.antitone (older.trans early))
  have one:1≤β f:=(R.family.path.levels.fits.delayed f).le
  have bf:β f≤β K:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le early
  have paid:β f≤M*(g⁻¹)^2:=by
    rw [inv_pow,←div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos live 2)).mpr ((mul_le_mul_of_nonneg_right bf (sq_nonneg _)).trans gross)
  have bill:(β f)^b ≤ M^b*(g⁻¹)^(2*b):=by
    simpa only [mul_pow,pow_mul] using pow_le_pow_left₀ (zero_le_one.trans one) paid b
  have size:r/a m ≤ (β f)^b:=
    (div_le_iff₀ (R.family.S.a_pos m)).mpr (reach.trans
      (mul_le_mul_of_nonneg_left (R.family.S.strictAnti.antitone older) (pow_nonneg (zero_le_one.trans one) _)))
  have identify:r/a K=(r/a m)/δ:=by
    dsimp only [δ,paceT,a]
    field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos K).ne']
  change δ^((1:ℝ)/4)*((g⁻¹)^p*(r/a K)^η) ≤ _
  rw [identify]
  exact rebate δ g (r/a m) η M p b P dp d₁ live (depth R m f K t _ older birth room g live clock)
    (div_nonneg radius.le (R.family.S.a_pos m).le) margin reserve ((one_le_pow₀ one).trans bill) (size.trans bill)

end YM.Integration.WilsonIndependentMatchedReportedOpticalFuel
