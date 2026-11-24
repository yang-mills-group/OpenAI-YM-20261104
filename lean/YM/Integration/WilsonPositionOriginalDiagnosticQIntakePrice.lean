import YM.Integration.WilsonPositionOriginalDiagnosticQIntake
import YM.Integration.ActualRunKernelPackets
import YM.RG05Readout.Aligned.Geometry

/-! On every true pair of meshes in the auxiliary comparison window the
physical spatial gain absorbs all fixed arities of the original moving-Q
marker tariff. This result uses the physical schedules themselves. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticQIntakePrice
open Filter Finset Lattice Wilson RG PhysicalNext.Repeat Legato
open scoped Classical Topology BigOperators

variable {G : Gauge} (R : Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels

theorem birth (m j : ℕ) :
    β j = β m+G.slopeConstant*(R.family.S.scale j-R.family.S.scale m) := by
  change R.family.path.levels.clock.bar + G.slopeConstant * R.family.S.scale j =
    (R.family.path.levels.clock.bar + G.slopeConstant * R.family.S.scale m) + _
  ring

private theorem log_cost (w : ℕ) (K s : ℝ) (hK : 0≤K) (hs : 0<s) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-x*s) * (K*(1+x)^w) ≤ 1 := by
  let A := K*(2/s)^w
  have grow : Tendsto (fun x : ℝ => s*x) atTop atTop := tendsto_id.const_mul_atTop hs
  have low := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero w).comp grow
  have small : ∀ᶠ x : ℝ in atTop, A*((s*x)^w * Real.exp (-(s*x))) ≤ 1 :=
    ((tendsto_const_nhds (x:=A)).mul low).eventually_le_const (by norm_num)
  filter_upwards [eventually_ge_atTop 1,small] with x hx priced
  have eq : 2/s*(s*x) = 2*x := by field_simp
  calc
    _ ≤ Real.exp (-x*s) * (K*(2/s*(s*x))^w) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by rw [eq]; linarith) w) hK) (Real.exp_pos _).le
    _ = A*((s*x)^w * Real.exp (-(s*x))) := by
      rw [show -x*s = -(s*x) by ring,mul_pow]; dsimp [A]; ring
    _ ≤ 1 := priced

/-- The birth and the physical reporter may be chosen after the
pre-regulator threshold. The original marker tariff is restored to its
actual fixed load. The forced allowance in the physical purchase is kept
in its own currency. -/
theorem restored (simple : G.Simple) (C : ℝ) (hC : 0 ≤ C) (b load n q : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ m : ℕ in atTop, ∀ j : ℕ, (Λ m)^((3:ℝ)/2) ≤ R.family.S.scale j-R.family.S.scale m →
      ∀ N per, m≤N →
        (R.family.S.a j/R.family.S.a m)^γ * (2*β m)^n * (C*(β j)^(b+1))^load ≤
          (Pert.Asymptotics.regulatorRun R.family N per m)^q := by
  let w := (b+1)*load
  let s := γ/2
  have hs : 0<s := half_pos hγ
  let K := C^load * (1+|G.slopeConstant|)^w
  have hK : 0≤K := by dsimp [K]; positivity
  obtain ⟨r,after⟩ := eventually_atTop.mp (log_cost w K s hK hs)
  let A := n+w+q
  have infinity := RG05Readout.lambda_growth simple R.family.path.levels
  have big := (tendsto_rpow_atTop (by norm_num:0<(3:ℝ)/2)).comp infinity
  have root := (tendsto_rpow_atTop (by norm_num:0<(1:ℝ)/2)).comp infinity
  filter_upwards [big.eventually_ge_atTop r,root.eventually_ge_atTop ((A:ℝ)/s)]
    with m above tall
  intro j window N per live
  let x := R.family.S.scale j-R.family.S.scale m
  let a := |G.slopeConstant|
  let g := Pert.Asymptotics.regulatorRun R.family N per m
  have good : 1 ≤ β m := (R.family.path.levels.fits.delayed _).le
  have hp : 0<β m := zero_lt_one.trans_le good
  have hLam : 0<Λ m := by
    change 0<2+Real.log (β m)
    linarith only [Real.log_nonneg good]
  have hx : 0≤x := (Real.rpow_nonneg hLam.le _).trans window
  have hxpaid := after x (above.trans window)
  have ha : 0≤a := abs_nonneg _
  have native : β j ≤ (1+a)*(2*β m)*(1+x) := by
    rw [birth R m j]
    change β m+G.slopeConstant*x ≤ _
    calc
      _ ≤ β m + a*x := add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self _) hx) _
      _ ≤ β m + β m*(a*x) := add_le_add_right (le_mul_of_one_le_left (mul_nonneg ha hx) good) _
      _ ≤ _ := by nlinarith [mul_nonneg hp.le ha,mul_nonneg hp.le hx,mul_nonneg hp.le (mul_nonneg ha hx)]
  have hj : 0≤β j := zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have inv : (C*(β j)^(b+1))^load ≤ K*(1+x)^w*(2*β m)^w := by
    calc
      _ = C^load*(β j)^w := by simp [w,mul_pow,pow_mul]
      _ ≤ C^load*((1+a)*(2*β m)*(1+x))^w := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hj native w) (pow_nonneg hC _)
      _ = _ := by simp only [K,a,mul_pow]; ring
  have base : Real.log (2*β m) ≤ Λ m := by
    rw [Real.log_mul (by norm_num) hp.ne']
    change Real.log 2+Real.log (β m) ≤ 2+Real.log (β m)
    linarith only [Real.log_le_sub_one_of_pos (two_pos:0<(2:ℝ))]
  have bill : (A:ℝ)*Real.log (2*β m) ≤ x*s := by
    calc
      _ ≤ (A:ℝ)*(Λ m) := mul_le_mul_of_nonneg_left base A.cast_nonneg
      _ ≤ ((Λ m)^((1:ℝ)/2)*s)*(Λ m) := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs).1 tall) hLam.le
      _ = (Λ m)^((3:ℝ)/2)*s := by
        rw [show (3:ℝ)/2=(1:ℝ)/2+1 by norm_num,Real.rpow_add hLam,Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right window hs.le
  have coarse : Real.exp (-x*s)*(2*β m)^A ≤ 1 := by
    rw [show (2*β m)^A=Real.exp ((A:ℝ)*Real.log (2*β m)) by
      rw [← Real.log_pow, Real.exp_log (pow_pos (mul_pos zero_lt_two hp) _)],
      ←Real.exp_add,Real.exp_le_one_iff]
    linarith only [bill]
  have space : (R.family.S.a j / R.family.S.a m)^γ = Real.exp (-x*s)*Real.exp (-x*s) := by
    rw [Real.rpow_def_of_pos (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)),
      Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne',←Real.exp_add]
    congr 1
    simp only [x,Schedule.scale,Real.log_inv,s]; ring
  have gpos := ActualRunKernelPackets.regulator_pos R N per m live
  have sq := Real.sqrt_pos.mpr hp
  have sqle : Real.sqrt (β m)≤β m := (le_mul_of_one_le_right sq.le (Real.one_le_sqrt.mpr good)).trans_eq (Real.mul_self_sqrt hp.le)
  have measured : (Real.sqrt (β m))⁻¹≤2*g := (RG04B.ratioHat R.makes (p:=per) live).1
  have reserve : 1≤g*(2*β m) := by
    calc
      1=(Real.sqrt (β m))⁻¹*Real.sqrt (β m):=(inv_mul_cancel₀ sq.ne').symm
      _≤(2*g)*β m:=mul_le_mul measured sqle sq.le (mul_nonneg zero_le_two gpos.le)
      _=_:=by ring
  apply le_of_mul_le_mul_right ?_ (pow_pos (mul_pos zero_lt_two hp) q)
  rw [← mul_pow]
  calc
    _ ≤ (Real.exp (-x*s)*Real.exp (-x*s))*(2*β m)^n*(K*(1+x)^w*(2*β m)^w)*(2*β m)^q := by
      rw [space]; gcongr
    _ = (Real.exp (-x*s)*(2*β m)^A)*(Real.exp (-x*s)*(K*(1+x)^w)) := by
      simp only [A,pow_add]; ring
    _ ≤ 1 := mul_le_one₀ coarse (mul_nonneg (Real.exp_pos _).le (mul_nonneg hK (pow_nonneg (by linarith) _))) hxpaid
    _ ≤ _ := one_le_pow₀ reserve

end YM.Integration.WilsonPositionOriginalDiagnosticQIntakePrice
