import YM.Integration.WilsonReceivedFirstCalibratedTop
import YM.Integration.WilsonRootedObservedRate

/-! The scalar error at the first two dated Q insertions, on their measured Wilson course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFirstCalibratedRate
open Filter Real Wilson RG Lattice PhysicalNext.Repeat.Legato ConnectedActivityE6
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor Pressure IterationFour
open scoped Topology

private theorem chart {x y β β' bill κ:ℝ} {grade prec p:ℕ}
    (x₁:1≤x) (rise:x≤y) (lower:x/2≤β ∧ β≤2*x) (upper:y/2≤β')
    (booked:bill≤y) (kpos:0<κ)
    (head:prec≤2*grade) (depth:p+3≤prec) (small:2*Coat.gStep β≤1) :
    8*x*(8*bill*y^(-((grade+1:ℕ):ℝ))+κ*(Coat.gStep β')^prec)+κ*(Coat.gStep β)^prec ≤
      (8*(64+9*κ))*(2*Coat.gStep β)^(p+1) := by
  let t:=2*Coat.gStep β
  have x₀:0<x:=lt_of_lt_of_le zero_lt_one x₁
  have y₀:0<y:=x₀.trans_le rise
  have β₀:0<β:=(half_pos x₀).trans_le lower.1
  have β'₀:0<β':=(half_pos y₀).trans_le upper
  have rt:=Real.sqrt_pos.mpr β₀
  have rt':=Real.sqrt_pos.mpr β'₀
  have t₀:0<t:=mul_pos (by norm_num) (inv_pos.mpr rt)
  have sq:t^2=4/β:=by
    change (2*(Real.sqrt β)⁻¹)^2=4/β
    rw [mul_pow,inv_pow,Real.sq_sqrt β₀.le]
    ring
  have invy:y⁻¹≤t^2:=by
    rw [sq,inv_eq_one_div]
    apply (div_le_div_iff₀ y₀ β₀).2
    linarith [lower.2]
  have pair:Coat.gStep β'≤t:=by
    change (Real.sqrt β')⁻¹≤2*(Real.sqrt β)⁻¹
    rw [inv_eq_one_div,←div_eq_mul_inv]
    apply (div_le_div_iff₀ rt' rt).2
    nlinarith [Real.sq_sqrt β₀.le,Real.sq_sqrt β'₀.le,lower.2]
  have fitted:bill*y^(-((grade+1:ℕ):ℝ))≤t^prec:= by
    calc
      _ ≤ y*(y^(grade+1))⁻¹ := by
        rw [Real.rpow_neg y₀.le,Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_right booked (inv_nonneg.mpr (pow_nonneg y₀.le _))
      _ = (y⁻¹)^grade := by rw [pow_succ,mul_inv_rev,←mul_assoc,mul_inv_cancel₀ y₀.ne',one_mul,inv_pow]
      _ ≤ (t^2)^grade := pow_le_pow_left₀ (inv_nonneg.mpr y₀.le) invy _
      _ = t^(2*grade) := (pow_mul _ _ _).symm
      _ ≤ t^prec := pow_le_pow_of_le_one t₀.le small head
  have charge:x*t^2≤8:=by
    rw [sq,←mul_div_assoc,div_le_iff₀ β₀]
    linarith [lower.1]
  have spill:x*t^prec≤8*t^(p+1):=by
    calc
      _ ≤ x*t^(2+(p+1)):= mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one
        t₀.le small (by omega)) x₀.le
      _ = (x*t^2)*t^(p+1):=by rw [pow_add]; ring
      _ ≤ _:= mul_le_mul_of_nonneg_right charge (pow_nonneg t₀.le _)
  have fine:=pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg β')) pair prec
  have current:Coat.gStep β≤t:=by
    change (Real.sqrt β)⁻¹≤2*(Real.sqrt β)⁻¹
    linarith [inv_pos.mpr rt]
  have paid:(Coat.gStep β)^prec≤x*t^prec :=
    (pow_le_pow_left₀ (inv_nonneg.mpr rt.le) current prec).trans
      (le_mul_of_one_le_left (pow_nonneg t₀.le _) x₁)
  have parcel:8*bill*y^(-((grade+1:ℕ):ℝ))+κ*(Coat.gStep β')^prec ≤ 8*t^prec+κ*t^prec := by
    simpa only [Coat.gStep,mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left fitted (by norm_num:0≤(8:ℝ)))
      (mul_le_mul_of_nonneg_left fine kpos.le)
  calc
    _ ≤ 8*x*(8*t^prec+κ*t^prec)+κ*(x*t^prec) := add_le_add
      (mul_le_mul_of_nonneg_left parcel (by positivity)) (mul_le_mul_of_nonneg_left paid kpos.le)
    _ = (64+9*κ)*(x*t^prec):=by ring
    _ ≤ (64+9*κ)*(8*t^(p+1)):=mul_le_mul_of_nonneg_left spill (by positivity)
    _ = _:= by ring

private theorem wallet {G:Gauge} (R:Run G) (j slots:ℕ)
    (enrolled:slots≤R.alloy.B.a.clock.J j) :
    (budgetR R j)^slots≤R.alloy.B.a.clock.hatBeta (j+1) := by
  let x:=R.alloy.B.a.clock.hatBeta (j+1)
  let h:=R.alloy.B.a.clock.J j
  have x₁:1≤x:=(R.alloy.B.a.fits.delayed _).le
  have x₀:0≤x:=zero_le_one.trans x₁
  have b₀:0≤budgetR R j:=le_min (Real.exp_pos _).le (Real.rpow_nonneg x₀ _)
  have sale:budgetR R j≤x^(Beaming.grain h):=min_le_right _ _
  have hg:Beaming.grain h*(slots:ℝ)≤1:=by
    unfold Beaming.grain
    rw [show (1:ℝ)/((h:ℝ)+1)*slots=(slots:ℝ)/((h:ℝ)+1) by ring]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast Nat.le_succ_of_le enrolled)
  calc
    _ ≤ (x^(Beaming.grain h))^slots:=pow_le_pow_left₀ b₀ sale _
    _ = (x^(Beaming.grain h))^(slots:ℝ):=(Real.rpow_natCast _ _).symm
    _ = x^(Beaming.grain h*slots):=(Real.rpow_mul x₀ _ _).symm
    _ ≤ x^(1:ℝ):=Real.rpow_le_rpow_of_exponent_le x₁ hg
    _ = _ := Real.rpow_one _

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (order prec p slots:ℕ) (depth:p+3≤prec)
    (accuracy:2*(prec+1)+8≤order) {κ ε:ℝ} (kpos:0<κ) (epos:0<ε) :
    ∀ᶠ j:ℕ in atTop, ∀ (N per:ℕ), j+1<N → ∀ (bill:ℝ), 0≤bill →
      bill≤(R.alloy.B.a.clock.hatBeta ((j+1)+1))^(Beaming.grain (R.alloy.B.a.clock.J (j+1))) →
      let g:=Coat.gStep (R.family.path.rep N per (j+1)).beta
      let g':=Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
      8*(budgetR R j)^slots*(8*bill*(R.alloy.B.a.clock.hatBeta ((j+1)+1))^(-(order:ℝ))+κ*g'^prec)
        +κ*g^prec≤ε*g^p := by
  let C:=8*(64+9*κ)
  have cp:0<C:=by dsimp [C]; positivity
  have cheap:=WilsonRootedObservedRate.power R simple p p le_rfl (div_pos epos cp)
  have cool:=WilsonRootedObservedRate.power R simple 0 0 le_rfl (show 0<(1:ℝ) by norm_num)
  filter_upwards [cheap,cool,R.alloy.B.a.fits.deep.eventually_ge_atTop slots] with j priced chilled active
  intro N per cut bill bd limited g g'
  let x:=R.alloy.B.a.clock.hatBeta (j+1)
  let y:=R.alloy.B.a.clock.hatBeta ((j+1)+1)
  have x₁:1≤x:=(R.alloy.B.a.fits.delayed _).le
  have y₁:1≤y:=(R.alloy.B.a.fits.delayed _).le
  have rise:x≤y:=WilsonStartup.Timing.hat_mono R.family.path.levels
    (Gauge.slopeConstant_pos simple).le (Nat.le_succ (j+1))
  have bill_y:bill≤y:=limited.trans ((Real.rpow_le_rpow_of_exponent_le y₁
    (show Beaming.grain (R.alloy.B.a.clock.J (j+1))≤1 by
      unfold Beaming.grain; apply (div_le_one (by positivity)).2; simp)).trans_eq (Real.rpow_one _))
  have band:= (R.makes.wilson.represents N per (j+1) (Nat.le_of_lt cut)).band
  have upper:= (R.makes.wilson.represents N per ((j+1)+1) (Nat.succ_le_of_lt cut)).band.1
  have mlt:j<N:=by omega
  have small:2*g≤1:=by
    have accepted:(2*g)^(0+1)≤1*g^0:=chilled N per mlt
    simpa only [Nat.zero_add,pow_one,pow_zero,mul_one] using accepted
  have final:(2*g)^(p+1)≤(ε/C)*g^p:=priced N per mlt
  cases order with
  | zero => omega
  | succ rank =>
    have fixed:=chart (x:=x) (y:=y) (β:=(R.family.path.rep N per (j+1)).beta)
      (β':=(R.family.path.rep N per ((j+1)+1)).beta) (grade:=rank) x₁ rise band upper bill_y kpos
      (by omega:prec≤2*rank) depth small
    calc
      _ ≤ 8*x*(8*bill*y^(-((rank+1:ℕ):ℝ))+κ*g'^prec)+κ*g^prec := by
        have nonneg:0≤8*bill*y^(-((rank+1:ℕ):ℝ))+κ*g'^prec:=add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) bd) (Real.rpow_nonneg (zero_le_one.trans y₁) _))
          (mul_nonneg kpos.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
        exact add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (wallet R j slots active) (by norm_num:0≤(8:ℝ))) nonneg) (le_refl (κ*g^prec))
      _ ≤ C*(2*g)^(p+1):=fixed
      _ ≤ C*((ε/C)*g^p):=mul_le_mul_of_nonneg_left final cp.le
      _ = _:=by field_simp [ne_of_gt cp]

end YM.Integration.WilsonReceivedFirstCalibratedRate
