import YM.Integration.FundedMarkedWindingWindow

/-! Torus powers in a native winding estimate, uniformly over original periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedMarkedPeriodPowers
open Function Filter Lattice Wilson RG Laurent Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket ActualRunAdmissionScales
open scoped Topology

variable {G : Gauge}

/-- The original mesh controls the finer side before the period is selected. -/
theorem next_side (D : Levels G) : ∀ᶠ m : ℕ in atTop, ∀ p,
    ((D.S.side (m+1) p).val : ℝ) ≤ ((D.S.side m p).val : ℝ)^2 := by
  filter_upwards [D.fits.mesh.eventually_lt_const zero_lt_one,D.S.divergent.eventually_gt_atTop 0]
    with m hm hs p
  have logs : Real.log ((D.S.block m).val:ℝ) ≤ D.S.scale m :=
    ((div_lt_iff₀ hs).mp hm).le.trans_eq (one_mul _)
  have hb : (0:ℝ)<(D.S.block m).val := by exact_mod_cast (D.S.block m).pos
  have hd : (0:ℝ)<(D.S.denominator m).val := by exact_mod_cast (D.S.denominator m).pos
  have block := Real.exp_le_exp.mpr logs
  simp only [Schedule.scale,Schedule.a,inv_inv,Real.exp_log hb,Real.exp_log hd] at block
  have per : (1:ℝ)≤(D.S.period p).val := by exact_mod_cast (D.S.period p).pos
  have larger : ((D.S.denominator m).val:ℝ)≤(D.S.side m p).val := by
    simpa only [Schedule.side,PNat.mul_coe,Nat.cast_mul] using le_mul_of_one_le_left hd.le per
  have side : (0:ℝ)≤(D.S.side m p).val := Nat.cast_nonneg _
  calc ((D.S.side (m+1) p).val:ℝ) = (D.S.side m p).val*((D.S.block m).val:ℝ) := by
          simp only [Schedule.side,Schedule.denominator,PNat.mul_coe,Nat.cast_mul,mul_assoc]
       _ ≤ ((D.S.side m p).val:ℝ)^2 := by
          rw [sq]; exact mul_le_mul_of_nonneg_left (block.trans larger) side

/-- Both halves of the rate of this actual donor fit inside its full admission cost. -/
theorem expense (D : Levels G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, 2*zz D m ≤ admittedCost D m := by
  have rise : Tendsto (zz D) atTop atTop := tendsto_atTop_add_const_left _ _
    (Real.tendsto_log_atTop.comp (Multi.Wage.log_tend hG D))
  filter_upwards [rise.eventually_ge_atTop 4] with m hz
  have mon : 2*zz D m ≤ D.clock.monitor m := by
    change _ ≤ Real.exp ((Real.log (Real.log (D.clock.hatBeta m)))^2)
    rw [show Real.log (Real.log (D.clock.hatBeta m))=zz D m-1 by simp [zz]]
    exact (show 2*zz D m ≤ (zz D m-1)^2+1 by
      nlinarith only [hz,sq_nonneg (zz D m-4)]) |>.trans (Real.add_one_le_exp _)
  apply mon.trans
  apply le_trans _ (cost_covers_geometry D m)
  have hp := (D.params m).paths_pos
  have hp' := (D.params (m+1)).paths_pos
  have hc := (D.params m).columns_ge
  have hc' := (D.params (m+1)).columns_ge
  have hr := (D.params m).clip.radius_pos
  have hr' := (D.params (m+1)).clip.radius_pos
  have hm : 0 < D.clock.monitor m := Real.exp_pos _
  have hm' : 0 < D.clock.monitor (m+1) := Real.exp_pos _
  have hl := Real.rpow_nonneg hm.le (D.clock.theta (D.clock.J m))
  have hl' := Real.rpow_nonneg hm'.le (D.clock.theta (D.clock.J (m+1)))
  unfold geometryCost Calendar.loopCap
  linarith [Nat.cast_nonneg (α:=ℝ) (D.clock.coverSize m),Nat.cast_nonneg (α:=ℝ) (D.clock.coverSize (m+1))]

/-- Every original period and positive stored Gear rate can absorb a fixed power of
the full fine size. The divisor 1024 spends half of the true spatial rate. -/
theorem absorb (D : Levels G) (hG : G.Simple) (h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (p : ℕ) (σ : ℝ), 0<σ → σ⁻¹≤zz D m →
      let n : ℝ := (D.S.side m p).val
      let f : ℝ := (D.S.side (m+1) p).val
      (σ/2)⁻¹≤admittedCost D m ∧
        f^h*Real.exp (-(σ/512)*n) ≤ Real.exp (-((σ/2)/512)*n) := by
  let K := (1024:ℝ)^(4*h)
  have lim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (4*h)).const_mul K
  rw [mul_zero] at lim
  obtain ⟨a,paid⟩ := eventually_atTop.mp (lim.eventually_le_const zero_lt_one)
  filter_upwards [next_side D,expense D hG,OriginalPeriodWindingPrice.period_power D 2,
    (Multi.Wage.hat_tend hG D).eventually_gt_atTop 1,
    (Multi.Wage.hat_tend hG D).eventually_ge_atTop (1024*a)]
    with m square invoice large hb ha p σ positive cheap n f
  constructor
  · have eq : (σ/2)⁻¹=2*σ⁻¹ := by field_simp [positive.ne']
    rw [eq]; exact (mul_le_mul_of_nonneg_left cheap (by norm_num)).trans invoice
  let x := Real.sqrt n/1024
  have hn : 0≤n := Nat.cast_nonneg _
  have hf : 0≤f := Nat.cast_nonneg _
  have hr := Real.sqrt_nonneg n
  have root := Real.sqrt_le_sqrt (large p)
  rw [Real.sqrt_sq (zero_le_one.trans hb.le)] at root
  have zx : zz D m ≤ D.clock.hatBeta m := by
    change 1+Real.log (Real.log (D.clock.hatBeta m)) ≤ _
    rw [add_comm]
    exact (Real.add_one_le_exp _).trans ((Real.exp_log (Real.log_pos hb)).le.trans
      (Real.log_le_self (zero_le_one.trans hb.le)))
  have zr := cheap.trans (zx.trans root)
  have scale := mul_le_mul_of_nonneg_right zr positive.le
  rw [inv_mul_cancel₀ positive.ne'] at scale
  have half : x ≤ ((σ/2)/512)*n := by
    have prod := mul_le_mul_of_nonneg_left scale hr
    have hr2 := Real.sq_sqrt hn
    dsimp only [x]; nlinarith only [prod,congrArg (fun t:ℝ=>t*σ) hr2]
  have big : a≤x := by dsimp only [x]; nlinarith only [ha,root]
  have size : f^h ≤ (1024*x)^(4*h) := by
    have eq : 1024*x=Real.sqrt n := by dsimp [x]; ring
    calc f^h ≤ (n^2)^h := pow_le_pow_left₀ hf (square p) _
         _ = ((Real.sqrt n)^2)^(2*h) := by rw [Real.sq_sqrt hn,pow_mul]
         _ = (1024*x)^(4*h) := by rw [eq,←pow_mul]; congr 1; omega
  have raw := paid x big
  change K*(x^(4*h)*Real.exp (-x))≤1 at raw
  have half_paid : f^h*Real.exp (-((σ/2)/512)*n)≤1 := by
    calc _ ≤ (1024*x)^(4*h)*Real.exp (-x) := mul_le_mul size
               (Real.exp_le_exp.mpr (by linarith only [half])) (Real.exp_pos _).le
               (pow_nonneg (by dsimp only [x]; positivity) _)
         _ = K*(x^(4*h)*Real.exp (-x)) := by rw [mul_pow]; dsimp only [K]; ring
         _ ≤ 1 := raw
  calc f^h*Real.exp (-(σ/512)*n) = (f^h*Real.exp (-((σ/2)/512)*n))*Real.exp (-((σ/2)/512)*n) := by
         rw [mul_assoc,←Real.exp_add]; congr 2; ring
       _ ≤ Real.exp (-((σ/2)/512)*n) := (mul_le_mul_of_nonneg_right half_paid
         (Real.exp_pos _).le).trans_eq (one_mul _)

end YM.Integration.FundedMarkedPeriodPowers

