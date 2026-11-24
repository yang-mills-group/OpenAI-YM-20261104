import YM.Integration.WilsonPhysicalHistoryFieldAnchors
import YM.Integration.WilsonWindowReportingPace

/-! Uniformly purchase the actual finite relative child displacements
from the chosen single-run slow block size and prescribed temperature. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryOffsetFare
open Filter Function Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Exterior Stationary Lotus Next.Foundations RG16 RG16.Literal RG16.Guarding
open PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical MSbar MSbar.Whisk
open scoped Classical Topology
variable {G : Gauge}

theorem displacement {l n : Side} (x y : Site l) :
    separation (wrap n (lift x)) (wrap n (lift y)) ≤ 2*l.val := by
  have bound (z : Site l) : separation (wrap n (lift z)) 0 ≤ l.val := by
    rw [separation,sub_zero]
    apply Finset.sup_le
    intro j _
    apply (Next.Free.below_wrap n (lift z) j).trans
    have h := lift_centers z j
    have abs : |lift z j| ≤ (l.val:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    rw [← Int.natCast_natAbs] at abs
    exact_mod_cast abs
  have q := separation_triangle (wrap n (lift x)) 0 (wrap n (lift y))
  rw [separation_comm 0 (wrap n (lift y))] at q
  exact q.trans (by have hx:=bound x;have hy:=bound y;omega)

theorem nonneg (β : ℝ) : 0≤Mosaic.αm β := by
  change 0≤((Real.log β)^2)^(-3:ℤ)
  exact zpow_nonneg (sq_nonneg _) _

private theorem upper {β : ℝ} (h : 1≤Real.log β) : Mosaic.αm β≤1 := by
  have h1 : (1:ℝ)≤((Real.log β)^2)^3 := one_le_pow₀ (one_le_pow₀ h)
  calc
    _ = (((Real.log β)^2)^3)⁻¹ := by change ((Real.log β)^2)^(-3:ℤ)=_;rw [zpow_neg];rfl
    _ ≤ (1:ℝ)⁻¹ := inv_anti₀ zero_lt_one h1
    _ = _ := inv_one

/-- Fixed costs in the measured log clock are paid directly in the temperature
of the archived `BankPaid` consumer, with no choice of cutoff or torus. -/
theorem temperature (R : Run G) (simple : G.Simple) (B : ℝ) (B0 : 0≤B) (m : ℕ)
    {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, B*(RG16.Lambda R.family.path.levels i)^m ≤
      (R.family.path.levels.clock.hatBeta i)^δ := by
  let C := R.family
  let V := RG16.Lambda C.path.levels
  let t := δ/2
  have t0 : 0<t := half_pos δ0
  let A := (B+1)*t⁻¹^m
  have A0 : 0<A := by dsimp [A]; positivity
  have rise : Tendsto (fun i=>t*V i) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos t0).mpr (lambda_leads C simple)
  have lim := ((Real.isLittleO_pow_exp_atTop (n:=m)).comp_tendsto rise).bound (inv_pos.mpr A0)
  filter_upwards [lim,(lambda_leads C simple).eventually_ge_atTop 4] with i hc high
  have V0 : 0≤V i := (lambda_pos C _).le
  change ‖(t*V i)^m‖ ≤ A⁻¹*‖Real.exp (t*V i)‖ at hc
  rw [Real.norm_of_nonneg (pow_nonneg (mul_nonneg t0.le V0) _),
    Real.norm_of_nonneg (Real.exp_pos _).le] at hc
  have hcost : A*(t*V i)^m ≤ Real.exp (t*V i) := by
    simpa only [← mul_assoc,mul_inv_cancel₀ A0.ne',one_mul] using mul_le_mul_of_nonneg_left hc A0.le
  have rearr : A*(t*V i)^m=(B+1)*(V i)^m := by
    dsimp [A];rw [mul_pow]
    calc
      _ = (B+1)*(t⁻¹*t)^m*(V i)^m := by rw [mul_pow];ring
      _ = _ := by rw [inv_mul_cancel₀ t0.ne',one_pow,mul_one]
  rw [rearr] at hcost
  have pos : 0<C.path.levels.clock.hatBeta i := zero_lt_one.trans (C.path.levels.fits.delayed i)
  apply ((mul_le_mul_of_nonneg_right (by linarith : B≤B+1) (pow_nonneg V0 _)).trans hcost).trans
  rw [Real.rpow_def_of_pos pos,Real.exp_le_exp]
  change 4≤2+Real.log (C.path.levels.clock.hatBeta i) at high
  change δ/2*(2+Real.log (C.path.levels.clock.hatBeta i))≤Real.log (C.path.levels.clock.hatBeta i)*δ
  nlinarith only [mul_nonneg δ0.le (by linarith only [high] : 0≤Real.log (C.path.levels.clock.hatBeta i)-2)]

/-- One common ultraviolet stage buys the exact anchor displacement for any two
actual child offsets on every later finite torus. -/
theorem paid (R : Run G) (simple : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    (s : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (n : Side) (x y : Site (R.family.S.block i)),
      Whisk.liftW (Mosaic.αm (R.family.path.levels.clock.hatBeta (i+1))) s
        (separation (wrap n (lift x)) (wrap n (lift y))) ≤
      (R.family.path.levels.clock.hatBeta (i+1))^δ := by
  let C := R.family
  obtain ⟨k,fund⟩ := eventually_atTop.mp (temperature R simple ((3:ℝ)^s) (by positivity) (s+2) δ0)
  filter_upwards [eventually_ge_atTop k,(lambda_leads C simple).eventually_ge_atTop 3] with i late big
  intro n x y
  let T := RG16.Lambda C.path.levels (i+1)
  let β := C.path.levels.clock.hatBeta (i+1)
  let v : ℝ := separation (wrap n (lift x)) (wrap n (lift y))
  have v0 : 0≤v := Nat.cast_nonneg _
  have T0 : 0<T := lambda_pos C _
  have step := (lambda_mono C simple).monotone (Nat.le_succ i)
  have T3 : 3≤T := big.trans step
  have temp : 1≤Real.log β := by change 3≤2+Real.log β at T3;linarith only [T3]
  have span : v ≤ 2*Real.log T := by
    have sites := displacement (n:=n) x y
    have geometry := pace.2 i
    change ((C.S.block i).val : ℝ) ≤ Real.log (RG16.Lambda C.path.levels i) at geometry
    calc
      _ ≤ 2*((C.S.block i).val:ℝ) := by
        dsimp only [v,C]
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr sites
      _ ≤ _ := mul_le_mul_of_nonneg_left (geometry.trans (Real.log_le_log (lambda_pos C i) step)) (by norm_num)
  have up : 1+v≤3*T := by linarith only [span,Real.log_le_self T0.le,T3]
  have ex : Real.exp (Mosaic.αm β*v) ≤ T^2 := by
    rw [pow_two,←Real.exp_log T0,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (upper temp) v0
    rw [one_mul] at h
    linarith only [span,h]
  change (1+v)^s*Real.exp (Mosaic.αm β*v)≤_
  apply le_trans _ (fund (i+1) (late.trans (Nat.le_succ i)))
  calc
    _ ≤ (3*T)^s*T^2 := mul_le_mul (pow_le_pow_left₀ (by linarith only [v0]) up _) ex
      (Real.exp_pos _).le (pow_nonneg (by positivity) _)
    _ = _ := by rw [mul_pow,pow_add]; ring

end YM.Integration.WilsonPhysicalHistoryOffsetFare

