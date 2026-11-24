import YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
import YM.Integration.FundedMarkedPeriodPowers
import YM.Integration.LocalComparisonJetNormalization

/-! The real period and the elected running clock absorb one complete
finite-volume heat tariff at every original date before either limit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatScale
open Filter Lattice RG Wilson Precision WilsonCoeffUV.Bank.Ticket
open ActualRunAdmissionScales ActualRunAdmissionClock Next.Foundations PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge}

def rate (A : Levels G) (m p : ℕ) : ℝ :=
  Real.exp (-((A.S.side m p).val : ℝ)/(16*zz A m))

theorem clock (A : Levels G) (simple : G.Simple) :
    ∀ᶠ m : ℕ in atTop, 1 ≤ zz A m ∧ 0 < zz A (m+1) ∧ zz A (m+1) ≤ 2*zz A m := by
  have rise : Tendsto (zz A) atTop atTop := tendsto_atTop_add_const_left _ _
    (Real.tendsto_log_atTop.comp (Multi.Wage.log_tend simple A))
  have finer : Tendsto (fun m : ℕ => m+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [rise.eventually_ge_atTop 1,(rise.comp finer).eventually_gt_atTop 0,
    (WardBin.bell A simple).eventually_ge_atTop 2,
    ((WardBin.bell A simple).comp finer).eventually_ge_atTop 2,
    LocalComparison.JetNormalization.adjacent_beta A simple] with m hz hz' hb hb' hnext
  change 2 ≤ A.clock.hatBeta (m+1) at hb'
  refine ⟨hz,hz',?_⟩
  have L := Real.log_le_log (by linarith : 0<A.clock.hatBeta (m+1)) hnext
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : A.clock.hatBeta m≠0)] at L
  have L0 := Real.log_le_log (by norm_num : (0:ℝ)<2) hb
  have L1 := Real.log_le_log (Real.log_pos (by linarith : 1<A.clock.hatBeta (m+1)))
    (show Real.log (A.clock.hatBeta (m+1)) ≤ 2 * Real.log (A.clock.hatBeta m) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.log_pos (by linarith : 1<A.clock.hatBeta m)).ne'] at L1
  have two := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  unfold zz at hz ⊢
  linarith

theorem power (x f z c : ℝ) (hx : 2≤f) (hz : 0≤z) (hZ : z≤f)
    (hc : 0≤c) (hC : c≤f) (D : ℕ) (hx' : x=z*(1+f)^4) :
    2*x^D ≤ f^(9*D+1) ∧ 2*(z*c)^D ≤ f^(9*D+1) := by
  have hf : 1 ≤ f := by linarith
  have hfun : 1+f ≤ f^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hf)]
  have px : x ≤ f^9 := by
    rw [hx']
    calc z*(1+f)^4 ≤ f*(f^2)^4 := mul_le_mul hZ (pow_le_pow_left₀ (by linarith) hfun 4) (by positivity) (by linarith)
         _ = f^9 := by ring
  have pc : z*c ≤ f^9 := calc
    z*c ≤ f*f := mul_le_mul hZ hC hc (by linarith)
    _ = f^2 := by ring
    _ ≤ f^9 := pow_le_pow_right₀ hf (by decide)
  rw [pow_succ, pow_mul]
  constructor
  · simpa [mul_comm] using mul_le_mul hx (pow_le_pow_left₀ (by rw [hx']; positivity) px D) (by rw [hx']; positivity) (by linarith)
  · simpa [mul_comm] using mul_le_mul hx (pow_le_pow_left₀ (mul_nonneg hz hc) pc D) (by positivity) (by linarith)

/-- At the actual fine side a complete fixed power of the physical-size
tariff and the independent fresh winding error fit the coarse rate. -/
theorem original (R : Run G) (simple : G.Simple) (paid : RG05Preconstruction.ReadoutPurchase R.b)
    (D : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ p : ℕ,
    let A := R.family.path.levels
    let n : ℝ := (A.S.side m p).val
    let f : ℝ := (A.S.side (m+1) p).val
    (zz A m*(1+f)^4)^D * rate A (m+1) p +
      (zz A m * admittedCost A m)^D*Real.exp (-n/(4*zz A m)) ≤ rate A m p := by
  let A := R.family.path.levels
  have mesh := ActualRunQLocalAdmission.actual_preMesh R paid
  filter_upwards [clock A simple,OriginalPeriodWindingPrice.period_power A 1,
    (WardBin.bell A simple).eventually_ge_atTop 2,FundedMarkedPeriodPowers.expense A simple,
    cost_subpower R.family simple R.makes mesh 1 zero_lt_one,
    actual_inverse_lower R.family simple R.makes mesh,
    FundedMarkedPeriodPowers.absorb A simple (9*D+1)] with m hz hm hb hzc hcost hg0 hpaid p
  let n : ℝ := (A.S.side m p).val
  let f : ℝ := (A.S.side (m+1) p).val
  let z := zz A m
  let z' := zz A (m+1)
  let C := admittedCost A m
  change (z*(1+f)^4)^D * Real.exp (-f/(16*z')) + (z*C)^D*Real.exp (-n/(4*z)) ≤ Real.exp (-n/(16*z))
  have hzn : 1≤z := hz.1
  have hpz : 0<z := by linarith
  have hpz' : 0<z' := hz.2.1
  have hzz : z' ≤ 2*z := hz.2.2
  have hnb : A.clock.hatBeta m ≤ n := by simpa [n] using hm p
  have hn : 2≤n := hb.trans hnb
  have hthree : 3*n ≤ f := by
    have hL : (3:ℝ)≤(A.S.block m).val := by exact_mod_cast A.S.block_large m
    have hs : f = n * ((A.S.block m).val : ℝ) := by
      dsimp [f,n]
      exact_mod_cast (A.S.oneStep m p).exact_size
    rw [hs, mul_comm n]
    exact mul_le_mul_of_nonneg_right hL (by linarith)
  have hnf : n≤f := by linarith
  let g := Pert.Asymptotics.regulatorRun R.family (m+1) p (m+1)
  have hg : 0<g := IterationFour.Currency.g_pos R.makes (m+1) p (m+1) (by rfl)
  have hc0 : C≤g⁻¹ := by simpa only [Real.rpow_neg_one] using hcost (m+1) p (by omega)
  have hi := inv_anti₀ (inv_pos.mpr (show 0<A.clock.hatBeta m by linarith)) (hg0 (m+1) p (by omega))
  have hc : C≤n := hc0.trans ((by simpa only [inv_inv] using hi : g⁻¹≤A.clock.hatBeta m).trans hnb)
  have hbills := power (z*(1+f)^4) f z C (hn.trans hnf) hpz.le (by linarith)
    (by exact (admittedCost_one A m).trans' zero_le_one) (hc.trans hnf) D rfl
  have hh := (hpaid p z⁻¹ (inv_pos.mpr hpz) (by simp [z])).2
  have he : f^(9*D+1) ≤ Real.exp (n/(1024*z)) := calc
    f^(9*D+1) = (f^(9*D+1)*Real.exp (-(z⁻¹/512)*n))*Real.exp ((z⁻¹/512)*n) := by
      rw [mul_assoc, ← Real.exp_add]; simp [neg_mul]
    _ ≤ Real.exp (-((z⁻¹/2)/512)*n)*Real.exp ((z⁻¹/512)*n) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp; ring
  have h_old : n/(1024*z) + -f/(16*z') ≤ -n/(16*z) := by
    apply (le_div_iff₀ (by positivity : 0<16*z)).mpr
    field_simp [hpz.ne',hpz'.ne']
    nlinarith [mul_le_mul_of_nonneg_left hzz (show 0≤n by linarith),
      mul_le_mul_of_nonneg_left hthree hpz.le]
  have h_fresh : n/(1024*z) + -n/(4*z) ≤ -n/(16*z) := by
    apply (le_div_iff₀ (by positivity : 0<16*z)).mpr
    field_simp [hpz.ne']; linarith
  have old := calc
    2*((z*(1+f)^4)^D*Real.exp (-f/(16*z'))) ≤ Real.exp (n/(1024*z))*Real.exp (-f/(16*z')) := by
      rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hbills.1.trans he) (Real.exp_pos _).le
    _ ≤ Real.exp (-n/(16*z)) := by rw [←Real.exp_add]; exact Real.exp_le_exp.mpr h_old
  have fresh := calc
    2*((z*C)^D*Real.exp (-n/(4*z))) ≤ Real.exp (n/(1024*z))*Real.exp (-n/(4*z)) := by
      rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hbills.2.trans he) (Real.exp_pos _).le
    _ ≤ Real.exp (-n/(16*z)) := by rw [←Real.exp_add]; exact Real.exp_le_exp.mpr h_fresh
  linarith

end YM.Integration.WilsonVacuumPreResetFiniteHeatScale
