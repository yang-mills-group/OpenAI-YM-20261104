import YM.Integration.WilsonMarkedSalaryHit

/-! The uncapped Wilson group field charges the grade of its source for
each inverse coupling, independently of the requested Taylor accuracy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedFixedPoleGross
open Function Filter Finset Lattice Wilson RG Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Poetry
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V I X : Type} [DecidableEq V] {P : Passport n V} {J : Census V}

theorem field (T : Row P J G X) {g σ : ℝ} (gp : 0<g) (small : g ≤ 1) (width : 0<σ)
    (valid : T.Graceful σ) (book : T.Budget) (K d : ℕ) (rank : T.lamp.r ≤ K)
    (stamp : T.lamp.r ≤ T.lamp.e+d) (x : X) (U : Config G n) :
    ‖T.nominal g x U‖ ≤ (2^K/g^d)*T.salary := by
  have mg : T.atom.magnitude ≤ 1 := (T.atom.lower_budget σ width).trans valid
  have pole : |g^T.lamp.lag| ≤ (g^d)⁻¹ := by
    rw [abs_of_nonneg (zpow_nonneg gp.le _),QuadraticLocal.Sunrise.Loan.lag,zpow_sub₀ gp.ne',
      zpow_natCast,zpow_natCast,←one_div,div_le_div_iff₀ (pow_pos gp _) (pow_pos gp _)]
    simpa only [←pow_add,one_mul] using pow_le_pow_of_le_one gp.le small stamp
  have nominal : ‖T.nominal g x U‖ ≤ T.salary*(|g^T.lamp.lag| *(T.atom.magnitude*2^T.lamp.r)) := by
    rw [Row.nominal,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Row.grain,abs_mul]
    exact mul_le_mul (book x) (mul_le_mul_of_nonneg_left (T.atom.unmasked_bound U T.center) (abs_nonneg _))
      (by positivity) T.sound.le
  have scale : |g^T.lamp.lag| *(T.atom.magnitude*2^T.lamp.r) ≤ (g^d)⁻¹*(1*2^K) := by
    apply mul_le_mul pole (mul_le_mul mg (pow_le_pow_right₀ (by norm_num) rank) (by positivity) zero_le_one)
      (mul_nonneg (by exact sum_nonneg fun _ _=>abs_nonneg _) (by positivity)) (by positivity)
  exact (nominal.trans (mul_le_mul_of_nonneg_left scale T.sound.le)).trans_eq (by ring)

theorem landed (M : I→Row P J G X) (w : V→ℝ) (t : V→ℕ) (B : BudgetPoint)
    {g U σ C a ξ : ℝ} {j k l : ℕ} (L : Scene.Armada M w t σ C j k l)
    (fund : Invoice.Supports B U a g σ ξ) (d : ℕ) (fees : ∀s:J.Mode,(∑v∈s.val,t v)+1 ≤ d) :
    WilsonRootedKioskOccupiedSlip.Gross (rendered M B g) w B.B a
      ((2^(j+l+1)/g^d)*(Invoice.price B U (j+l+1) k a ξ G*C)) := by
  let φ:=2^(j+l+1)/g^d
  let f i:=φ*(M i).salary
  have gp:=fund.1
  have pos : 0≤φ:=by dsimp only [φ];positivity
  obtain ⟨α,xi,wide⟩:=fund.2.2.2.2.2
  have sa : 0<σ:=by nlinarith only [xi,wide,mul_nonneg α (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) B.B))]
  refine ⟨f,fun i=>mul_nonneg pos (M i).sound.le,?_,?_⟩
  · intro i x U'
    have stamp : (M i).lamp.r ≤ (M i).lamp.e+d := by
      have h:=(M i).lamp.crest
      rw [(L.purchases.usable i).2] at h
      exact h.trans (by rw [Nat.add_assoc];exact Nat.add_le_add_left (fees _) _)
    exact field (M i) gp fund.2.1 sa (L.purchases.spend i) (L.honor i) (j+l+1) d
      (Scene.Armada.degreeR _ L.toMinistry (M i) (L.purchases.usable i)).2.2 stamp x U'
  · change Hit (fun i=>(M i).ground B) B.B (fun i=>Poly.toll w (M i).mode*f i) a _
    intro x
    convert budget_scale pos (WilsonMarkedSalaryHit.original M w t B L fund x) using 1
    funext i
    by_cases hi:x∈(M i).ground B
    · simp only [hi,if_true,f];ring
    · simp only [hi,if_false,mul_zero]

end YM.Integration.WilsonMarkedFixedPoleGross
