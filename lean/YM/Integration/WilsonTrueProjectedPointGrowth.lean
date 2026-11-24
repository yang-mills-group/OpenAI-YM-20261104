import YM.Integration.WilsonTrueProjectedPointClock

/-! A fixed inverse prefix on the original clock incurs a polynomial of the
initial logarithmic temperature and of the elapsed logarithmic scale. An
arbitrarily small portion of the physical contraction pays the latter. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointGrowth

private theorem polynomial (m : ℕ) {δ : ℝ} (pos : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1+t)^m ≤ C*Real.exp (δ*t) := by
  refine ⟨Real.exp δ*(m.factorial:ℝ)/δ^m,by positivity,?_⟩
  intro t ht
  have k : 0 < (m.factorial:ℝ) := by positivity
  have bound := (div_le_iff₀ k).mp
    (Real.pow_div_factorial_le_exp (δ*(1+t)) (by positivity) m)
  rw [mul_pow, mul_add, mul_one,Real.exp_add] at bound
  calc
    _ ≤ Real.exp δ*Real.exp (δ*t)*(m.factorial:ℝ)/δ^m :=
      (le_div_iff₀ (pow_pos pos _)).mpr (by simpa only [mul_comm ((1+t)^m)] using bound)
    _ = _ := by ring

theorem original (q v h : ℕ) {σ A M δ : ℝ}
    (slope : 0 ≤ σ) (count : 0 ≤ A) (fund : 0 ≤ M) (margin : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n l : ℕ}, l ≤ h → ∀ {Λ t : ℝ}, 1 ≤ Λ → 0 ≤ t →
      (n:ℝ)*Real.log 3 ≤ t →
      (1+A*((2*(1+σ*t))^q*(M*(Λ+σ*t)^v))*(n+1))^l ≤
      C*Λ^((q+v+3)*h)*Real.exp (δ*t) := by
  let m := (q+v+3)*h
  let W : ℝ := 3+2*σ+A+M+(Real.log 3)⁻¹
  have lg : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hi : 0 ≤ (Real.log 3)⁻¹ := (inv_pos.mpr lg).le
  have W1 : 1 ≤ W := by dsimp [W]; linarith
  have ws : 2*(1+σ) ≤ W := by dsimp [W]; linarith
  have wa : A ≤ W := by dsimp [W]; linarith
  have wm : M ≤ W := by dsimp [W]; linarith
  have wl : 1+(Real.log 3)⁻¹ ≤ W := by dsimp [W]; linarith
  obtain ⟨C,positive,decay⟩ := polynomial m margin
  refine ⟨2^h*W^m*C,by have := zero_lt_one.trans_le W1; positivity,?_⟩
  intro n l degree Λ t base non time
  let U := W*Λ*(1+t)
  have one : (1:ℝ) ≤ 1+t := by linarith
  have Wpos := zero_le_one.trans W1
  have hu : W ≤ U := (le_mul_of_one_le_right Wpos base).trans
    (le_mul_of_one_le_right (mul_nonneg Wpos (zero_le_one.trans base)) one)
  have u1 := W1.trans hu
  have geom : W*(1+t) ≤ U := mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right Wpos base) (zero_le_one.trans one)
  have therm : 2*(1+σ*t) ≤ U := calc
    _ ≤ 2*(1+σ)*(1+t) := by nlinarith only [slope,non]
    _ ≤ W*(1+t) := mul_le_mul_of_nonneg_right ws (zero_le_one.trans one)
    _ ≤ U := geom
  have spatial : Λ+σ*t ≤ U := calc
    _ ≤ (1+σ)*Λ*(1+t) := by
      have x := mul_nonneg (sub_nonneg.mpr base) (mul_nonneg slope non)
      have y := mul_nonneg slope (zero_le_one.trans base)
      have z := mul_nonneg (zero_le_one.trans base) non
      nlinarith only [x,y,z]
    _ ≤ U := by
      dsimp only [U]
      gcongr
      linarith only [ws,slope]
  have dates : (n:ℝ)+1 ≤ U := calc
    _ ≤ t*(Real.log 3)⁻¹+1 := by
      rw [←div_eq_mul_inv]
      exact add_le_add ( (le_div_iff₀ lg).mpr time) le_rfl
    _ ≤ (1+(Real.log 3)⁻¹)*(1+t) := by nlinarith only [hi,non]
    _ ≤ W*(1+t) := mul_le_mul_of_nonneg_right wl (zero_le_one.trans one)
    _ ≤ U := geom
  have expensive : A*((2*(1+σ*t))^q*(M*(Λ+σ*t)^v))*((n:ℝ)+1) ≤ U^(q+v+3) := calc
    _ ≤ U*(U^q*(U*U^v))*U := by
      have h1 := zero_le_one.trans u1
      have c := zero_le_one.trans base
      have ac := wa.trans hu
      have mc := wm.trans hu
      gcongr
    _ = _ := by rw [pow_add,pow_add];ring
  have cap : 1+A*((2*(1+σ*t))^q*(M*(Λ+σ*t)^v))*((n:ℝ)+1) ≤ 2*U^(q+v+3) := by
    linarith only [expensive,one_le_pow₀ u1 (n:=q+v+3)]
  have raw : 0 ≤ 1+A*((2*(1+σ*t))^q*(M*(Λ+σ*t)^v))*((n:ℝ)+1) := by
    have := zero_le_one.trans base
    positivity
  have head : 1 ≤ 2*U^(q+v+3) := by linarith only [one_le_pow₀ u1 (n:=q+v+3)]
  calc
    _ ≤ (2*U^(q+v+3))^h := (pow_le_pow_left₀ raw cap _).trans (pow_le_pow_right₀ head degree)
    _ = 2^h*W^m*Λ^m*(1+t)^m := by dsimp only [U,m];rw [mul_pow,←pow_mul,mul_pow,mul_pow];ring
    _ ≤ (2^h*W^m*Λ^m)*(C*Real.exp (δ*t)) :=
      mul_le_mul_of_nonneg_left (decay t non) (by have := zero_le_one.trans base; positivity)
    _ = _ := by dsimp only [m];ring

end YM.Integration.WilsonTrueProjectedPointGrowth
