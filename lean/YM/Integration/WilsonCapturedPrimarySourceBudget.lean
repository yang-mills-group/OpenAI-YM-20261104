import YM.Integration.WilsonReceivedSingletonWindow

/-! The two singleton estimates on the original post in the source
units of the pair and its alternative counterterm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySourceBudget

def cost (g E : ℝ) (order : ℕ) := 2*E+2*E/g+E^2+g^(order+1)/g^2

theorem complete {g E wa wb wc X ma mb ta tb : ℝ} (order : ℕ)
    (hg : 0 < g) (hE : 0 ≤ E) (ha : 0 < wa) (hb : 0 < wb) (hc : 0 < wc)
    (_m0 : 0 ≤ ma) (m1 : 0 ≤ mb) (_t0 : 0 ≤ ta) (_t1 : 0 ≤ tb)
    (am : g*(wa*ma) ≤ 1) (bm : g*(wb*mb) ≤ 1) (at' : g*(wa*ta) ≤ 1) (bt : g*(wb*tb) ≤ 1)
    (observed : X ≤ (E/(wa*wb)+E/wc+E/wa*(tb+E/wb)+ta*(E/wb))+g^(order+1)*(ma*mb)) :
    min (wa*wb) wc * X ≤ cost g E order := by
  let σ := min (wa*wb) wc
  have hs : 0 ≤ σ := le_min (mul_pos ha hb).le hc.le
  have left : σ ≤ wa*wb := min_le_left .. 
  have right : σ ≤ wc := min_le_right ..
  have capA {u : ℝ} (h : g*(wa*u) ≤ 1) : u ≤ 1/(g*wa) :=
    (le_div_iff₀ (mul_pos hg ha)).2 (by linarith only [h,show u*(g*wa)=g*(wa*u) by ring])
  have capB {u : ℝ} (h : g*(wb*u) ≤ 1) : u ≤ 1/(g*wb) :=
    (le_div_iff₀ (mul_pos hg hb)).2 (by linarith only [h,show u*(g*wb)=g*(wb*u) by ring])
  let Z := E/wa*(1/(g*wb)+E/wb)+(1/(g*wa))*(E/wb)+g^(order+1)*(1/(g*wa)*(1/(g*wb)))
  have zout : 0 ≤ Z := by dsimp [Z];positivity
  have upper : X ≤ E/(wa*wb)+E/wc+Z := by
    apply observed.trans
    dsimp only [Z]
    linarith only [mul_le_mul_of_nonneg_left (add_le_add_right (capB bt) (E/wb)) (div_nonneg hE ha.le),
      mul_le_mul_of_nonneg_right (capA at') (div_nonneg hE hb.le),
      mul_le_mul_of_nonneg_left (mul_le_mul (capA am) (capB bm) m1 (by positivity)) (pow_nonneg hg.le (order+1))]
  have first : σ*(E/(wa*wb)) ≤ E := by
    calc
      _ ≤ (wa*wb)*(E/(wa*wb)) := mul_le_mul_of_nonneg_right left (by positivity)
      _ = _ := by field_simp
  have next : σ*(E/wc) ≤ E := by
    calc
      _ ≤ wc*(E/wc) := mul_le_mul_of_nonneg_right right (by positivity)
      _ = _ := by field_simp
  have scaled : wa*wb*Z = 2*E/g+E^2+g^(order+1)/g^2 := by
    dsimp [Z]
    field_simp
    ring
  calc
    σ*X ≤ σ*(E/(wa*wb)+E/wc+Z) := mul_le_mul_of_nonneg_left upper hs
    _ ≤ E+E+wa*wb*Z := by
      rw [mul_add,mul_add]
      exact add_le_add (add_le_add first next) (mul_le_mul_of_nonneg_right left zout)
    _ = cost g E order := by rw [scaled]; unfold cost;ring

theorem paid {g E C : ℝ} (P order : ℕ) (hg : 0 < g) (small : g ≤ 1)
    (he : 0 ≤ E) (hc : 0 ≤ C) (rent : E ≤ C*g^(P+2)) (room : P+2 ≤ order+1) :
    cost g E order ≤ (4*C+C^2+1)*g^P := by
  have power {k : ℕ} (hk : P ≤ k) : g^k ≤ g^P := pow_le_pow_of_le_one hg.le small hk
  have first : E ≤ C*g^P := rent.trans (mul_le_mul_of_nonneg_left (power (by omega)) hc)
  have shifted : E/g ≤ C*g^P := by
    apply (div_le_iff₀ hg).2
    apply rent.trans
    rw [mul_assoc,←pow_succ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le small (by omega)) hc
  have square : E^2 ≤ C^2*g^P := by
    calc
      _ ≤ (C*g^(P+2))^2 := pow_le_pow_left₀ he rent _
      _ = C^2*g^((P+2)*2) := by rw [mul_pow,pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (power (by omega)) (sq_nonneg _)
  have last : g^(order+1)/g^2 ≤ g^P := by
    apply (div_le_iff₀ (pow_pos hg _)).2
    rw [←pow_add]
    exact pow_le_pow_of_le_one hg.le small room
  calc
    cost g E order = 2*E+2*(E/g)+E^2+g^(order+1)/g^2 := by unfold cost; ring
    _ ≤ 2*(C*g^P)+2*(C*g^P)+C^2*g^P+g^P := add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left first (by norm_num))
        (mul_le_mul_of_nonneg_left shifted (by norm_num))) square) last
    _ = _ := by ring

end YM.Integration.WilsonCapturedPrimarySourceBudget
