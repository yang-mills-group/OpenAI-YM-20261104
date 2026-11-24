import YM.Integration.WilsonCapturedPrimarySale
import YM.Integration.WilsonCapturedPrimarySection

/-! The loss in the true captured-field recovery is fixed by the physical
horizon, originally enrolled source widths and rough capture fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryEngineering

def loss (d h k : ℕ) := 2+(2*h+2+2*d)+k

private theorem spare {g x C : ℝ} (pos : 0 < g) (unit : g ≤ 1) (price : 0 ≤ C)
    {n j : ℕ} (room : n ≤ j) (paid : g^n*x ≤ C) : g^j*x ≤ C := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le room
  calc
    g^(n+u)*x = g^u*(g^n*x) := by rw [pow_add];ring
    _  ≤  g^u*C := mul_le_mul_of_nonneg_left paid (pow_nonneg pos.le _)
    _  ≤  C := mul_le_of_le_one_left price (pow_le_one₀ pos.le unit)

theorem named {g b U : ℝ} (pos : 0<g) (birth : 0<b) (budget : 0 ≤ U)
    (close : g ≤ 3*b) (h : ℕ) : U*b^(-(h:ℝ))  ≤  (U*3^h)/g^h := by
  rw [Real.rpow_neg birth.le,Real.rpow_natCast]
  apply (le_div_iff₀ (pow_pos pos h)).mpr
  calc
    (U*(b^h)⁻¹)*g^h = U*((b^h)⁻¹*g^h) := by ring
    _  ≤  U*((b^h)⁻¹*(3*b)^h) := by gcongr
    _ = _ := by rw [mul_pow];field_simp

theorem absorb {g I w : ℝ} (hg : 0<g) (h1 : g ≤ 1) (fee : 0 ≤ I)
    (read : w  ≤  4/g^2) (date : 8*I*g ≤ 1) {T : ℕ} (enough : 3 ≤ T) :
    (I*g^T)*w ≤ 1/2 := by
  have cap : g^T  ≤  g^3 := pow_le_pow_of_le_one hg.le h1 enough
  calc
    _  ≤  (I*g^3)*(4/g^2) := by
      exact (mul_le_mul_of_nonneg_left read (mul_nonneg fee (pow_nonneg hg.le _))).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap fee) (by positivity))
    _ = 4*I*g := by field_simp
    _  ≤  _ := by linarith

theorem rate {g I H A γ U B w M s error : ℝ} (pos : 0<g) (unit : g ≤ 1)
    (inv : 0 ≤ I) (interp : 0 ≤ H) (floor : 0 ≤ A) (wrap : 0 ≤ γ) (bound : 0 ≤ B)
    (source : 0 ≤ M) (rough : 0 ≤ s) (p d h k : ℕ)
    (column : w ≤ 4/g^2) (name : M ≤ U/g^h) (capture : s ≤ B/g^k)
    (measured : error  ≤  2*(I*g^(p+loss d h k))*
      (A+w*(H*(4*M^2/(g^2*(g^2)^d))+γ*s)+s)) :
    error  ≤  2*I*(A+4*(H*(4*U^2)+γ*B)+B)*g^p := by
  let v := 2*h+2+2*d
  let J := loss d h k
  let F := H*(4*M^2/(g^2*(g^2)^d))
  have F0 : 0 ≤ F := by dsimp [F];positivity
  have w0 : g^2*w  ≤ 4 := by simpa [mul_comm] using (le_div_iff₀ (pow_pos pos 2)).mp column
  have M0 : g^h*M  ≤ U := by simpa [mul_comm] using (le_div_iff₀ (pow_pos pos h)).mp name
  have s0 : g^k*s  ≤ B := by simpa [mul_comm] using (le_div_iff₀ (pow_pos pos k)).mp capture
  have wF : g^v*F  ≤  H*(4*U^2) := by
    have normalize : g^v = (g^h)^2*(g^2*(g^2)^d) := by dsimp [v];simp [pow_add,pow_mul];ring
    calc
      _ = H*(4*(g^h*M)^2) := by dsimp [F];rw [normalize];field_simp
      _  ≤  _ := by gcongr
  have prod : g^(2+v)*(w*F)  ≤  4*(H*(4*U^2)) := by
    calc
      _ = (g^2*w)*(g^v*F) := by rw [pow_add];ring
      _  ≤  _ := mul_le_mul w0 wF (mul_nonneg (pow_nonneg pos.le _) F0) (by norm_num)
  have residue : g^(2+k)*(w*(γ*s))  ≤  4*(γ*B) := by
    calc
      _ = (g^2*w)*(γ*(g^k*s)) := by rw [pow_add];ring
      _  ≤  _ := mul_le_mul w0 (mul_le_mul_of_nonneg_left s0 wrap) (by positivity) (by norm_num)
  have a1 : g^J*A ≤ A := mul_le_of_le_one_left floor (pow_le_one₀ pos.le unit)
  have a2 := spare pos unit (show 0 ≤ 4*(H*(4*U^2)) by positivity) (show 2+v ≤ J by dsimp [J,v,loss]; omega) prod
  have a3 := spare pos unit (show 0 ≤ 4*(γ*B) by positivity) (show 2+k ≤ J by dsimp [J,loss]; omega) residue
  have a4 := spare pos unit bound (show k ≤ J by dsimp [J,loss];omega) s0
  have total : g^J*(A+w*(F+γ*s)+s)  ≤  A+4*(H*(4*U^2)+γ*B)+B := by
    linarith only [a1,a2,a3,a4]
  calc
    error  ≤  _ := measured
    _ = (2*I*g^p)*(g^J*(A+w*(F+γ*s)+s)) := by dsimp only [J,F];rw [pow_add];ring
    _  ≤  (2*I*g^p)*(A+4*(H*(4*U^2)+γ*B)+B) := mul_le_mul_of_nonneg_left total (by positivity)
    _ = _ := by ring

end YM.Integration.WilsonCapturedPrimaryEngineering
