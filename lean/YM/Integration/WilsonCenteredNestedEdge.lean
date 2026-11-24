import YM.Integration.WilsonCenteredNestedProjectedShadow

/-! Engineering accounting at one strict inner/outer edge.  The interior
through-D gain survives even in its lowest public coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedEdge
open scoped Classical
def port (r : ℝ) (n e : ℕ) : ℝ := r^n / r^e
def base (a r : ℝ) (m e f : ℕ) : ℝ := r^m / (a^e * r^f)

lemma inner {a r : ℝ} (ap : 0 < a) (rp : 0 < r) (D m e f j : ℕ) (jD : j ≤ D) :
    port a (D+1) e * port r m (j+f) =
      base a r m e f * (a/r)^(D+1) * r^(D+1-j) := by
  have restore : r^(D+1-j) * r^j = r^(D+1) := by rw [←pow_add,Nat.sub_add_cancel (by omega : j ≤ D+1)]
  unfold port base
  rw [div_pow,←restore,pow_add r j f]
  field_simp [ap.ne',rp.ne']

lemma outer {a r : ℝ} (ap : 0 < a) (rp : 0 < r) (H m e f j : ℕ) (mH : m ≤ H) :
    port a j e * port r (H+1) (j+f) =
      base a r m e f * (a/r)^j * r^(H+1-m) := by
  have restore : r^m * r^(H+1-m) = r^(H+1) := by rw [←pow_add,Nat.add_sub_of_le (by omega : m ≤ H+1)]
  unfold port base
  rw [div_pow,←restore,pow_add r j f]
  field_simp [ap.ne',rp.ne']

theorem paid {a r : ℝ} (ap : 0 < a) (ar : a ≤ r) (r1 : r ≤ 1)
    (D H m e f j : ℕ) (jD : j ≤ D) (mH : m ≤ H) :
    port a (D+1) e * port r m (j+f) + port a j e * port r (H+1) (j+f) ≤
      base a r m e f * ((a/r)^(D+1) + r^(H+1-m)) := by
  have rp := ap.trans_le ar
  have nn : 0 ≤ base a r m e f := by unfold base;positivity
  have qp : 0 ≤ a/r := div_nonneg ap.le rp.le
  have q1 : a/r ≤ 1 := (div_le_one rp).mpr ar
  rw [inner ap rp D _ _ _ _ jD,outer ap rp H _ _ _ _ mH,mul_add]
  refine add_le_add (mul_le_of_le_one_right (mul_nonneg nn (pow_nonneg qp _)) (pow_le_one₀ rp.le r1)) ?_
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right nn (pow_le_one₀ qp q1)) (pow_nonneg rp.le _)

theorem term {a r W V : ℝ} (ap : 0 < a) (ar : a ≤ r) (r1 : r ≤ 1)
    (D H m e f j : ℕ) (jD : j ≤ D) (mH : m ≤ H)
    (x x' y y' : ℂ) (Wn : 0 ≤ W) (Vn : 0 ≤ V)
    (young : ‖x-x'‖ ≤ W * port a (D+1) e) (older : ‖y-y'‖ ≤ V * port r (H+1) (j+f))
    (innerGross : ‖x'‖ ≤ W*port a j e) (outerGross : ‖y‖ ≤ V*port r m (j+f)) :
    ‖x*y-x'*y'‖ ≤ W*V*base a r m e f*((a/r)^(D+1) + r^(H+1-m)) := by
  have first : ‖x-x'‖ * ‖y‖ ≤ (W*port a (D+1) e)*(V*port r m (j+f)) :=
    mul_le_mul young outerGross (norm_nonneg _) ((norm_nonneg _).trans young)
  have second : ‖x'‖ * ‖y-y'‖ ≤ (W*port a j e)*(V*port r (H+1) (j+f)) :=
    mul_le_mul innerGross older (norm_nonneg _) ((norm_nonneg _).trans innerGross)
  rw [show x*y-x'*y'=(x-x')*y+x'*(y-y') by ring]
  calc
    _ ≤ ‖(x-x')*y‖ + ‖x'*(y-y')‖ := norm_add_le ..
    _ ≤ _ := by simp only [norm_mul];exact add_le_add first second
    _ = W*V*(port a (D+1) e*port r m (j+f)+port a j e*port r (H+1) (j+f)) := by ring
    _ ≤ W*V*(base a r m e f*((a/r)^(D+1) + r^(H+1-m))) :=
      mul_le_mul_of_nonneg_left (paid ap ar r1 D H m e f j jD mH) (mul_nonneg Wn Vn)
    _ = _ := by ring

end YM.Integration.WilsonCenteredNestedEdge
