import YM.QuadraticLocal.Earn.Blend
import YM.QuadraticLocal.Pry
/-!
# Reusable stowed weights for a real Model at polynomial temporary radii

Don't normalize by editing models/norm functions or comparison geometry.
This currency move retains all supports and witnesses. Use around steps with
actual β and Appointments.Memory.Tool.Encoding. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn.Scene.Armada
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}{f:ι→ℝ}{P:Passport n V} {R:Census V} {g a e σ ρ r b d:ℝ} {k i' j u i h : ℕ}
variable {X:ι→Row P R G α}{q:Ratio c n}{w:V→ℝ}{t:V→ℕ}
variable (T:Armada X w t σ e j k i)
include T
-- positivity.Of.R eligible.T need Height nonnegative
lemma looks : 0≤ e:= budget_nonneg (T.suggests 0)
lemma higher (he:e≤b) : Armada X w t σ b j k i := { T with suggests c:=budget_loosen (T.suggests c) he }
local notation "ω₁"=> Stoop.radius w r
-- COST normalized with multiplier scratch. ∀ c_E.Frame.L. size.Art. Entity.S.B royalty Rune.V.Node.Work.St.Capt.Widget`
set_option quotPrecheck false
lemma stored (hr:1≤r) : Armada X (Stoop.radius w r) t σ (r⁻¹*e) j k i:=by
    have hw (i:V):0 < (ω₁) i:= div_pos (T.positive i) (zero_lt_one.trans_le hr); refine { T with positive:=hw, suggests:= fun x=>budget_mono (budget_scale (inv_nonneg.mpr (zero_le_one.trans hr)) (T.suggests x)) (fun j=>?_) (fun j=>?_) }
    · split; next=> exact mul_nonneg (Poly.worth hw _).le (mul_pos (X _).sound (Real.exp_pos _)).le
      next=> rfl
    split; next=> rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (Stoop.shrink w ((X j).mode) (X j).binder.live T.positive hr) (mul_pos (X j).sound (Real.exp_pos _)).le
    next=>rw [mul_zero]
omit T
lemma wallet (t:V→ℝ)(p:ℝ)(v:ℕ) (he:r=p^v): Stoop.radius (Stoop.radius t p) r= Stoop.radius t (p^(v+1)):= by funext i; unfold Stoop.radius; rw [div_div,he,pow_succ']
end YM.QuadraticLocal.Earn.Scene.Armada
