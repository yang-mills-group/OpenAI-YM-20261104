import YM.Frontier.Tuning.VertexPay
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan

/-! The comparison covariance of a window, in real physical displacement units.
Changing z in the right half-plane has a Jacobian/norm cost depending on the dimension
of this contour, not the path length or a Gibbs denominator. For disconnected selections
we will use this on each support-marginal, not with full dimension per support.
This alone isn't the Taylor/gauge expansion or a Markov-chain estimate on β. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.GaussContour
open Matrix MeasureTheory Filter Set ConnectedActivityE6 Blaze Shield Poll ComplexVertex
open scoped BigOperators Topology Classical ENNReal Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Space (ι:Type):= Body ι

def qform (K:Matrix ι ι ℝ) (u: Space ι) := dotProduct (WithLp.ofLp u) (K *ᵥ WithLp.ofLp u)/2
lemma q_smul (K:Matrix ι ι ℝ) (u:Space ι) (r:ℝ) : qform K (r • u)=r^2 * qform K u:=by
  unfold qform dotProduct Matrix.mulVec; rw [Finset.sum_div,Finset.sum_div,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  change ((r*(WithLp.ofLp u i))*(∑ j,K i j*(r*WithLp.ofLp u j)))/2=r^2*_ -- inspect
  simp_rw [show ∀ j,K i j*(r*WithLp.ofLp u j)=r*(K i j*WithLp.ofLp u j) from fun j=>by ring,← Finset.mul_sum]; unfold dotProduct; ring

def prefactor (K:Matrix ι ι ℝ) := ((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp (-(Real.log K.det)/2)
def lens (K:Matrix ι ι ℝ) (z:ℂ) (u: Space ι) := prefactor K * Complex.exp (((Fintype.card ι/2:ℂ) * Complex.log z) - z * qform K⁻¹ u)
lemma lens₀_eq (K:Matrix ι ι ℝ) u : lens₀ K u=prefactor K * Real.exp (-qform K⁻¹ u):=by unfold lens₀ prefactor qform; rw [mul_assoc,←Real.exp_add]; ring_nf
lemma lensAt (K:Matrix ι ι ℝ){β:ℝ} (hβ:0<β)(u:Space ι) : lens K β u=((Real.sqrt β^Fintype.card ι* lens₀ K (Real.sqrt β • u):ℝ):ℂ):=by
   have he : (↑(Fintype.card ι):ℝ)/2*Real.log β= (↑(Fintype.card ι):ℝ)*Real.log (Real.sqrt β):= by rw [Real.log_sqrt hβ.le]; ring
   have h' : (Fintype.card ι /2:ℂ) = Complex.ofReal ((Fintype.card ι:ℝ)/2):= by simp [Complex.ofReal_natCast, Complex.ofReal_div]
   rw [lens₀_eq, q_smul, Real.sq_sqrt hβ.le,lens,h',← Complex.ofReal_log hβ.le,← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_exp,← Complex.ofReal_mul]; apply congr_arg Complex.ofReal
   rw [sub_eq_add_neg,Real.exp_add,he,Real.exp_nat_mul,Real.exp_log (Real.sqrt_pos.mpr hβ)]; ring
private theorem cast_power : Complex.ofReal ((↑(Fintype.card ι):ℝ)/2) = (Fintype.card ι/2:ℂ):=by simp

def markup (ι:Type)[Fintype ι] (z : ℂ):=Real.exp (Fintype.card ι / 2 * Real.log (‖z‖/z.re))
lemma absolute (K:Matrix ι ι ℝ){z:ℂ}(hz:0<z.re) (u:Space ι):
    ‖lens K z u‖ = markup ι z * ((Real.sqrt z.re)^Fintype.card ι * lens₀ K (Real.sqrt z.re • u)) := by
  have he : 0<‖z‖:=norm_pos_iff.mpr (fun h=>show False from by subst z; simpa using not_lt.mpr (le_refl (0:ℝ)) hz)
  unfold lens; rw [← cast_power]; simp only [norm_mul,Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0≤ prefactor K by unfold prefactor; positivity),Complex.norm_exp,Complex.sub_re,Complex.mul_re,Complex.ofReal_im, Complex.ofReal_re,zero_mul,mul_zero,sub_zero,Complex.log_re]
  rw [show (Real.sqrt z.re)^Fintype.card ι = Real.exp ((↑(Fintype.card ι):ℝ)/2*Real.log z.re) by rw [show (↑(Fintype.card ι):ℝ)/2*Real.log z.re= ↑(Fintype.card ι)*Real.log (Real.sqrt z.re) by rw [Real.log_sqrt hz.le]; ring, Real.exp_nat_mul,Real.exp_log (Real.sqrt_pos.mpr hz)], lens₀_eq,q_smul, Real.sq_sqrt hz.le]
  let c:=(↑(Fintype.card ι):ℝ)/2
  suffices he : Real.exp (c * Real.log ‖z‖ - z.re * qform K⁻¹ u) = Real.exp (c * Real.log (‖z‖/z.re)) * Real.exp (c*Real.log z.re) * Real.exp (-(z.re*qform K⁻¹ u)) by rw [he]; unfold markup c; ring
  rw [← Real.exp_add, ← Real.exp_add, Real.log_div he.ne' hz.ne']; apply congr_arg Real.exp; ring
def evaluate (K:Matrix ι ι ℝ) (v : Space ι → ℂ) (z:ℂ) := ∫ u,lens K z u*v u
lemma evaluate_real (K: Matrix ι ι ℝ) (hK:K.PosDef) (v : Space ι→ℂ) {z:ℝ}(hz:0<z):
    evaluate K v z=∫ a, v ((Real.sqrt z)⁻¹ • a) ∂Poll.sweep K:=by
  let f (a:Space ι):= ((lens₀ K a):ℂ) * v ((Real.sqrt z)⁻¹ • a)
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ:=volume) (R:=Real.sqrt z) f (hR:=Real.sqrt_nonneg _)
  unfold evaluate; simp_rw [lensAt K hz,Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul]
  have hv a: ((lens₀ K (Real.sqrt z • a):ℝ):ℂ) * v a= f (Real.sqrt z • a):=by unfold f; rw [smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr hz).ne',one_smul]
  simp_rw [hv]; rw [h,magnifies K hK]
  have hM: Measurable (fun a => lens₀ K a):= bulbB (S:=fun _ : Space ι=>K) (fun _ _=> measurable_const) (z:=id) measurable_id
  rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ K x)) from ENNReal.measurable_ofReal.comp hM) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top)),finrank_euclideanSpace]
  simp only [Complex.real_smul, ← mul_assoc,← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero _ (Real.sqrt_pos.mpr hz).ne'),Complex.ofReal_one,one_mul]; apply integral_congr_ae; filter_upwards with x using by unfold f; rw [ENNReal.toReal_ofReal (fullFuel K x).le]

def rebate (K:Matrix ι ι ℝ) (v : Space ι→ℂ) (z : ℝ) := ∫ a, lens₀ K a * ‖v ((Real.sqrt z)⁻¹ • a)‖
lemma evaluate_cap (K:Matrix ι ι ℝ)(v:Space ι→ℂ){z:ℂ}(hz :0<z.re):
    ‖evaluate K v z‖ ≤ markup ι z * rebate K v z.re:= by
   let q u := lens₀ K u * ‖v ((Real.sqrt z.re)⁻¹ • u)‖
   have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ:=volume) (R:=Real.sqrt z.re) q (hR:=Real.sqrt_nonneg _)
   unfold evaluate; refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
   simp_rw [norm_mul,absolute _ hz, mul_assoc, show ∀ u:Space ι, lens₀ K (Real.sqrt z.re • u)* ‖v u‖ = q (Real.sqrt z.re • u) from fun u=> by unfold q; rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hz).ne',one_smul]]
   rw [integral_const_mul,integral_const_mul,h]; unfold rebate; dsimp only [q,smul_eq_mul]; rw [finrank_euclideanSpace,← mul_assoc ((Real.sqrt z.re)^Fintype.card ι), mul_inv_cancel₀ (pow_ne_zero _ (Real.sqrt_pos.mpr hz).ne'),one_mul]
lemma rebate_eq (K:Matrix ι ι ℝ)(hK:K.PosDef)(v:Space ι → ℂ)(z:ℝ): rebate K v z= ∫ a, ‖v ((Real.sqrt z)⁻¹ • a)‖ ∂ Poll.sweep K:=by unfold rebate; rw [← Shield.recommends K hK]
lemma lens_analytic (K:Matrix ι ι ℝ) {z:ℂ}(hz:z∈Complex.slitPlane) (u : Space ι): DifferentiableAt ℂ (lens K · u) z:=((differentiableAt_const _).mul ((((Complex.differentiableAt_log hz).const_mul _).sub ((differentiableAt_id (𝕜:=ℂ)).mul_const _)).cexp))
end YM.Frontier.Tuning.GaussContour
