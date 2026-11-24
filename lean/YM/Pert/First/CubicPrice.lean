import YM.Pert.First.PathJet
/-! Wilson price cubic computed as norm-square derivative, not an isolated amplitude coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Pert.First
open Filter Orb Function Matrix Gauge Topology NormedSpace
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {N : Lattice.Side}
attribute [local instance] Gauge.frobInner
lemma equal_penalty (y : G.El) : G.price y = ((2*(↑G.repDim:ℝ))⁻¹ * inner ℝ (G.mat y-1) (G.mat y-1)) := by
  have he := G.chord_price y
  simp only [real_inner_self_eq_norm_sq, chord,div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at *
  have hv : (↑G.repDim:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.dimPos)
  rw [div_eq_iff hv] at he; rw [he]; field_simp [hv]
lemma square_transverse (v : G.Color) : inner ℝ (G.colorMat v) (G.colorMat v * G.colorMat v) = (0:ℝ) := by
  let A:= G.colorMat v
  have he := real_inner_comm A (A*A)
  change (A*A * star A).trace.re = (A * star (A*A)).trace.re at he
  rw [star_mul,G.colorMat_skew v, mul_neg,neg_mul_neg,Matrix.trace_neg,Complex.neg_re] at he -- note redundant rw? test
  change (A*star (A*A)).trace.re=0
  rw [star_mul,G.colorMat_skew v,neg_mul_neg]; rw [mul_assoc] at he
  change -(A*(A*A)).trace.re = (A*(A*A)).trace.re at he
  linarith -- maybe twice?
lemma crossing_inner (v a : G.Color) : inner ℝ (G.colorMat v) (defect v a) = (↑ G.repDim : ℝ)*inner ℝ v a := by
  rw [defect,inner_add_right,pow_two,square_transverse,zero_add]
  change (G.colorMat v*star (G.colorMat a)).trace.re = _
  exact (by simp only [G.colorMat_skew,mul_neg,Matrix.trace_neg,Complex.neg_re,G.trace_color])
lemma inner_deriv (f g : ℝ→G.Mat) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) : deriv (fun t=>inner ℝ (f t) (g t)) = fun t=> inner ℝ (f t) (deriv g t) + inner ℝ (deriv f t) (g t) := funext (fun t=> deriv_inner_apply ℝ (hf t) (hg t))
lemma inner_third {f : ℝ→G.Mat} (h : ContDiff ℝ ∞ f) (h0 : f 0 =0) :
    iteratedDeriv 3 (fun t=>inner ℝ (f t) (f t)) 0 =
      6*inner ℝ (deriv f 0) (deriv (deriv f) 0) := by
  let p₀:=f; let p₁:=deriv f; let p₂:=deriv (deriv f)
  let B (f g : ℝ→G.Mat) t:= inner ℝ (f t) (g t)
  have hd : Differentiable ℝ p₀ := h.differentiable (by decide)
  have he : Differentiable ℝ p₁ := (contDiff_infty_iff_deriv.mp h).2.differentiable (by decide)
  have hg : Differentiable ℝ p₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp h).2).2.differentiable (by decide)
  have hB {f g : ℝ→G.Mat} (ha : Differentiable ℝ f) (hb : Differentiable ℝ g) : Differentiable ℝ (B f g) := ha.inner ℝ hb
  have h₁ : iteratedDeriv 1 (B f f)=B f p₁+B p₁ f := (iteratedDeriv_one).trans (inner_deriv f f hd hd)
  have h₂ : iteratedDeriv 2 (B f f)= B f p₂+B p₁ p₁+(B p₁ p₁+B p₂ f) := by
    rw [iteratedDeriv_succ,h₁]; exact (funext fun t=> deriv_add ((hB hd he) t) ((hB he hd) t) |>.trans (by rw [show deriv (B f p₁) t = _ from congrFun (inner_deriv f p₁ hd he) t, show deriv (B p₁ f) t = _ from congrFun (inner_deriv p₁ f he hd) t]; rfl))
  change iteratedDeriv 3 (B f f) 0 = _
  rw [iteratedDeriv_succ,h₂,deriv_add,deriv_add,deriv_add]; rotate_left
  · apply hB he he
  · apply hB hg hd
  · apply hB hd hg
  · apply hB he he
  · apply Differentiable.add (hB hd hg) (hB he he)
  · apply Differentiable.add (hB he he) (hB hg hd)
  rw [inner_deriv f p₂ hd hg, inner_deriv p₁ p₁ he he,inner_deriv p₂ f hg hd]; dsimp only; rw [h0,inner_zero_left, inner_zero_right]; change (0 + inner ℝ (p₁ 0) (p₂ 0) + (inner ℝ (p₁ 0) (p₂ 0) + inner ℝ (p₂ 0) (p₁ 0)) + (inner ℝ (p₁ 0) (p₂ 0) + inner ℝ (p₂ 0) (p₁ 0) + (inner ℝ (p₂ 0) (p₁ 0) + 0))) = _ ; change _ = 6*inner ℝ (p₁ 0) (p₂ 0); rw [real_inner_comm (p₁ 0)]; ring -- orientation
lemma Tried.square3 {p : ℝ→G.El} {v b : G.Color} (h : Tried (G.mat ∘ p) v b) (hd : ContDiff ℝ ∞ (G.mat ∘ p)) : iteratedDeriv 3 (G.price ∘ p) (0:ℝ)/6 = inner ℝ v b/2 := by
  let f := G.mat ∘ p
  have he : G.price ∘ p = fun t=> (2*(↑G.repDim:ℝ))⁻¹* inner ℝ (f t-1) (f t-1) := funext (fun t => equal_penalty (p t))
  have hr : ContDiff ℝ ∞ (fun t=>f t-1) := hd.sub contDiff_const
  have ht : deriv (fun t=> f t-1) = deriv f := by ext1; apply deriv_sub_const
  have H := inner_third hr (sub_eq_zero.2 h.value_eq)
  have hs : deriv (deriv f) 0 = defect v b := by
    change deriv (deriv (G.mat ∘ p)) 0 = _
    convert! h.second using 1
    erw [iteratedDeriv_succ (n:=1)]
    rw [iteratedDeriv_one]; rfl
  rw [ht, (show deriv f 0 =G.colorMat v from (h.slope_eq.choose_spec.2.1 0).deriv.trans h.slope_eq.choose_spec.1), hs,crossing_inner] at H
  -- function-vs-apply rewriting
  rw [he]; try rw [iteratedDeriv_const_mul_field]
  change (2*(↑G.repDim:ℝ))⁻¹ * iteratedDeriv 3 (fun t=>inner ℝ (f t-1) (f t-1)) 0 / 6 = _; rw [H]
  have hw : (↑G.repDim : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt G.dimPos)
  field_simp
end YM.Pert.First
