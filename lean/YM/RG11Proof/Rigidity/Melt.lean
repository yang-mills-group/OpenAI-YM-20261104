import YM.RG11Proof.Rigidity.Cauchy

/-!
# Scalar bilocal extraction, second step
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Tensor Analysis Extra.FD SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff

/-- The Taylor coefficients of `qRad` times *any* scalar germ still have the
radial factor. Only the ideal matters; keep the positive-order factorials as
constants. AnalyticAt not needed here. -/
lemma diagonal_taylor {p v : E4 → ℝ} (hp : ContDiffAt ℝ ∞ p 0) (hv : ContDiffAt ℝ ∞ v 0)
    (he : p =ᶠ[𝓝 0] qRad • v) (n : ℕ) : ∃ c : ℝ,
      Tensor.diagonal (coeff p n 0) = qRad • c • Tensor.diagonal (coeff v (n-2) 0) := by
  let i := n-2
  have hl (r : ℕ) : ContDiffAt ℝ r p 0 := hp.of_le (WithTop.coe_le_coe.mpr le_top)
  have ht (r : ℕ) : ContDiffAt ℝ r v 0 := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  let s := ((n.factorial:ℝ)⁻¹ * ((n.choose 2:ℝ)*(2:ℕ).factorial))
  refine ⟨s*(i.factorial:ℝ), funext fun x=> ?_⟩
  have hw : (fun t : ℝ => p (t • x)) =ᶠ[𝓝 0] fun t : ℝ => qRad x * (t^2 * v (t • x)) := by
    have hf : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by simpa using (@continuousAt_id ℝ _ 0).tendsto.smul (tendsto_const_nhds (x:=x))
    refine (he.comp_tendsto hf).mono fun t h=> ?_
    have h : p (t • x)= qRad (t • x) * v (t • x) := h
    change p (t • x)=_; rw [h,pure_square.rad]; change (t^2 * qRad x)* v (t • x)=_; ring
  have hk : ContDiffAt ℝ n (fun t : ℝ => v (t • x)) 0 :=
    (show ContDiffAt ℝ n v ((0:ℝ) • x) from by rw [zero_smul]; exact ht n).comp 0 (contDiffAt_id.smul contDiffAt_const)
  have hr (y : ℝ → ℝ) (hy : ContDiffAt ℝ n y 0) : iteratedDeriv n ((fun t : ℝ => t^2) * y) 0 =
      (n.choose 2:ℝ)*(2:ℕ).factorial * iteratedDeriv i y 0 := by
    rw [iteratedDeriv_mul (by exact contDiffAt_id.pow 2) hy, Finset.sum_eq_single 2]
    · rw [iteratedDeriv_fun_pow_zero,if_pos rfl]
    · intro b _ hb; rw [iteratedDeriv_fun_pow_zero,if_neg hb]; ring
    intro h
    have hh : n < 2 := by simpa only [Finset.mem_range,Nat.lt_succ_iff,not_le] using h
    rw [Nat.choose_eq_zero_of_lt hh]; push_cast; ring
  change Tensor.diagonal (coeff p n 0) x=qRad x * (s*(i.factorial:ℝ)*(Tensor.diagonal (coeff v i 0) x))
  rw [along (hl n),along (ht i)]; simp_rw [zero_add,smul_eq_mul]
  rw [hw.iteratedDeriv_eq,
      show (fun t : ℝ => qRad x * (t^2 * v (t • x)))=qRad x • ((fun t : ℝ => t^2)*(fun t : ℝ => v (t • x))) from rfl,
      iteratedDeriv_const_smul,hr (fun t : ℝ => v (t • x)) hk]
  change (n.factorial:ℝ)⁻¹ * (qRad x * ((n.choose 2:ℝ)*(2:ℕ).factorial*iteratedDeriv i (fun t : ℝ => v (t • x)) 0))= _
  have h : (i.factorial:ℝ)≠0 := by positivity
  unfold s; field_simp
  exact (contDiffAt_id.pow 2).mul hk

/-- One unit of angular clearance: an analytic, harmonic bilocal with the
indicated radial factor has zero germ at the collision. This is why ignoring
all *regular* Wick terms at the collision is enough. -/
theorem dividesToZero {p v : E4 → ℝ} (hp : ContDiffAt ℝ ω p 0) (hv : ContDiffAt ℝ ∞ v 0)
    (he : p =ᶠ[𝓝 0] qRad • v) (hh : lap p =ᶠ[𝓝 0] 0) : p =ᶠ[𝓝 0] 0 := by
  have ha := hp.of_le (show ∞ ≤ ω from le_top)
  have h (n : ℕ) : Tensor.diagonal (coeff p n 0)=0 := by
    obtain ⟨t,ht⟩ := diagonal_taylor ha hv he n
    let q := Tensor.diagonal (coeff v (n-2) 0)
    rw [ht,harmonic_multiple (n-2) (t • q) ((pure_diag _).vScale _) (ht ▸ taylor_lap ha hh n),smul_zero]
  obtain ⟨P,r,H⟩ := hp.analyticAt
  filter_upwards [Metric.eball_mem_nhds _ H.r_pos] with y hy
  have ht := H.hasSum_iteratedFDeriv hy
  have hz (n : ℕ) : (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n p 0 (fun _=> y)=0 := congr_fun (h n) y
  simp_rw [hz,zero_add] at ht
  exact ht.unique hasSum_zero

end YM.RG11.Rigidity
