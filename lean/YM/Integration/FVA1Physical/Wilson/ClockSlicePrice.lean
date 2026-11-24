import YM.Integration.FVA1Physical.Wilson.WickCubeLaw

/-! The published unit-clock painter controls its complete homogeneous jet on
the joint clock-field cube. The finite interpolation grid only probes fields
in the very same unit ball and its charge is independent of volume. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Valence FVA1Physical.Round2
open scoped Classical ContDiff BigOperators
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def clockRent (k:ℕ):ℝ:=(∑i:Fin (k+1),(2:ℝ)^i.val*gridPrice k i)*2^k

private theorem shifted_grid {k:ℕ} {u v:ℝ→ℂ} (hu:Level (k:ℤ) u) (hv:Level (k:ℤ) v)
    {δ:ℝ} (grid:∀j,‖u (unitGrid k j)-v (unitGrid k j)‖≤δ) {s:ℝ} (hs:|s|≤2):
    ‖u s-v s‖≤(∑i:Fin (k+1),(2:ℝ)^i.val*gridPrice k i)*δ:=by
  have expand (h:ℝ→ℂ) (hh:Level (k:ℤ) h):h s=∑ i : Fin (k+1),s^i.val • jet h i.val 1:=by
    rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>s^i • jet h i 1),hh.posted]
    apply sum_congr rfl;intro i _
    simpa only [smul_eq_mul,mul_one] using Clipper.weight (1:ℝ) s i h
  rw [expand u hu,expand v hv,←sum_sub_distrib,sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro i _
  have price:=grid_jet_error hu hv (1:ℝ) i (fun j=>by simpa only [smul_eq_mul,mul_one] using grid j)
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_pow,mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hs _) price (norm_nonneg _) (by positivity)

theorem unit_clock_cube {a b:ℝ×X→ℂ} (sa:ContDiffAt ℝ ω a 0) (sb:ContDiffAt ℝ ω b 0)
    (k:ℕ) {δ:ℝ} (slice:∀u:X,‖u‖≤1→‖jet a k (1,u)-jet b k (1,u)‖≤δ)
    (v:ℝ×X) (bound:‖v‖≤1):
    ‖jet a k v-jet b k v‖≤clockRent k*δ:=by
  let L:ℝ→L[ℝ]ℝ×X:=ContinuousLinearMap.inl ℝ ℝ X
  let U:=fun s:ℝ=>jet a k ((1,v.2)+L s)
  let V:=fun s:ℝ=>jet b k ((1,v.2)+L s)
  have hu:=SignCovariance.affine_degree (1,v.2) L (Adjacent.levelJet sa k)
  have hv:=SignCovariance.affine_degree (1,v.2) L (Adjacent.levelJet sb k)
  have grid(j:Fin (k+1)):‖U (unitGrid k j)-V (unitGrid k j)‖≤2^k*δ:=by
    let t:=1+unitGrid k j
    have hi:=unitGrid_mem k j
    have one:1≤t:=by dsimp [t];linarith [hi.1]
    have two:t≤2:=by dsimp [t];linarith [hi.2]
    have nz:t≠0:=ne_of_gt (zero_lt_one.trans_le one)
    have eq:((1,v.2)+L (unitGrid k j))=t • ((1:ℝ),t⁻¹ • v.2):=by
      apply Prod.ext
      · change 1+unitGrid k j=t*1;rw [mul_one]
      change v.2+0=t • (t⁻¹ • v.2)
      rw [add_zero,smul_smul,mul_inv_cancel₀ nz,one_smul]
    have normIn:‖t⁻¹ • v.2‖≤1:=by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans one))]
      exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ one)).trans ((norm_snd_le v).trans bound)
    change ‖jet a k _-jet b k _‖≤_
    rw [eq,Clipper.weight,Clipper.weight,←smul_sub,norm_smul,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans one) _)]
    exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans one) two _) (slice _ normIn) (norm_nonneg _) (by positivity)
  have htime:|v.1-1|≤2:=(abs_sub v.1 1).trans (by rw [abs_one];have hx:|v.1|≤1:=(norm_fst_le v).trans bound;linarith)
  have estimate:=shifted_grid hu hv grid htime
  have center:((1,v.2)+L (v.1-1))=v:=by
    apply Prod.ext
    · change 1+(v.1-1)=v.1;ring
    change v.2+0=v.2;rw [add_zero]
  change ‖jet a k _-jet b k _‖≤_ at estimate
  rw [center] at estimate
  exact estimate.trans_eq (by unfold clockRent;ring)

end YM.Integration.FVA1Physical.Wilson
