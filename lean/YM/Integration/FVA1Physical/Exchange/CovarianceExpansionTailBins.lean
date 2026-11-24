import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionStableBins

/-! A gross pointwise cap on the original field is unnecessary after
projection onto the physical test bins. A true joint second moment pays
the upper tail of the genuine bin reading, with period-independent scalar
and marked variation constants and an explicitly chosen cutoff M. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory
open scoped Classical BigOperators

private theorem tail_one (p r M:ℝ)(nn:0≤p)(mp:0<M)(a b:ℂ):
    p*‖a/(p:ℂ)-clippedBin p r M b‖≤(2*‖a-b‖+2*M*|p-r|)+(3/M)*(p*‖a/(p:ℂ)‖^2):=by
  rcases nn.eq_or_lt with z|pos
  · rw [←z,zero_mul,zero_mul,mul_zero,add_zero];positivity
  let u:=a/(p:ℂ);let v:=clippedBin p r M b
  have unit:p*‖u‖=‖a‖:=by
    dsimp only [u]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg pos.le,mul_comm,div_mul_cancel₀ _ pos.ne']
  by_cases cap:‖a‖≤M*p
  · exact ((stable_bin_reading p r M pos.le mp.le a b cap).2).trans
      (le_add_of_nonneg_right (mul_nonneg (div_nonneg (by norm_num) mp.le) (mul_nonneg pos.le (sq_nonneg _))))
  have excess:M≤‖u‖:=by
    apply le_of_mul_le_mul_left (a:=p) (b:=M) _ pos
    rw [mul_comm p M,unit]
    exact le_of_not_ge cap
  have blank:‖(0:ℂ)‖≤M*p:=by rw [norm_zero];positivity
  have bv: p*‖v‖≤2*‖b‖+2*M*|p-r|:=by
    simpa only [v,zero_div,zero_sub,norm_neg] using (stable_bin_reading p r M pos.le mp.le 0 b blank).2
  have dist:=norm_sub_le u v
  have along:=norm_sub_le a (a-b)
  rw [sub_sub_cancel] at along
  have overflow:3*‖a‖≤(3/M)*(p*‖u‖^2):=by
    rw [←unit]
    apply (le_of_mul_le_mul_left (a:=M) (b:=3*(p*‖u‖)) ?_ mp)
    rw [←mul_assoc M (3/M) (p*‖u‖^2),mul_comm M (3/M),div_mul_cancel₀ _ mp.ne']
    nlinarith only [mul_nonneg (mul_nonneg pos.le (norm_nonneg u)) (sub_nonneg.mpr excess)]
  have gross:=mul_le_mul_of_nonneg_left dist pos.le
  rw [mul_add,unit] at gross
  change p*‖u-v‖≤(2*‖a-b‖+2*M*|p-r|)+(3/M)*(p*‖u‖^2)
  linarith only [gross,bv,along,overflow]

/-- Individual conditional readings can be unbounded. Choosing M after
fixing the signed variations only requires a true RMS on the received
observable, and never a second moment of the reciprocal vacuum. -/
theorem normalized_bin_square_transport {ι:Type*}[Fintype ι](p r:ι→ℝ)(a b:ι→ℂ)
    (mass:∀i,0≤p i)(M ε δ K:ℝ)(mp:0<M)
    (scalar:(∑i:ι,|p i-r i|)≤ε)(marked:(∑i:ι,‖a i-b i‖)≤δ)
    (square:(∑i:ι,p i*‖a i/(p i:ℂ)‖^2)≤K):
    (∑i:ι,p i*‖a i/(p i:ℂ)-clippedBin (p i) (r i) M (b i)‖)≤(2*δ+2*M*ε)+(3/M)*K:=by
  apply (Finset.sum_le_sum (fun i _=>tail_one (p i) (r i) M (mass i) mp (a i) (b i))).trans
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left marked (by norm_num))
    (mul_le_mul_of_nonneg_left scalar (mul_nonneg (by norm_num) mp.le)))
    (mul_le_mul_of_nonneg_left square (div_nonneg (by norm_num) mp.le))

end YM.Integration.FVA1Physical.Exchange.RoseCut
