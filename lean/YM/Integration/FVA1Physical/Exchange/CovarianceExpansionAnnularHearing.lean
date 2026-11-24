import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionAnnularReceipt

/-! Testing the normalized corrected pair only requires one relative raw
crossing price. The true scalar may be arbitrarily small and the cut scalar
may be zero. On small relative mass the gross physical comparison, not a
uniform RMS bound on the connected hard cofactor, pays the branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open scoped Classical
variable (ν W:ℝ)(np:0<ν)(wp:0≤W)
variable (e₀ ea eb eab u v H:ℂ)
variable (q0:‖e₀‖≤W)(qa:‖ea‖≤W)(qb:‖eb‖≤W)(qab:‖eab‖≤W)
variable (physical:((ν:ℂ)-e₀)*((ν:ℂ)*H-(eab-u*eb-v*ea+u*v*e₀))=(ea-u*e₀)*(eb-v*e₀))

include np wp q0 qa qb qab physical in
/-- Numerical price of the signed connected row at the common positive
vacuum if the relative crossing is at most half. No division by a possibly
zero cut mass is used to derive the signed identity. -/
theorem good_crossing_price (good:2*W≤ν):
    ν*‖H‖≤2*W*(1+‖u‖)*(1+‖v‖):=by
  let A:=1+‖u‖
  let B:=1+‖v‖
  let E:=eab-u*eb-v*ea+u*v*e₀
  have an:0≤A:=by dsimp only [A];positivity
  have bn:0≤B:=by dsimp only [B];positivity
  have first (p y:ℂ)(limit:‖y‖≤W):‖y-p*e₀‖≤W*(1+‖p‖):=by
    apply (norm_sub_le ..).trans
    rw [norm_mul]
    nlinarith only [limit,mul_le_mul_of_nonneg_left q0 (norm_nonneg p)]
  have linear:‖E‖≤W*A*B:=by
    have l1:=norm_sub_le eab (u*eb)
    have l2:=norm_sub_le (eab-u*eb) (v*ea)
    have l3:=norm_add_le (eab-u*eb-v*ea) (u*v*e₀)
    simp only [norm_mul] at l1 l2 l3
    dsimp only [E,A,B]
    nlinarith only [l1,l2,l3,qab,mul_le_mul_of_nonneg_left qb (norm_nonneg u),
      mul_le_mul_of_nonneg_left qa (norm_nonneg v),
      mul_le_mul_of_nonneg_left q0 (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
  have vu:‖((ν:ℂ)-e₀)‖≥ν-‖e₀‖:=by
    have f:=norm_sub_norm_le (ν:ℂ) e₀
    simpa only [Complex.norm_real,Real.norm_of_nonneg np.le] using f
  have enough:W≤‖(ν:ℂ)-e₀‖:=by linarith
  have nz:0<‖(ν:ℂ)-e₀‖:=by linarith
  have net:‖(ν:ℂ)*H-E‖≤W*A*B:=by
    apply (le_of_mul_le_mul_left (a:=‖(ν:ℂ)-e₀‖) (b:=‖(ν:ℂ)*H-E‖) (c:=W*A*B) ?_ nz)
    have bound:=mul_le_mul (first u ea qa) (first v eb qb) (norm_nonneg _) (mul_nonneg wp an)
    calc ‖(ν:ℂ)-e₀‖*‖(ν:ℂ)*H-E‖=‖(ea-u*e₀)‖*‖(eb-v*e₀)‖:=by rw [←norm_mul,physical,norm_mul]
         _≤(W*A)*(W*B):=bound
         _≤‖(ν:ℂ)-e₀‖*(W*A*B):=by
           calc _=W*(W*A*B):=by ring
                _≤_:=mul_le_mul_of_nonneg_right enough (mul_nonneg (mul_nonneg wp an) bn)
  have total:=norm_add_le ((ν:ℂ)*H-E) E
  rw [sub_add_cancel,norm_mul,Complex.norm_real,Real.norm_of_nonneg np.le] at total
  change ν*‖H‖≤2*W*A*B
  linarith only [total,net,linear]

include np wp q0 qa qb qab physical in
/-- At every positive original vacuum the complete restored difference can
be charged to its existing regular defect and one unnormalized crossing
wallet. This is an inequality for ν times the discrepancy, not a uniform
unweighted estimate on the incoming field. -/
theorem restored_original_price (δ:ℂ)(M:ℝ)(cap:‖δ‖≤M):
    ν*‖δ‖≤ν*‖δ-H‖+2*W*(M+(1+‖u‖)*(1+‖v‖)):=by
  by_cases good:2*W≤ν
  · have h:=good_crossing_price ν W np wp e₀ ea eb eab u v H q0 qa qb qab physical good
    have f:=norm_add_le (δ-H) H
    rw [sub_add_cancel] at f
    have cost:=mul_le_mul_of_nonneg_left f np.le
    have mn:0≤M:=(norm_nonneg δ).trans cap
    nlinarith only [cost,h,mul_nonneg wp mn]
  have expense:=mul_le_mul (le_of_not_ge good) cap (norm_nonneg _) (by positivity:0≤2*W)
  have pos:0≤2*W*((1+‖u‖)*(1+‖v‖)):=by positivity
  have reg:=mul_nonneg np.le (norm_nonneg (δ-H))
  nlinarith only [expense,pos,reg]

end YM.Integration.FVA1Physical.Exchange.RoseCut
