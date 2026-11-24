import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSingularCut

/-! Normalize the signed cut only after projection onto the same physical
bins. Low or negative retained bin mass spends the *projected signed scalar*
variation. Marked numerical readings can then be normalized on all other
bins with one uniform price and no pointwise inverse-vacuum premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset
open scoped Classical BigOperators

private theorem one_bin (p r M:ℝ)(live:0<p)(stable:p≤2*r)(a b:ℂ)(cap:‖a‖≤M*p):
    p*‖a/(p:ℂ)-b/(r:ℂ)‖≤2*‖a-b‖+2*M*|p-r|:=by
  have rp:0<r:=by linarith only [live,stable]
  have pn:(p:ℂ)≠0:=Complex.ofReal_ne_zero.mpr live.ne'
  have rn:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr rp.ne'
  have ac:‖a/(p:ℂ)‖≤M:=by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg live.le]
    exact (div_le_iff₀ live).mpr cap
  have eq:(r:ℂ)*(a/(p:ℂ)-b/(r:ℂ))=(a-b)+((r-p:ℝ):ℂ)*(a/(p:ℂ)):=by
    rw [Complex.ofReal_sub]
    field_simp [rn,pn]
    ring
  have raw:=norm_add_le (a-b) (((r-p:ℝ):ℂ)*(a/(p:ℂ)))
  rw [←eq,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg rp.le,
    Real.norm_eq_abs,abs_sub_comm r p] at raw
  have sealed:=(raw.trans (add_le_add_right (mul_le_mul_of_nonneg_left ac (abs_nonneg _)) _))
  have scale:=mul_le_mul_of_nonneg_right stable (norm_nonneg (a/(p:ℂ)-b/(r:ℂ)))
  linarith only [scale,sealed]

def clippedBin (p r M:ℝ)(v:ℂ):ℂ:=
  if p≤2*r ∧ ‖v/(r:ℂ)‖≤2*M then v/(r:ℂ) else 0

theorem stable_bin_reading (p r M:ℝ)(np:0≤p)(mp:0≤M)(a b:ℂ)(cap:‖a‖≤M*p):
    ‖clippedBin p r M b‖≤2*M ∧
    p*‖a/(p:ℂ)-clippedBin p r M b‖≤2*‖a-b‖+2*M*|p-r|:=by
  refine ⟨?_,?_⟩
  · unfold clippedBin
    split
    next yes=>exact yes.2
    rw [norm_zero];linarith
  rcases np.eq_or_lt with z|pos
  · rw [←z,zero_mul];positivity
  have amin:‖a/(p:ℂ)‖≤M:=by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg np]
    exact (div_le_iff₀ pos).mpr cap
  by_cases stable:p≤2*r
  · have raw:=one_bin p r M pos stable a b cap
    by_cases within:‖b/(r:ℂ)‖≤2*M
    · simpa only [clippedBin,if_pos (And.intro stable within)] using raw
    have triangle:=norm_sub_norm_le (b/(r:ℂ)) (a/(p:ℂ))
    rw [norm_sub_rev] at triangle
    have lost:‖a/(p:ℂ)‖≤‖a/(p:ℂ)-b/(r:ℂ)‖:=by linarith only [triangle,amin,not_le.mp within]
    rw [clippedBin,if_neg (fun s=>within s.2),sub_zero]
    exact (mul_le_mul_of_nonneg_left lost np).trans raw
  rw [clippedBin,if_neg (fun s=>stable s.1),sub_zero]
  have loss:p≤2*|p-r|:=by linarith only [le_abs_self (p-r),not_le.mp stable]
  have paid:=mul_le_mul loss amin (norm_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
  nlinarith only [paid,norm_nonneg (a-b)]

/-- One small signed-scalar bill buys all cells whose conditional retained
mass is below the chosen fraction of that cell's true positive mass. -/
theorem projected_small_mass {ι:Type*}[Fintype ι](p r:ι→ℝ)(η:ℝ)(ηpos:0<η)
    (fee:ℝ)(scalar:(∑i:ι,|p i-r i|)≤fee):
    (∑i∈univ.filter (fun i=>r i≤(1-η)*p i),p i)≤fee/η:=by
  apply (le_div_iff₀ ηpos).mpr
  rw [Finset.sum_mul]
  apply (Finset.sum_le_sum (g:=fun i=>|p i-r i|) (fun i hi=>?_)).trans
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>abs_nonneg _)).trans scalar
  have q:=(mem_filter.mp hi).2
  linarith only [q,le_abs_self (p i-r i)]

/-- The same cutoff and bins serve every face. A negative cut bin and a zero
bin are admissible; the normalized retained reading falls back to zero there. -/
theorem normalized_bin_transport {ι:Type*}[Fintype ι](p r:ι→ℝ)(P R:ι→ℂ)
    (mass:∀i,0≤p i)(M ε δ:ℝ)(m0:0≤M)(cap:∀i,‖P i‖≤M*p i)
    (scalar:(∑i:ι,|p i-r i|)≤ε)(marked:(∑i:ι,‖P i-R i‖)≤δ):
    (∀i,‖clippedBin (p i) (r i) M (R i)‖≤2*M) ∧
    (∑i:ι,p i*‖P i/(p i:ℂ)-clippedBin (p i) (r i) M (R i)‖)≤2*δ+2*M*ε:=by
  refine ⟨fun i=>(stable_bin_reading (p i) (r i) M (mass i) m0 (P i) (R i) (cap i)).1,?_⟩
  apply (Finset.sum_le_sum (fun i _=>(stable_bin_reading (p i) (r i) M (mass i) m0 (P i) (R i) (cap i)).2)).trans
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left marked (by norm_num)) (mul_le_mul_of_nonneg_left scalar (mul_nonneg (by norm_num) m0))

end YM.Integration.FVA1Physical.Exchange.RoseCut
