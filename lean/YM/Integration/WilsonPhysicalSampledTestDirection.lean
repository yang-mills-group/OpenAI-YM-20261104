import YM.Integration.WilsonPhysicalFullMeshTestJet

/-! A smooth physical test derivative can be read by moving the actual K-born
field on the complete finite lattice, with an order chosen after its gross. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalSampledTestDirection
open Set Finset LocalLTE.Weft WilsonPosteriorProjectionStencil
open WilsonSmoothUnitLatticeDifference (coef)
open WilsonSmoothUnitFiniteGrid
open scoped Classical BigOperators
private theorem expansion (f:ℝ → ℝ)(m:ℕ)(a t s:ℝ)(ht:0<t)
    (smooth:ContDiff ℝ (↑(m+1):WithTop ℕ∞) f):
    (∑i:Fin (m+1),coef f a i.val*s^i.val)=taylorWithinEval f m (Icc a (a+t)) a (a+s):=by
  rw [taylor_within_apply,Fin.sum_univ_eq_sum_range (fun i:ℕ=>coef f a i*s^i)]
  apply sum_congr rfl
  intro i hi
  have degree:i ≤ m+1:=by have:=Finset.mem_range.mp hi;omega
  have sm:ContDiffAt ℝ i f a:=(smooth.of_le (by exact_mod_cast degree)).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith: a<a+t)) sm
    (show a∈Icc a (a+t) from ⟨le_rfl,by linarith⟩)]
  simp only [coef,add_sub_cancel_left,smul_eq_mul]
  ring


/-- All numerical weights are independent of the measured field, the period and the grid phase. -/
theorem original {N:ℕ}[NeZero N](k:ℕ)(j:J k)(left h:ℝ)(pos:0<h)(fit:width k≤N)
    (φ:ℝ → ℝ)(regular:ContDiff ℝ (↑(2*k+1):WithTop ℕ∞) φ)
    (clear:∀y:ℝ,y≤left+(width k:ℝ)*h ∨ left+(N:ℝ)*h≤y → φ y=0)
    (F:ZMod N→ℂ)(mass:ZMod N→ℝ)(nonneg:∀z,0≤ mass z)
    (heads:∀z y,y∈Icc (point left h z) (point left h z+(width k:ℝ)*h) →
      |iteratedDeriv (2*k+1) φ y|≤ mass z):
    let t:ℝ:=(width k:ℝ)*h
    ‖(∑z,(↑(coef φ (point left h z) j.val*t^j.val):ℂ)*F z)-
      ∑z,(φ (point left h z):ℂ)*∑l:J k,(weight k l j:ℂ)*F (z-(offset l:ZMod N))‖≤
      cost k j*t^(2*k+1)*∑z,mass z*‖F z‖:=by
  let t:ℝ:=(width k:ℝ)*h
  have ht:0<t:=mul_pos (by exact_mod_cast Nat.factorial_pos (2*k+1)) pos
  let turns(l:J k):ZMod N ≃ ZMod N:=Equiv.addRight ((offset l):ZMod N)
  let x:=point left h (N:=N)
  have values (z:ZMod N)(l:J k):φ (x z+t*probe k l)=φ (x (turns l z)):=by
    dsimp only [x,t]
    rw [lattice]
    exact reading left h pos φ _ fit clear _ (Nat.div_le_self _ _) z
  have data(z:ZMod N)(l:J k):|∑i:J k,coef φ (x z) i.val*(t*probe k l)^i.val-φ (x (turns l z))|
       ≤ mass z*t^(2*k+1):=by
    let a:=x z
    let s:=t*probe k l
    have hs:0 ≤ s:=mul_nonneg ht.le (probes k l).1.le
    have st:s ≤ t:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left (probes k l).2 ht.le
    have inc:a+s∈Icc a (a+t):=by exact ⟨by linarith,by linarith⟩
    have wage(y:ℝ)(hy:y∈Icc a (a+t)):‖iteratedDerivWithin (2*k+1) φ (Icc a (a+t)) y‖ ≤ mass z:=by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith:a<a+t)) regular.contDiffAt hy]
      exact heads z y hy
    have pay:=taylor_mean_remainder_bound (n:=2*k) (by linarith:a ≤ a+t)
      regular.contDiffOn inc wage
    rw [←values z l,expansion φ (2*k) a t s ht regular,abs_sub_comm]
    have H:1 ≤ ((2*k).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (2*k)
    calc _  ≤  mass z*s^(2*k+1)/(2*k).factorial:=by simpa only [Real.norm_eq_abs,add_sub_cancel_left] using pay
         _  ≤  mass z*s^(2*k+1):=div_le_self (mul_nonneg (nonneg z) (pow_nonneg hs _)) H
         _  ≤  _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs st _) (nonneg z)
  have probed:=WilsonPhysicalFullMeshTestJet.projected k j (fun z i=>coef φ (x z) i.val) t turns
    (fun z=>φ (x z)) F (fun z=>mass z*t^(2*k+1)) data
  have back (z:ZMod N)(l:J k):(turns l).symm z=z-(offset l:ZMod N):=by
    apply (turns l).injective
    rw [Equiv.apply_symm_apply]
    exact (sub_add_cancel ..).symm
  simp_rw [back] at probed
  apply probed.trans_eq
  change cost k j*(∑z,mass z*t^(2*k+1)*‖F z‖)=cost k j*t^(2*k+1)*∑z,mass z*‖F z‖
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  ring
end YM.Integration.WilsonPhysicalSampledTestDirection
