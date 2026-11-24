import YM.IterationFour.Vacuum.Trace
import YM.IterationFour.Series.Root

/-!
# Adjacent coefficient transport inside the SAME marked perturbative plan

A bridge from the actual reclosure estimate (β units) to true coupling
ratio. Use the same α/reset as in that step; no claim of beta evaluation at
orders not printed in the Plan. Series budgets explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function MeasureTheory Filter Currency Polynomial Series
open scoped Topology BigOperators ContDiff
variable {G : Gauge}
lemma price_zone (a : Levels G) (i : ℕ) {v : ℝ} (hv : Real.log ((a.S.block i).val:ℝ) ≤ v * a.S.scale i)
    (hg : G.Simple) (hp : 0≤v) : B a (i+1) ≤ (1+v)*B a i := by
  have ht := mul_le_mul_of_nonneg_left hv (G.slopeConstant_pos hg).le
  have h := mul_nonneg hp a.clock.bar_pos.le
  unfold B Calendar.hatBeta; rw [Schedule.scale_succ]
  unfold Levels.S at *; linarith only [ht,h]
lemma adjacent (a : Levels G) (hg : G.Simple) (v : ℝ) (h : 1 < v) :
    ∀ᶠ i in atTop,B a (i+1)≤v*B a i := by
  let H := a.fits.mesh
  have hp : 0<v-1:= by linarith
  filter_upwards [H.eventually_le_const hp, a.S.divergent.eventually_gt_atTop 0] with i hi he
  change Real.log ((a.S.block i).val:ℝ) / a.S.scale i ≤ _ at hi
  simpa only [add_sub_cancel] using! (price_zone a i ((div_le_iff₀ he).1 hi) hg hp.le)

variable {N q r : ℕ} {C : Family G} (P : Plan C N q r)

def direction (m : ℕ) : Polynomial ℝ := 1 +
    X^2 * ∑ e∈Finset.range (r-2+1), monomial e (P.coefficient m e)

lemma direction_values (m : ℕ) (x : ℝ) : (direction P m).eval x=1+x^2*P.poly m x := by
  unfold direction Plan.poly; rw [eval_add,eval_one,eval_mul, eval_finsetSum, eval_pow, eval_X]
  congr 2
  apply Finset.sum_congr rfl; intro i _; rw [eval_monomial]
lemma direction_head (m : ℕ) : (direction P m).coeff 0=1 := by rw [coeff_zero_eq_eval_zero,direction_values]; ring
lemma direction_cost (m : ℕ) : mass (direction P m) ≤
    1 + ∑ e∈Finset.range (r-2+1), |P.coefficient m e| := by
  apply le_trans (mass_add ..); rw [Series.mass_id]
  refine add_le_add_right ((mass_mul ..).trans ?_) _
  rw [show mass ((X:Polynomial ℝ)^2)=1 by
    rw [show (X:Polynomial ℝ)^2 = Polynomial.C 1 * X^2 by rw [map_one,one_mul], C_mul_X_pow_eq_monomial, prices_monomial, norm_one], one_mul]
  exact (mass_sum ..).trans_eq (Finset.sum_congr rfl fun i _=> prices_monomial ..)

-- Costs through *printed* order

def ratioConstant (Y : Purse) := 8*tiltFee 1*(Y.fare+1)
lemma ratioConstant_nn (Y : Purse) : 0≤ratioConstant Y :=
    mul_nonneg (mul_nonneg (by norm_num) (tiltFee_nonneg _)) (by linarith only [Y.cash])

lemma uses (hg : G.Simple) (hC : C.Makes) (Y : Purse) (m : ℕ) (hm : m<N)
    (he : B C.path.levels (m+1)≤4*B C.path.levels m) (hx : P.predict m∈stripe (B C.path.levels m))
    (h : |P.predict m-C.path.β N q m| ≤ (Y.fare+1)*weight C.path.levels (Y.sigma-2) m) :
    let D := direction P m; let u:= g C N q (m+1)
    |(Real.sqrt (D.eval u))⁻¹ - g C N q m / u| ≤ ratioConstant Y * weight C.path.levels Y.sigma m := by
  intro D u
  let v:= P.predict m; let y:= C.path.β N q (m+1); let x:= C.path.β N q m
  let a := C.path.levels; let b:= B a m
  have h1 := WardBin.hot a m; have h2 := WardBin.hot a (m+1)
  have hv : 0 < v := stripe_pos h1 hx
  have hγ : 0< y:= stripe_pos h2 (actual_band hC N q _ hm)
  have h3 : 0 < u:= g_pos hC _ _ _ hm
  have hd : D.eval u=v/y:= by
    have hh : u^2*y=1:= by
      change (Real.sqrt y)⁻¹^2*y=1; rw [inv_pow,Real.sq_sqrt hγ.le,inv_mul_cancel₀ hγ.ne']
    rw [direction_values]
    apply (eq_div_iff hγ.ne').2
    unfold v Plan.predict; rw [if_neg hm.ne]
    change (1+u^2*P.poly m u)*y=y+P.poly m u
    linear_combination P.poly m u * hh
  have ht : (Real.sqrt (D.eval u))⁻¹ = gain v/u := by
    rw [hd,Real.sqrt_div hv.le]; change _=(Real.sqrt v)⁻¹ / (Real.sqrt y)⁻¹; field_simp
  have hY : hat a m ≤ 8*u:= by
    have hh : B a (m+1) ∈ stripe b :=
      ⟨(by
        apply le_trans _ ((YM.Push.Corrected.Last.band_le a hg) (Nat.le_succ m))
        change B a m/4≤ _; change 0<B a m at h1; linarith), he⟩
    have hl := (sizes_band h1 hh).1
    change hat a m≤ 2*hat a (m+1) at hl
    have hr := (hat_g hC N q (m+1) hm).1
    change hat a (m+1)≤ 2*u at hr
    linarith
  have hh : |gain v - gain x| ≤ (tiltFee 1*b⁻¹) * hat a m * ((Y.fare+1)*weight a (Y.sigma-2) m) := by
    have hl := gain_compare 1 h1 hx (actual_band hC N q m hm.le)
    simp_rw [Real.rpow_one] at hl
    refine hl.trans (mul_le_mul_of_nonneg_left h ?_)
    exact mul_nonneg (mul_nonneg (tiltFee_nonneg _) (inv_nonneg.mpr h1.le)) (WardBin.stepG a m).le
  rw [ht,← sub_div,abs_div,abs_of_pos h3,div_le_iff₀ h3]
  refine hh.trans ?_
  calc
    _ ≤ (tiltFee 1*b⁻¹) * (8*u) * ((Y.fare+1)*weight a (Y.sigma-2) m) := by
         apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY ?_) ?_
         · exact mul_nonneg (tiltFee_nonneg _) (inv_nonneg.mpr h1.le)
         exact mul_nonneg (by linarith only [Y.cash]) (Currency.weight_pos a _ _).le
    _ = _ := by
      unfold ratioConstant
      rw [show weight a (Y.sigma-2) m=b*weight a Y.sigma m from (beta_payment a m Y.sigma).symm]
      have hZ : b ≠ 0 := h1.ne'
      dsimp only [a] at *
      field_simp

/-- Recover the actual g-ratio through the independently calculated adjacent
    reparameterization, to the full order and with all coefficient truncation
    costs explicit. Requires only the stamps on the unmarked side and powers of
    these input coefficients (to be paid separately). -/
theorem radius (hg : G.Simple) (hC : C.Makes) (Y : Purse) (m : ℕ) (hm : m<N) {t : ℕ→Pocket} (ht : P.predict m ∈ stripe (B C.path.levels m))
    {U x} (h : Issued P Y t m x U) (hp : B C.path.levels (m+1)≤4*B C.path.levels m)
    (hj : g C N q (m+1)≤1)
    (hf : (mass (root (direction P m) r)+1) * g C N q (m+1) ≤ 1/2) :
    let u:=g C N q (m+1); let a:= C.path.levels; let p:=root (direction P m) r
    |g C N q m / u - p.eval u| ≤ ratioConstant Y * weight a Y.sigma m +
       128 * mass (Series.equation (direction P m) p) * u^(r+1) := by
   intro u a p
   let b:= C.path.β N q (m+1); let H:=B a m
   have hu: 0<u:=g_pos hC _ _ _ hm
   have he: 0<b:=stripe_pos (WardBin.hot ..) (actual_band hC N q _ hm)
   have hK : 1/64 ≤ (direction P m).eval u := by
     have hz : u^2=b⁻¹:= by change (Real.sqrt b)⁻¹^2=_; rw [inv_pow,Real.sq_sqrt he.le]
     have hv : P.predict m=b+P.poly m u:=by rw [Plan.predict, if_neg hm.ne]
     rw [direction_values,hz]
     have hx: b ≤ 4*B a (m+1):= (actual_band hC N q (m+1) hm).2
     rw [inv_mul_eq_div, show 1+P.poly m u/b=P.predict m / b by rw [hv,add_div,div_self he.ne']]
     apply (le_div_iff₀ he).2
     have hw : H/4 ≤ P.predict m:= ht.1
     unfold H a at hx hw
     linarith only [hw,hx,hp]
   let d :=Real.sqrt ((direction P m).eval u)
   have he': |g C N q m/u-p.eval u| ≤ |g C N q m/u-d⁻¹|+|d⁻¹-p.eval u|:= by exact norm_sub_le_norm_sub_add_norm_sub (g C N q m/u) (d⁻¹) (p.eval u)
   apply he'.trans
   rw [abs_sub_comm (d⁻¹) (p.eval u),abs_sub_comm (g C N q m/u)]
   apply add_le_add
   · exact uses P hg hC Y m hm hp ht h.kinetic
   exact (Series.invoice hu.le hj (direction_head P m) hf (by norm_num : 0<(1/64:ℝ)) hK).trans_eq (by rw [show (2:ℝ)/(1/64)=128 by norm_num])
end YM.IterationFour.Vacuum
