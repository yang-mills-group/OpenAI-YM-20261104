import YM.Integration.ActualRunRatioGrowth
import YM.FullVolume.Cross

/-! A fixed native source frame determines beforehand the extra Taylor
degrees that pay its actual fine threshold and the entire block-volume factor.
No uniform cap on the terminal coefficient vector is silently inserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetOrderPayment
open Filter Finset Lattice Labels RG PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

def order {d:ℕ} (F:Frame G d):ℕ := Finset.univ.sup (fun i:F.Index=>(F.grades i).2)

private theorem amplitude {d:ℕ} (F:Frame G d) (v:F.Coeff) {g θ:ℝ} (hg:0<g)
    (small:g ≤ 1) (hθ:0<θ) (gain:g ≤ 2*θ) :
    (∑i,‖F.scaled θ⁻¹ v i‖)*g^order F ≤ 2^order F*(∑i,‖v i‖) :=by
  classical
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let h:=(F.grades i).2
  have bound:h ≤ order F:=Finset.le_sup (f:=fun a:F.Index=>(F.grades a).2) (Finset.mem_univ i)
  have a:0 ≤ θ⁻¹*g := mul_nonneg (inv_nonneg.mpr hθ.le) hg.le
  have b:θ⁻¹*g ≤ 2:=by
    rw [←div_eq_inv_mul,(div_le_iff₀ hθ)];linarith
  have w:0 ≤ θ⁻¹^h:=pow_nonneg (inv_nonneg.mpr hθ.le) _
  rw [F.scaled_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg w]
  calc
    θ⁻¹^h*‖v i‖*g^order F ≤ θ⁻¹^h*‖v i‖*g^h :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le small bound) (mul_nonneg w (norm_nonneg _))
    _ = (θ⁻¹*g)^h*‖v i‖:=by rw [mul_pow];ring
    _ ≤ 2^order F*‖v i‖:=by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (pow_le_pow_left₀ a b h).trans (pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) bound)

theorem paid (R:Run G) (hG:G.Simple) (d:ℕ) :
    let F:=R.family.labels.level d
    ∀ᶠ m:ℕ in atTop, ∀ N p, m<N → ∀ (v:F.Coeff) (k:ℕ),
      let g:=Next.SectorChange.coupling (R.family.path.β N p (m+1))
      let θ:=R.family.path.levels.clock.threshold (m+1)
      4*((R.family.S.block m).val:ℝ)^d*(∑i,‖F.scaled θ⁻¹ v i‖)*g^(k+order F+1) ≤
        (∑i,‖v i‖)*g^k :=by
  let F:=R.family.labels.level d
  let h:=order F
  have block:=ActualRunRatioGrowth.actual_payment R hG d (4*2^h) 1 (by positivity) zero_lt_one
  have small:∀ᶠ t:ℕ in atTop, ∀ N p, t+1≤N → IterationFour.Currency.g R.family N p (t+1)<1:=
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)
  filter_upwards [block,small] with m E one N p hm v k
  let g:=Next.SectorChange.coupling (R.family.path.β N p (m+1))
  let θ:=R.family.path.levels.clock.threshold (m+1)
  let B:=((R.family.S.block m).val:ℝ)^d
  let H:=R.family.path.levels.clock.hatCoupling (m+1)
  have hg:0<g:=IterationFour.Currency.g_pos R.makes N p (m+1) hm
  have hat:g≤2*H:=(IterationFour.Currency.hat_g R.makes N p (m+1) hm).2
  have hH:0<H:=by linarith
  have mon:1 ≤ R.family.path.levels.clock.monitor (m+1):=Real.one_le_exp (sq_nonneg _)
  have th:H ≤ θ:=le_mul_of_one_le_right hH.le mon
  have eff:=amplitude F v hg (one N p hm).le (hH.trans_le th) (hat.trans (by linarith))
  have bx:=E N p hm
  change 4*2^h*B ≤ g^(-(1:ℝ)) at bx
  rw [Real.rpow_neg_one,←one_div,(le_div_iff₀ hg)] at bx
  let X:=∑i,‖F.scaled θ⁻¹ v i‖
  let Y:=∑i,‖v i‖
  have hB:0≤B:=by dsimp [B]; positivity
  have hY:0≤Y:=Finset.sum_nonneg fun i _=>norm_nonneg _
  change X*g^h ≤ 2^h*Y at eff
  change 4*B*X*g^(k+h+1)≤Y*g^k
  calc
    4*B*X*g^(k+h+1)=(4*B*g*g^k)*(X*g^h):=by rw [pow_add,pow_add];ring
    _ ≤ (4*B*g*g^k)*(2^h*Y):=mul_le_mul_of_nonneg_left eff (by positivity)
    _ = (4*2^h*B*g)*(Y*g^k):=by ring
    _ ≤ 1*(Y*g^k):=mul_le_mul_of_nonneg_right bx (mul_nonneg hY (pow_nonneg hg.le _))
    _ = Y*g^k:=one_mul _

end YM.Integration.WilsonOffsetOrderPayment
