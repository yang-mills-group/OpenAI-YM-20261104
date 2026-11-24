import YM.Integration.FVA1Physical.Wilson.MeasuredSourceClock
import YM.Integration.FVA1Physical.Wilson.SceneSourceClock
import YM.Integration.FVA1Physical.Round2.FieldSharpClock

/-! A spatially uniform price for replacing the true scalar coupling ratio by
the prescribed formal ratio in a marked observable of arbitrary fixed field
degree. The residual is a polynomial, so independent derivative words can be
tested after its full norm has been paid. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG
open MSbar MSbar.Mosaic MSbar.Bristol MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Wave MSbar.Whisk MSbar.Heath.Stock MSbar.Rolling MSbar.CrossH MSbar.Measuring
open scoped Classical Topology BigOperators

private def beltBank (r : ℕ) (D : ℝ) : ℝ :=
  let z := ((r+1 : ℕ) : ℝ)
  4+|z*D|+z*(1+z*D)^r

private theorem beltBank_sup {p r : ℕ} {D : ℝ} (b : PowerSeries ℝ) (hp : p ≤ r)
    (unit : PowerSeries.coeff 0 b = 1) (one : 1 ≤ D) (paid : Bronze.brim r b D) :
    4 ≤ beltBank r D ∧ Belt p b ≤ beltBank r D ∧ Belt p b⁻¹ ≤ beltBank r D ∧
      Belt r b ≤ beltBank r D := by
  let z : ℝ := ((r+1 : ℕ) : ℝ)
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have pos := zero_le_one.trans one
  have alt := Bronze.cold b unit paid one
  have bound (q : ℕ) (H : PowerSeries ℝ) (B : ℝ) (sn : q ≤ r)
      (br : Bronze.brim r H B) (positive : 0 ≤ B) : Belt q H ≤ z*B := by
    apply (sum_le_sum (s:=range (q+1)) (g:=fun _=>B)
      (fun j hj=>br j ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans sn))).trans
    rw [sum_const,nsmul_eq_mul,card_range]
    exact mul_le_mul_of_nonneg_right (by dsimp only [z];exact_mod_cast Nat.succ_le_succ sn) positive
  have rank := mul_nonneg hz (pow_nonneg (show 0 ≤ 1+z*D by positivity) r)
  have core := abs_nonneg (z*D)
  have basic : z*D ≤ beltBank r D :=
    (le_abs_self _).trans (by dsimp only [beltBank]; change _ ≤ 4+|z*D|+z*(1+z*D)^r;linarith only [rank])
  have high : z*(1+z*D)^r ≤ beltBank r D := by
    dsimp only [beltBank]; change _ ≤ 4+|z*D|+z*(1+z*D)^r;linarith only [core]
  refine ⟨?_,(bound p b D hp paid pos).trans basic,
      (bound p b⁻¹ _ hp alt (pow_nonneg (show 0 ≤ 1+z*D by positivity) r)).trans high,
      (bound r b D le_rfl paid pos).trans basic⟩
  change 4 ≤ 4+|z*D|+z*(1+z*D)^r
  linarith only [core,rank]

private theorem scalar_fee_run {A : ℝ → ℝ} (ha : Mosaic.Run atTop id A 0) (m p : ℕ) :
    Mosaic.Run atTop id (fun y=>scalarResetFee m p (A y)) 0 := by
  have hx : Tendsto (id : ℝ→ℝ) atTop atTop := tendsto_id
  unfold scalarResetFee
  apply Mosaic.Run.count hx (range (p+1))
  intro i _
  apply Mosaic.Run.count hx (range (m+1))
  intro d _
  have hd := ha.Ypow hx (d+i)
  have hi := ha.Ypow hx (i+d)
  let jd := hd.mulK hx (d:ℝ)
  let ji := hi.mulK hx (i:ℝ)
  exact ((((jd.addR hx (ji.Ymul hx (ha.Ymul hx ((ha.Ymul hx ha).addR hx ha)))).addR hx hd).addR hx jd).addR hx ji)

private theorem curtain (p : ℕ) {y g : ℝ} (hy : 1 ≤ y) (band : lensT y g) :
    y^(pawn (p+2)) ≤ (2:ℝ)^(p+1)*g^(p+1) := by
  have pos := zero_lt_one.trans_le hy
  have head : cue y = y^(-(1/2:ℝ)) := by rw [Real.rpow_neg pos.le,←Real.sqrt_eq_rpow];rfl
  have gpos : 0 ≤ cue y := (inv_pos.mpr (Real.sqrt_pos.mpr pos)).le
  have lower : cue y ≤ 2*g := by linarith only [(show cue y/2 ≤ g from band.1)]
  rw [←mul_pow]
  calc
    y^(pawn (p+2)) ≤ y^(-(1/2:ℝ)*((p+1:ℕ):ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hy
      unfold pawn; push_cast;linarith only
    _ = (cue y)^(p+1) := by rw [head,←Real.rpow_natCast,←Real.rpow_mul pos.le]
    _ ≤ _ := pow_le_pow_left₀ gpos lower _

theorem measured_source_envelope (s h m p r : ℕ) (hr : p+2 ≤ r) {η : ℝ} (hη : 0 < η) (hp : η < (p:ℝ)+1) :
    ∀ᶠ y : ℝ in atTop, ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (c : Side)
      (l : τ→Site c) (W : Finset (Site c)) (a t u : ℝ) (b : PowerSeries ℝ)
      (T : PowerSeries (Pot τ)), lensT y t → t ≤ 1 → 1/4 ≤ u → u ≤ 4 →
      PowerSeries.coeff 0 b = 1 →
      (∀ j ≤ r, |PowerSeries.coeff j b| ≤ Alto.purse Alto.Dean (hatW y) j) →
      |u-taste r b t| ≤ y^(pawn r) →
      (∀ j ≤ p, Vault l W a s h 0 (PowerSeries.coeff j T) (y^(η/16))) →
      Vault l W a s h 0 (scalarResetRow m p b t u T) (t^((p:ℝ)+1-η)) := by
  let D(y:ℝ) := (hatW y)^(Alto.Dean r)
  let B(y:ℝ) := beltBank r (D y)
  let C : ℝ := (2:ℝ)^(p+1)+1
  let F(y:ℝ) := scalarResetFee m p (B y)*(C+2*B y)
  let z := ((r+1 : ℕ) : ℝ)
  have hx : Tendsto (id : ℝ→ℝ) atTop atTop := tendsto_id
  have cost : Mosaic.Run atTop id D 0 := (Mosaic.Run.stanza hx).Ypow hx _
  have jd := cost.mulK hx z
  have bb : Mosaic.Run atTop id B 0 := ((Mosaic.Run.token hx 4).addR hx (jd.absA hx)).addR hx
    ((((Mosaic.Run.token hx 1).addR hx jd).Ypow hx r).mulK hx z)
  have fee : Mosaic.Run atTop id F 0 := (scalar_fee_run bb m p).Ymul hx ((Mosaic.Run.token hx C).addR hx (bb.mulK hx 2))
  have small : 0 < η/16 := by positivity
  filter_upwards [fee _ small,Alto.broad.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ),
    Round2.Curvature.field_sharp_clock p 0 le_rfl hη hp] with y balance wide hy sharp
  change |F y| ≤ y^(η/16) at balance
  intro τ _ _ c l W a t u b T band ht lo hi unit bill error inp
  have pos := zero_lt_one.trans_le hy
  have t₀ := (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr pos))).trans_le band.1
  have u₀ : 0 < u := lt_of_lt_of_le (by norm_num) lo
  have pay : Bronze.brim r b (D y) :=
    fun j hj=>(bill j hj).trans (pow_le_pow_right₀ wide (Alto.ranked hj))
  obtain ⟨four,bp,bi,br⟩ := beltBank_sup b (show p ≤ r by omega) unit (one_le_pow₀ wide) pay
  have b0 : 0 ≤ B y := (by norm_num : (0:ℝ)≤4).trans four
  have iu : u⁻¹ ≤ 4 := (inv_anti₀ (by norm_num : (0:ℝ) < 1/4) lo).trans_eq (by norm_num)
  have envelope := scalar_reset_vault l W s h m p b T unit t₀.le ht u₀
    ((abs_of_pos u₀).le.trans (hi.trans four)) (iu.trans four) ((by norm_num : (1:ℝ)≤4).trans four) bp bi inp
  have cut := Bristol.remainderM br (show p ≤ r by omega) t₀.le ht
  have energy : y^(pawn r) ≤ y^(pawn (p+2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hy
    have back : ((p+2 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    unfold pawn;linarith only [back]
  have err := (abs_sub_le u (taste r b t) (taste p b t)).trans (add_le_add
    (error.trans (energy.trans (curtain p hy band))) cut)
  have fee0 : 0 ≤ scalarResetFee m p (B y) := by unfold scalarResetFee tonK;positivity
  have shot : |u-taste p b t|+(B y+1)*t^(p+1) ≤ (C+2*B y)*t^(p+1) := by
    dsimp only [C];nlinarith only [err]
  apply Quote.widen envelope _ le_rfl
  calc
    scalarResetFee m p (B y)*((|u-taste p b t|+(B y+1)*t^(p+1))*y^(η/16)) ≤
        F y*t^(p+1)*y^(η/16) := by
            unfold F
            exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right shot
              (Real.rpow_nonneg pos.le _)) fee0).trans_eq (by ring)
    _ ≤ t^(p+1)*(y^(η/16)*y^(η/16)) := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans balance)
        (pow_nonneg t₀.le _)) (Real.rpow_nonneg pos.le _)).trans_eq (by ring)
    _ ≤ _ := by
      rw [←Real.rpow_add pos,show η/16+η/16=η/8 by ring]
      have S := sharp t band
      have f₀ : 0 ≤ y^(pawn (p+2)) := Real.rpow_nonneg pos.le _
      have v₀ : 0 ≤ t^(p+1)*y^(η/8) := by positivity
      linarith only [S,f₀,v₀]
end YM.Integration.FVA1Physical.Wilson
