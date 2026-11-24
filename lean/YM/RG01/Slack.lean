import YM.RG01.Seed

/-! # Coupling-uniform and seed/divisor-slack consequences.
Expansion parameter in these estimates is actual incoming `g=gap β`. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Physical
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Input Time Org Supply
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Greenbelt Match Song
open Roof Roost ThroughLaunch Progress.DirectedRecipe Stock Opera PriceCompiler Pressure.Testing Clock Instrument
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (hG : G.Simple) (A : Levels G)

include hG
lemma hats : Tendsto A.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma nextHat : ∀ᶠ m in atTop, A.clock.hatBeta (m+1) ≤ 2*A.clock.hatBeta m := by
  filter_upwards [A.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    A.S.divergent.eventually_gt_atTop 0] with i hi he
    -- Grows.walls argument with result on hatBeta itself
  have hS : Real.log (A.S.block i).val ≤ A.S.scale i := by
    have hh : Real.log (A.S.block i).val / A.S.scale i ≤ 1 := hi
    simpa using (div_le_iff₀ he).mp hh
  have hg := Gauge.slopeConstant_pos hG
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]; unfold Levels.S at hS; nlinarith only [A.clock.bar_pos, mul_le_mul_of_nonneg_left hS hg.le]
/-- Any fixed powers even with divisor; using elementary weaker bounds beta^k
and coarse vs fine comparison for simplicity. -/
lemma shrink (K : ℕ) : Tendsto (fun m:ℕ => (A.clock.hatBeta m)^K * A.clock.forcedAllowance m) atTop (𝓝 0) := by
  let f m:=A.clock.hatBeta m
  have he:= (Clock.burnt (-((2*K:ℕ):ℝ)) 1 2 ((1:ℝ)/5) (by norm_num) (by norm_num) (by norm_num)).comp (hats hG A)
  refine he.congr fun m=>?_ 
  have h0 : 0 < f m:= zero_lt_one.trans (A.fits.delayed _)
  -- rpow to powers
  dsimp only [Function.comp_apply]
  rw [Real.rpow_neg (Clock.gp h0).le,Real.rpow_natCast]
  unfold Calendar.forcedAllowance
  rw [Clock.watch_two, neg_one_mul] 
  change ((Real.sqrt (f m))⁻¹ ^ (2*K))⁻¹ * Real.exp _ = _
  rw [inv_pow,inv_inv,pow_mul,Real.sq_sqrt h0.le]
  rfl

lemma hard_slack (K : ℕ) :
    ∀ᶠ m in atTop, (A.clock.hatBeta (m+1))^K*A.clock.forcedAllowance m ≤ (1/4:ℝ)^K := by
  have hb:= (shrink hG A K).eventually (ge_mem_nhds (pow_pos (by norm_num : (0:ℝ)<1/8) K))
  filter_upwards [nextHat hG A,hb] with m hm hb
  have he : 0≤ A.clock.hatBeta (m+1):=(zero_lt_one.trans (A.fits.delayed _)).le
  have hh :0≤ A.clock.forcedAllowance m := (Real.exp_pos _).le
  calc
    _ ≤ (2*A.clock.hatBeta m)^K*A.clock.forcedAllowance m := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he hm _) hh
    _ = (2:ℝ)^K*((A.clock.hatBeta m)^K*A.clock.forcedAllowance m) := by rw [mul_pow,mul_assoc]
    _ ≤ (2:ℝ)^K*((1/8:ℝ)^K):=mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _:= by rw [←mul_pow]; norm_num

omit hG A in
lemma gap_below (x : ℝ) (hx : 1 ≤ x) : x⁻¹ ≤ Clock.gap x := by
  have he : (Real.sqrt x)^2=x:=Real.sq_sqrt (le_trans zero_le_one hx)
  have h := zero_lt_one.trans_le hx
  exact inv_anti₀ (Real.sqrt_pos.mpr h) ((Real.sqrt_le_left h.le).mpr (le_self_pow₀ hx (by omega : (2:ℕ)≠0)))

omit hG in
lemma gaps (m : ℕ) (β : ℝ) (hβ : β ∈ band A (m+1)) :
    let x:= A.clock.hatBeta (m+1); 0<Clock.gap β ∧ (2*x)⁻¹ ≤ Clock.gap β:= by
  intro x
  have he:=A.fits.delayed (m+1); change 1<x at he
  change x/2 ≤ β ∧ β ≤ 2*x at hβ
  have hp : 0<β := lt_of_lt_of_le (by positivity) hβ.1
  exact ⟨Clock.gp hp,(gap_below (2*x) (by linarith)).trans (inv_anti₀ (Real.sqrt_pos.mpr hp)
    (Real.sqrt_le_sqrt hβ.2))⟩

/-- sqrt(w) divided output. Uniform in actual β; w at COARSE scale. -/
lemma divided_slack (K : ℕ) : ∀ᶠ m in atTop, ∀ β ∈ band A (m+1),
    A.clock.forcedAllowance m ≤ Real.sqrt (A.clock.forcedAllowance m)*(Clock.gap β)^K := by
  filter_upwards [hard_slack hG A (2*K)] with m h β hβ
  let x:= A.clock.hatBeta (m+1)
  have hx:0<x:=zero_lt_one.trans (A.fits.delayed _)
  let w:=A.clock.forcedAllowance m
  have hw:0<w:=Real.exp_pos _
  change x^(2*K)*w ≤ (1/4:ℝ)^(2*K) at h
  obtain ⟨hf,hT⟩:= gaps A m β hβ
  change w ≤ Real.sqrt w * _
  have h0:w≤ ((Clock.gap β)^K)^2:= by
    have hv:w ≤ ((1/(4*x))^(2*K)):= by
      rw [one_div,inv_pow,mul_pow,mul_inv]; field_simp; rw [div_pow,one_pow] at h; field_simp at h; linarith only [h]
    apply hv.trans
    rw [Nat.mul_comm 2 K,pow_mul]
    apply pow_le_pow_left₀ (by positivity) _
    exact pow_le_pow_left₀ (by positivity) ((show 1/(4*x)≤ (2*x)⁻¹ by rw [one_div]; apply inv_anti₀ (by positivity); linarith).trans hT) _
  calc
    w = Real.sqrt w*Real.sqrt w := by rw [←pow_two,Real.sq_sqrt hw.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [Real.sqrt_le_left (by positivity)]; exact h0) (Real.sqrt_nonneg _)

section Purchased
variable {M : Metals G} {D:Rolls M.p} {B : Alloy M D} (X : Factor B)

/-- Export to `Cull`: the missing higher grades in the seed-height gate are
available simultaneously with all the existing gates at fixed demand, on the
same levels. -/
lemma seed_slack (K : ℕ) : ∀ᶠ m in atTop,
    let i:= B.B.a.clock.J m; let j:= B.B.a.clock.J (m+1)
    let x:= B.B.a.clock.hatBeta m
    (grow G (D.L j) x)^K ≤ Real.exp ((X.target j i).mark (D.L j) (X.shape.μ j i) x) := by
  let Lv := B.B.a
  filter_upwards [hard_slack hG Lv (K+1)] with m h
  intro i j x
  let y:= Lv.clock.hatBeta (m+1)
  have he:1<y:=Lv.fits.delayed (m+1)
  have hy:0<y:=zero_lt_one.trans he
  change y^(K+1)*Lv.clock.forcedAllowance m ≤ (1/4:ℝ)^(K+1) at h
  let a:=(X.target j i).mark (D.L j) (X.shape.μ j i) x
  have hη:y⁻¹ * Real.exp (-a) ≤ Lv.clock.forcedAllowance m:= obliged X y (m:=m) ⟨by change y/2 ≤ y; linarith,by change y≤ 2*y; linarith⟩
  have hq: y^K * Real.exp (-a) ≤ 1:= by
    calc
      y^K* Real.exp (-a)= y^(K+1)*(y⁻¹*Real.exp (-a)):= by rw [pow_succ,mul_assoc,mul_inv_cancel_left₀ hy.ne']
      _ ≤ _:= (mul_le_mul_of_nonneg_left hη (by positivity)).trans (h.trans (pow_le_one₀ (by norm_num) (by norm_num)))
  have hz:=hq
  rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),one_mul] at hz
  apply (pow_le_pow_left₀ ?_ (b:=y) ?_ K).trans hz
  · unfold grow; rw [← PriceCompiler.beta_eq B.B.valid]; exact Real.rpow_nonneg hy.le _
  unfold grow; rw [← PriceCompiler.beta_eq B.B.valid,show y=y^(1:ℝ) by rw [Real.rpow_one]] -- repeated y
  exact Real.rpow_le_rpow_of_exponent_le he.le (by norm_num)

omit hG in
lemma forecast_le (m : ℕ) : forecastE A m ≤ 1 := by -- replace
  have h:= (Time.authorized G (A.params m)).1
  have hl := A.fits.delayed m
  unfold forecastE
  have he: 0 ≤ credit G (A.params m):=(Time.credit_pos ..).le
  apply le_trans (b:=credit G (A.params m)) (mul_le_of_le_one_right he ?_) (by linarith)
  unfold Calendar.allowance Calendar.hatCoupling
  exact Real.rpow_le_one (by positivity) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hl.le)) (by norm_num)

omit hG in
/-- Spend four internal occurrence orders per requested order (actually much
fewer suffice). Actual β remains positive throughout. -/
lemma occurrence_cost (m R : ℕ) (β:ℝ) (hβ:β∈band B.B.a (m+1))
    (hy : 4 ≤ B.B.a.clock.hatBeta (m+1)) :
    let j:= B.B.a.clock.J (m+1)
    let x:= B.B.a.clock.hatBeta m; let y:=grow G (D.L j) x
    (y^3 / y^(3+4*(R+1)))*forecastE B.B.a m ≤ Clock.gap β ^ (R+1) := by
  intro j x y
  let z:= B.B.a.clock.hatBeta (m+1)
  change 4 ≤ z at hy
  have hz : 1 ≤ z:= le_trans (by norm_num) hy
  have hx : y=z^(3/8:ℝ):=by unfold y grow j x; rw [← PriceCompiler.beta_eq B.B.valid]
  have hY : 0<y := hx ▸ Real.rpow_pos_of_pos (by linarith) _
  have ht : 0 < z := by linarith
  have hw : 2 ≤ z^((1/2):ℝ) := by
    rw [← Real.sqrt_eq_rpow]; rw [Real.le_sqrt (by norm_num) ht.le]; linarith
  have hp : 2*z ≤ y^(4:ℕ) := by
    rw [hx,← Real.rpow_natCast,← Real.rpow_mul ht.le, Nat.cast_ofNat,
      show (3/8:ℝ)*4=1/2+1 by norm_num,Real.rpow_add ht,Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hw ht.le
  have hf : (y^(4:ℕ))⁻¹ ≤ Clock.gap β := (inv_anti₀ (show (0:ℝ)<2*z by positivity) hp).trans (gaps B.B.a m β hβ).2
  calc
    _ ≤ y^3 / y^(3+4*(R+1)) := mul_le_of_le_one_right (by positivity) (forecast_le (A:=B.B.a) m)
    _ = ((y^(4:ℕ))⁻¹)^(R+1):= by rw [pow_add,pow_mul,inv_pow]; field_simp
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hf _

end Purchased
end YM.RG01.Physical
