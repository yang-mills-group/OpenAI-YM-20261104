import YM.Integration.WilsonCapturedPrimaryPanel
import YM.Integration.WilsonCapturedPrimaryPotential
import YM.Integration.WilsonFirstReceivedRadialRoom

/-! Pay the true cover collar on the original reporting schedule before
the period and finer cutoff are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCourse
open Function Filter Finset Set Labels Lattice Wilson RG PhysicalNext.Repeat.Legato
open Pert.Asymptotics Next.Rank.Perch
open WilsonCapturedPrimaryCollar WilsonFirstReceivedRadialStencil
open scoped Classical Topology

private theorem cover (P : BudgetPoint) {g s : ℝ} (hg : 0<g) (h1 : g≤1)
    (hs : 1 ≤ s) (support : 1≤P.supportExponent) (cost : -Real.log g ≤ s) (T : ℕ) :
    1+(radius P (cutoff P g T):ℝ) ≤ 9*((T:ℝ)+1)*s*(P.B:ℝ)^2 := by
  let a : ℝ := ((T:ℝ)+1)*s
  let b : ℝ := P.B
  have ha : 1≤a := one_le_mul_of_one_le_of_one_le (by linarith only [Nat.cast_nonneg (α:=ℝ) T]) hs
  have hb : 1≤b := by change (1:ℝ)≤(P.B:ℝ);exact_mod_cast P.B_pos
  have nm : 0≤ -Real.log (g^T) := neg_nonneg.mpr (Real.log_nonpos
    (pow_nonneg hg.le _) (pow_le_one₀ hg.le h1))
  have k : (cutoff P g T:ℝ)≤a := by
    have kceil := (Nat.ceil_lt_add_one (div_nonneg nm P.exponent_pos.le)).le
    have le := div_le_self nm support
    rw [Real.log_pow] at le kceil
    have scale := mul_le_mul_of_nonneg_left cost (Nat.cast_nonneg (α:=ℝ) T)
    change (Nat.ceil (-Real.log (g^T)/P.supportExponent):ℝ) ≤ ((T:ℝ)+1)*s
    rw [Real.log_pow]
    linarith only [kceil,le,scale,hs]
  have c := mul_le_mul k (show 4*b+2 ≤ 6*b by linarith only [hb]) (by linarith only [hb])
    (zero_le_one.trans ha)
  have bill := mul_le_mul_of_nonneg_right ha (zero_le_one.trans hb)
  have bill' : b≤b^2 := by nlinarith only [mul_nonneg (zero_le_one.trans hb) (sub_nonneg.mpr hb)]
  unfold radius
  push_cast
  calc
    _ ≤ 9*a*b := by dsimp only [b] at *;nlinarith only [c,bill,hb]
    _ ≤ 9*((T:ℝ)+1)*s*(P.B:ℝ)^2 := by
      rw [show 9*((T:ℝ)+1)*s=9*a by unfold a;ring]
      exact mul_le_mul_of_nonneg_left bill' (by linarith only [ha])

private theorem nodeFee (D : ℕ) : 1≤budget D := by
  simpa only [Polynomial.eval_one,norm_one,abs_zero,add_zero,one_pow,one_mul,mul_one] using
    (priced (1:Polynomial ℂ) (d:=D) (by simp) (A:=1) (fun _ _ => by simp) 0)

/-- Any fixed collar grade and any fixed polynomial in its length cost an
arbitrarily small multiple of one inverse coupling power. -/
theorem original {G : Gauge} (R : Run G) (simple : G.Simple) (T l : ℕ)
    {C ε : ℝ} (cc : 0≤C) (ep : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i+1≤N →
      let P := R.family.path.levels.budget i
      let g := regulatorRun R.family N per (i+1)
      let r := radius P (cutoff P g T)
      1≤P.supportExponent →
      0<g ∧ g≤1/2 ∧ g≤2*P.threshold ∧ P.threshold*(1+(r:ℝ))^2≤1 ∧
      C*g*(1+(r:ℝ))^l ≤ ε := by
  let V := R.family.path.levels
  let D := max 3 l
  let H : ℝ := 20*((T:ℝ)+1)
  let δ := min 1 (ε/(1+C))
  have hp : 0<H := by unfold H; positivity
  have dp : 0<δ := lt_min zero_lt_one (div_pos ep (by linarith))
  have grows := RG01.Physical.hats simple V
  filter_upwards [RG01.Physical.nextHat simple V,grows.eventually_ge_atTop 8,
    (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop 1,
    WilsonFirstReceivedRadialRoom.original R simple D 1 H dp] with i near large logb nodes
  intro N per hi P g r support
  let X := V.clock.hatBeta i
  let b := R.family.path.β N per (i+1)
  have upperDate := ActualCoarseStagePrice.hatBeta_mono V simple (Nat.le_succ i)
  have band := (R.makes.wilson.represents N per (i+1) hi).band
  change V.clock.hatBeta (i+1)/2 ≤ b ∧ b≤2*V.clock.hatBeta (i+1) at band
  have low : 4≤b := by change 8≤X at large; linarith only [large,upperDate,band.1]
  have xp : 0<X := by change 8≤X at large; linarith only [large]
  have bp : 0<b := by linarith only [low]
  have rp : 0<Real.sqrt b := Real.sqrt_pos.mpr bp
  have gp : 0<g := inv_pos.mpr rp
  have ghalf : g≤1/2 := by
    change (Real.sqrt b)⁻¹ ≤ 1/(2:ℝ)
    rw [one_div]
    apply (inv_le_inv₀ rp (by norm_num : 0<(2:ℝ))).2
    exact (Real.le_sqrt (by norm_num) bp.le).2 (by linarith only [low])
  have top : Real.sqrt b ≤ X :=
    (Real.sqrt_le_iff).2 ⟨xp.le,by
      have bx : b≤4*X := by linarith only [band.2,near]
      nlinarith only [bx,mul_nonneg xp.le (sub_nonneg.mpr (show 4≤X by linarith only [large]))]⟩
  have logg : -Real.log g ≤ Real.log X := by
    change -Real.log (Real.sqrt b)⁻¹ ≤ Real.log X
    rw [Real.log_inv,neg_neg]; exact Real.log_le_log rp top
  have base : Real.sqrt X≤2*Real.sqrt b := by
    calc
      _ ≤ Real.sqrt (4*b) := Real.sqrt_le_sqrt (by linarith only [upperDate,band.1,bp])
      _ = _ := by rw [Real.sqrt_mul (by norm_num)];norm_num
  have gθ : g≤2*P.threshold := by
    let M := Real.exp ((Real.log (Real.log X))^2)
    have one : 1≤M := Real.one_le_exp (sq_nonneg _)
    have h : (Real.sqrt b)⁻¹ ≤ 2*(Real.sqrt X)⁻¹ := by
      rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ rp (Real.sqrt_pos.mpr xp)]
      simpa using base
    change (Real.sqrt b)⁻¹ ≤ 2*((Real.sqrt X)⁻¹*M)
    exact h.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right
      (inv_nonneg.mpr (Real.sqrt_nonneg _)) one) (by norm_num))
  have income : (1:ℝ)/2 ≤ P.threshold/g := (le_div_iff₀ gp).2 (by linarith only [gθ])
  let z := H*Real.log X*((P.B:ℝ)^2*P.threshold)/g
  have zpos : 0≤z := by unfold z;positivity [P.threshold_pos]
  have room : |z| ≤ |H| *(Real.log X)^1*((P.B:ℝ)^2*P.threshold)/g := by
    rw [abs_of_nonneg zpos,abs_of_pos hp,pow_one]
  have issued := nodes N per hi z room
  rw [abs_of_nonneg zpos] at issued
  have raw : g*(1+z)^D ≤ δ := by
    calc
      _ ≤ budget D*((1+z)^D*g) := by rw [mul_comm g];exact le_mul_of_one_le_left (by positivity) (nodeFee D)
      _ ≤ _ := by simpa only [mul_assoc] using issued
  have bb : (1:ℝ)≤P.B := by exact_mod_cast P.B_pos
  have s1 : 1≤Real.log X := logb
  have cost : 1+(r:ℝ)≤z := by
    apply (cover P gp (ghalf.trans (by norm_num)) s1 support logg T).trans
    have more := mul_le_mul_of_nonneg_left income
      (show 0≤H*Real.log X*(P.B:ℝ)^2 by positivity)
    have norm : 0≤((T:ℝ)+1)*Real.log X*(P.B:ℝ)^2 := by positivity
    calc
      _ ≤ H*Real.log X*(P.B:ℝ)^2*((1:ℝ)/2) := by unfold H; linarith only [norm]
      _ ≤ _ := more.trans_eq (by unfold z;ring)
  have basez : P.threshold ≤ g*z := by
    have h₁ : 1≤H*Real.log X*(P.B:ℝ)^2 := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by unfold H; linarith only [Nat.cast_nonneg (α:=ℝ) T]) s1)
      (one_le_pow₀ bb)
    unfold z
    calc
      _ ≤ H*Real.log X*(P.B:ℝ)^2*P.threshold := le_mul_of_one_le_left P.threshold_pos.le h₁
      _ = _ := by field_simp
  have z1 : 1 ≤ 1+z := le_add_of_nonneg_right zpos
  have r1 : 1+(r:ℝ)≤1+z := cost.trans (by linarith)
  have third : P.threshold*(1+(r:ℝ))^2 ≤ g*(1+z)^D := by
    calc
      _ ≤ (g*(1+z))*(1+z)^2 := mul_le_mul (basez.trans (mul_le_mul_of_nonneg_left
        (by linarith only [zpos]) gp.le)) (pow_le_pow_left₀ (by positivity) r1 2) (by positivity)
        (mul_nonneg gp.le (by positivity))
      _ = g*(1+z)^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ z1 (le_max_left ..)) gp.le
  have last : g*(1+(r:ℝ))^l ≤ g*(1+z)^D := mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (by positivity) r1 l).trans (pow_le_pow_right₀ z1 (le_max_right ..))) gp.le
  have cash := (le_div_iff₀ (show 0<1+C by linarith)).mp (raw.trans (min_le_right ..))
  refine ⟨gp,ghalf,gθ,third.trans (raw.trans (min_le_left ..)),?_⟩
  calc
    _ = C*(g*(1+(r:ℝ))^l) := by ring
    _ ≤ C*(g*(1+z)^D) := mul_le_mul_of_nonneg_left last cc
    _ ≤ _ := (mul_le_mul_of_nonneg_right (show C≤1+C by linarith)
      (mul_nonneg gp.le (pow_nonneg (show 0≤1+z by linarith only [zpos]) D))).trans
        (by simpa only [mul_comm (1+C)] using cash)

end YM.Integration.WilsonCapturedPrimaryCourse
