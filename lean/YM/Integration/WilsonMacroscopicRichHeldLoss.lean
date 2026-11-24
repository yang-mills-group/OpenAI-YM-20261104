import YM.Integration.WilsonMacroscopicRichHeldMarkedScore

/-! A localized signed derivative spends a finite number of orders of the actual Wilson coupling, uniformly in its true finite volume and cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichHeldLoss
open Function Filter MeasureTheory Lattice Wilson RG Source Push.Local Push.Local.Kernel PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonMacroscopicRichHeldProbePrice
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G : Gauge}

def exponent : ℕ → ℕ | 0 => 0 | m+1 => exponent m + exponent m + 1

def loss (k : ℕ) := k * (exponent k + 1)

private lemma inverse (k : ℕ) (C : ℝ) (m : ℕ) : invRate k C m = ((2:ℝ)^k * (2^k*C))^(exponent m) := by
  induction m with
  | zero => simp [invRate,exponent]
  | succ m ih => simp only [invRate,exponent,ih,pow_add,pow_one];ring

def unit (R : Run G) (k width : ℕ) (r : ℝ) := (noiseFactor G (2*R.family.path.levels.clock.kernel.penalty) k width r)^k

def capital (R : Run G) (k width : ℕ) (r : ℝ) := (2:ℝ)^k * (unit R k width r * invRate k (unit R k width r) k)

theorem physical (R : Run G) (k width : ℕ) {r : ℝ} (rp : 0≤r) :
    0 ≤ capital R k width r ∧ ∀ m, price R m k width r ≤ capital R k width r * (R.family.path.levels.clock.hatBeta (m+1))^(loss k) := by
  let t := unit R k width r
  let a : ℝ := 2^k
  have ap : 0 ≤ a := pow_nonneg (by norm_num) _
  have tp : 0 ≤ t := pow_nonneg (zero_le_one.trans (noiseFactor_ge G _ k width rp)) _
  have cc : 0 ≤ capital R k width r := by
    unfold capital;rw [inverse];exact mul_nonneg ap (mul_nonneg tp (pow_nonneg (mul_nonneg ap (mul_nonneg ap tp)) _))
  refine ⟨cc,?_⟩
  intro m
  let b := R.family.path.levels.clock.hatBeta (m+1)
  let κ := R.family.path.levels.clock.kernel.penalty
  have one : 1≤b := (R.family.path.levels.fits.delayed (m+1)).le
  have bp : 0 ≤ b := zero_le_one.trans one
  let x := noise R m k width r
  have xp : 0 ≤ x := pow_nonneg (zero_le_one.trans (noiseFactor_ge G _ k width rp)) _
  have field : noiseFactor G (2*b*κ) k width r ≤ b * noiseFactor G (2*κ) k width r := by
    unfold noiseFactor scorePrice
    rw [show 2*b*κ=b*(2*κ) by ring,abs_mul,abs_of_nonneg bp]
    nlinarith only [mul_le_mul_of_nonneg_left one ap]
  have xn : x ≤ b^k*t := by
    change (noiseFactor G (2*b*κ) k width r)^k ≤ b^k * (noiseFactor G (2*κ) k width r)^k
    rw [←mul_pow]
    exact pow_le_pow_left₀ (zero_le_one.trans (noiseFactor_ge G (2*b*κ) k width rp)) field k
  have ax : a*(a*x) ≤ b^k * (a*(a*t)) := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left xn ap) ap).trans_eq (by ring)
  change a * (x*invRate k x k) ≤ a*(t*invRate k t k)*b^(loss k)
  rw [inverse,inverse]
  calc a*(x*(a*(a*x))^(exponent k)) ≤ a*((b^k*t)*(b^k*(a*(a*t)))^(exponent k)) :=
         mul_le_mul_of_nonneg_left (mul_le_mul xn (pow_le_pow_left₀ (mul_nonneg ap (mul_nonneg ap xp)) ax _)
           (pow_nonneg (mul_nonneg ap (mul_nonneg ap xp)) _) (mul_nonneg (pow_nonneg bp _) tp)) ap
       _ = _ := by unfold loss; rw [mul_pow,pow_mul,pow_add,pow_one];ring

theorem orders (R : Run G) (k width q : ℕ) {r : ℝ} (hr : 0≤r) (m N p : ℕ) (live : m+1 ≤ N) :
    let g := regulatorRun R.family N p (m+1)
    price R m k width r * g^(q+2*loss k) ≤ (capital R k width r * 2^(loss k)) * g^q := by
  intro g
  let b := R.family.path.levels.clock.hatBeta (m+1)
  let β := R.family.path.β N p (m+1)
  have bp : 0 < b := zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have band : b/2≤β := (R.makes.wilson.represents N p (m+1) live).band.1
  have beta : 0 < β := (half_pos bp).trans_le band
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have rate : b*g^2 ≤ 2 := by
    change b*(Real.sqrt β)⁻¹^2 ≤ 2
    rw [inv_pow,Real.sq_sqrt beta.le,←div_eq_mul_inv,div_le_iff₀ beta];linarith only [band]
  obtain ⟨cc,pm⟩ := physical R k width hr
  calc _ ≤ (capital R k width r * b^(loss k))*g^(q+2*loss k) := mul_le_mul_of_nonneg_right (pm m) (pow_nonneg gp _)
       _ = capital R k width r*((b*g^2)^(loss k))*g^q := by rw [pow_add,pow_mul,mul_pow];ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg bp.le (sq_nonneg _)) rate _) cc) (pow_nonneg gp _)

end YM.Integration.WilsonMacroscopicRichHeldLoss
