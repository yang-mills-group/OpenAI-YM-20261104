import YM.WilsonCoeffUV.Emit.NoiseLaw
import YM.PertExtension.Exponent

/-! Finite coefficient arithmetic for the actual scalar Gaussian phase and its
independently charged numerator.  Coordinates and the constant term of the
original normalized phase are retained through substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringWickExponential

open Finset PowerSeries WilsonCoeffUV.Blue PertExtension.Series
open scoped BigOperators Classical

variable {X B : Type*} [CommRing B] (e : X → B →+* ℝ)

/-- Read the original formal coefficient at its actual Gaussian coordinates. -/
def value (P : PowerSeries B) (k : ℕ) (x : X) : ℝ := e x (coeff k P)

theorem power (P : PowerSeries B) (a k : ℕ) (x : X) :
    e x (coeff k (P^a)) = Zone.TaylorPow (value e P) a k x := by
  induction a generalizing k with
  | zero =>
    cases k <;> simp [Zone.TaylorPow]
  | succ a ih =>
    rw [pow_succ,coeff_mul,map_sum]
    change _=∑ d ∈ antidiagonal k, Zone.TaylorPow (value e P) a d.1 x * value e P d.2 x
    apply sum_congr rfl
    intro d _
    rw [map_mul]
    exact congrArg (fun a => a*value e P d.2 x) (ih d.1)

/-- Only the actual values at grades at most k enter a finite exponential
coefficient; no continuation past the purchased foreground is required. -/
theorem «prefix» (a b : ℕ → X → ℝ) (k : ℕ) (x : X) (h : ∀ i≤k,a i x=b i x) :
    Radial.expsum a k k x=Radial.expsum b k k x := by
  have powers (n : ℕ) : ∀ i≤k,Zone.TaylorPow a n i x=Zone.TaylorPow b n i x := by
    induction n with
    | zero => intro i _; rfl
    | succ n ih =>
      intro i hi
      change (∑ d ∈ antidiagonal i,Zone.TaylorPow a n d.1 x*a d.2 x)=
        ∑ d ∈ antidiagonal i,Zone.TaylorPow b n d.1 x*b d.2 x
      apply Finset.sum_congr rfl
      intro d hd
      have he : d.1+d.2=i := mem_antidiagonal.mp hd
      rw [ih d.1 (by omega),h d.2 (by omega)]
  unfold Radial.expsum
  apply Finset.sum_congr rfl
  intro j _
  rw [powers j k le_rfl]

variable [Algebra ℚ B]

/-- Each finite perturbative coefficient of the real exponential is the actual
radial exponential polynomial at the same submitted point. -/
theorem raised (P : PowerSeries B) (hP : constantCoeff P=0) (k : ℕ) (x : X) :
    value e (raiseE P) k x = Radial.expsum (value e P) k k x := by
  have hx : constantCoeff (PowerSeries.map (e x) PowerSeries.X)=0 := by simp
  have hp : constantCoeff (PowerSeries.map (e x) P)=0 := by
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,hP,map_zero]
  calc
    value e (raiseE P) k x = coeff k (PowerSeries.map (e x) (raiseE P)) := by simp only [value,coeff_map]
    _ = coeff k (raiseE (PowerSeries.map (e x) P)) :=
      congrArg (coeff k) (raise_map (PowerSeries.map (e x)) hx hP)
    _ = _ := by
      rw [WilsonCoeffUV.Convention.expansion_price _ hp]
      unfold Radial.expsum
      apply sum_congr rfl
      intro i _
      rw [←(PowerSeries.map (e x)).map_pow,coeff_map,power]

theorem unit (P : PowerSeries B) (hP : constantCoeff P=0) (x : X) :
    value e (raiseE P) 0 x=1 := by
  unfold value
  rw [coeff_zero_eq_constantCoeff_apply,raise_one hP,map_one]

/-- Evaluation at true original real coordinates commutes with the logarithm
of a unit-leading scalar mass. -/
theorem log_map [IsAddTorsionFree B] (q : PowerSeries B) (hq : constantCoeff q=1) (x : X) :
    PowerSeries.map (e x) (logOf q)=logOf (PowerSeries.map (e x) q) := by
  have image (p : PowerSeries B) :
      constantCoeff (PowerSeries.map (e x) p)=e x (constantCoeff p) := by
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply]
  have h1 : constantCoeff (PowerSeries.map (e x) q)=1 := by rw [image,hq,map_one]
  have h0 : constantCoeff (logOf q)=0 := constantCoeff_logOf hq
  have h2 : constantCoeff (PowerSeries.map (e x) (logOf q))=0 := by rw [image,h0,map_zero]
  apply raise_inj h2 (constantCoeff_logOf h1)
  have hx : constantCoeff (PowerSeries.map (e x) PowerSeries.X)=0 := by simp
  rw [←raise_map (PowerSeries.map (e x)) hx h0,raising_log hq,raising_log h1]

/-- An arbitrary genuine complex or marked multiplier retains its true
coefficient, including its degree-zero term and every nonempty marking. -/
theorem charged {S : Type*} [CommRing S] [Algebra ℝ S] (P : PowerSeries B)
    (hP : constantCoeff P=0) (M : PowerSeries S) (k : ℕ) (x : X) :
    coeff k (PowerSeries.map (algebraMap ℝ S) (PowerSeries.map (e x) (raiseE P))*M) =
    ∑ d ∈ antidiagonal k,algebraMap ℝ S (Radial.expsum (value e P) d.1 d.1 x) * coeff d.2 M := by
  rw [coeff_mul]
  apply sum_congr rfl
  intro d _
  rw [coeff_map,coeff_map]
  exact congrArg (fun t => algebraMap ℝ S t*coeff d.2 M) (raised e P hP d.1 x)

end YM.Integration.WilsonLimitConstruction.FundedSpringWickExponential
