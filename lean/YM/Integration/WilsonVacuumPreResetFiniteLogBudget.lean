import YM.Integration.WilsonVacuumPreResetFiniteTilt
import YM.Integration.MSFixedRatioSaddleWick
import YM.Next.RANK.Guard

/-! An all-order, finite polynomial price for the genuine normalized finite
vacuum logarithm. The difference of real shifted weight polynomials retains
the entire old nonquadratic input before the Gaussian average. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteLogBudget
open Function Finset PowerSeries FormalBulk08 FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Series
open Comparison.RG02 Comparison.RG02.Cumulants Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped Classical BigOperators

private theorem product {n:ℕ}{A B:ℝ}{f g:PowerSeries ℝ} (ha:0≤A)
    (hf:∀i≤n,|coeff i f|≤A) (hg:∀i≤n,|coeff i g|≤B) {i:ℕ}(hi:i≤n):
    |coeff i (f*g)|≤(n+1)*(A*B):=by
  have hb:0≤B:=(abs_nonneg _).trans (hg 0 (Nat.zero_le _))
  rw [coeff_mul]
  calc
    _≤∑v∈antidiagonal i,|coeff v.1 f*coeff v.2 g|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑_v∈antidiagonal i,A*B:=by
      apply Finset.sum_le_sum
      intro v hv
      have both:v.1+v.2=i:=by simpa using hv
      rw [abs_mul]
      exact mul_le_mul (hf _ (by omega)) (hg _ (by omega)) (abs_nonneg _) ha
    _≤_:=by
      simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right (show (i+1:ℝ)≤n+1 by exact_mod_cast Nat.succ_le_succ hi) (mul_nonneg ha hb)

private theorem powers {n:ℕ} (f g:PowerSeries ℝ) (A D:ℝ)(ha:0≤A)(hd:0≤D)
    (hf:∀i≤n,|coeff i f|≤A) (hg:∀i≤n,|coeff i g|≤A) (delta:∀i≤n,|coeff i (f-g)|≤D)(k:ℕ):
    let C:=(n+1:ℝ)*(1+A)
    (∀i≤n,|coeff i (f^k)|≤C^k) ∧ (∀i≤n,|coeff i (f^k-g^k)|≤C^k*D):=by
  intro C
  induction k with
  | zero=>
    constructor
    · intro i _;by_cases i=0 <;> simp [*,coeff_one]
    · simp [hd]
  | succ k ih=>
    have hc:0≤C:=by unfold C;positivity
    have hk:=pow_nonneg hc k
    constructor
    · intro i hi
      rw [pow_succ]
      apply (product hk ih.1 hf hi).trans
      rw [pow_succ];unfold C
      nlinarith [mul_nonneg (by positivity : 0≤(n+1:ℝ)) hk]
    · intro i hi
      have identity:f^(k+1)-g^(k+1)=f^k*(f-g)+(f^k-g^k)*g:=by ring
      rw [identity,map_add]
      apply (abs_add_le ..).trans
      apply (add_le_add (product hk ih.1 delta hi) (product (mul_nonneg hk hd) ih.2 hg hi)).trans
      rw [pow_succ];unfold C;ring_nf;exact le_rfl

private theorem logarithm {n:ℕ}{f g:PowerSeries ℝ}(one:coeff 0 f=1)(two:coeff 0 g=1)
    (A D:ℝ)(ha:0≤A)(hd:0≤D) (hf:∀i≤ n,|coeff i (f-1)|≤A)
    (hg:∀i≤n,|coeff i (g-1)|≤A)(delta:∀i≤ n,|coeff i (f-g)|≤D):
    |coeff n (covelog f-covelog g)|≤
      (∑k∈range (n+1),|coeff k (stem ℝ)| *((n+1:ℝ)*(1+A))^k)*D:=by
  have hf0:coeff 0 (f-1)=0:=by rw [map_sub,one];simp
  have hg0:coeff 0 (g-1)=0:=by rw [map_sub,two];simp
  have hdif:∀i≤n,|coeff i ((f-1)-(g-1))|≤D:=by simpa using delta
  rw [map_sub,covelog,covelog,subst_coeff hf0 _ n n le_rfl,subst_coeff hg0 _ n n le_rfl,←sum_sub_distrib,sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [←mul_sub,abs_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [map_sub] using (powers (f-1) (g-1) A D ha hd hf hg hdif k).2 n le_rfl

variable {U I:Type} [Fintype U] [DecidableEq U]
def polynomial (B:I→ℝ)(P:Orb.Ink U I)(e:ℕ):MvPolynomial U ℂ:=
  MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (MvPolynomial.eval B) (coeff e P))

def fee (M:ℝ) (B:I→ℝ)(P:Orb.Ink U I)(e:ℕ):ℝ:=
  let w:=polynomial B P e
  Rise.coin w*Common.priced M w.totalDegree

private theorem measured (H:Hull U I) (M:ℝ) (one:1≤M) (paid:∀i j,|H.saddle.q i j|≤M)
    (B:I→ℝ)(P:Orb.Ink U I)(e:ℕ):
    |MvPolynomial.eval B (coeff e (beam (variation H.saddle I).call P))|≤fee M B P e:=by
  let T:=realRank H.saddle.q (show H.saddle.q.IsSymm by ext i j;exact H.saddle.ok j i)
  let w:=polynomial B P e
  have v:=MSFixedRatioSaddleWick.coefficient H.saddle B P e
  have bound:=Tapes.bound_v (m:=0) w T (le_refl _) one (fun _ _=>by simpa using zero_le_one.trans one)
    (fun i _ j _=>by simpa [T,realRank] using paid i j)
  change ‖Cloud.wick H.saddle.q _ 0 w‖≤fee M B P e at bound
  have vv:Cloud.wick H.saddle.q _ 0 w=(MvPolynomial.eval B (coeff e (beam (variation H.saddle I).call P)):ℂ):=v
  rw [vv,Complex.norm_real,Real.norm_eq_abs] at bound
  exact bound

/-- Full incoming and reference masses, plus one signed change in the weights,
suffice for the normalized log at this coupling order on each coarse field. -/
theorem compared (H:Hull U I)(P Q:Pap (U⊕I))(hp:Solved H P)(hq:Solved H Q)
    (M:ℝ)(one:1≤M)(paid:∀i j,|H.saddle.q i j|≤M)(B:I→ℝ)(n:ℕ):
    let UQ:=expan (positive H Q)
    let UP:=expan (positive H P)
    let A:=1+∑i∈range (n+1),(fee M B UQ i+fee M B UP i)
    let D:=∑i∈range (n+1),fee M B (UQ-UP) i
    |MvPolynomial.eval B (coeff n (Orb.out H Q-Orb.out H P))|≤
      (∑k∈range (n+1),|coeff k (stem ℝ)| *((n+1:ℝ)*(1+A))^k)*D:=by
  intro UQ UP A D
  let f:=PowerSeries.map (MvPolynomial.eval B) (vocal H Q)
  let g:=PowerSeries.map (MvPolynomial.eval B) (vocal H P)
  have hf0:coeff 0 f=1:=by rw [show coeff 0 f=_ from coeff_map ..,voice H Q hq,map_one]
  have hg0:coeff 0 g=1:=by rw [show coeff 0 g=_ from coeff_map ..,voice H P hp,map_one]
  have fee_pos (T:Orb.Ink U I) (e:ℕ):0≤fee M B T e:=(abs_nonneg _).trans (measured H M one paid B T e)
  have ha:0≤A:=add_nonneg zero_le_one (sum_nonneg fun i _=>add_nonneg (fee_pos _ i) (fee_pos _ i))
  have hd:0≤D:=sum_nonneg fun i _=>fee_pos _ i
  have priced (i:ℕ) (hi:i≤n): |coeff i (f-1)|≤A ∧ |coeff i (g-1)|≤A:=by
    have cost:fee M B UQ i+fee M B UP i≤∑j∈range (n+1),(fee M B UQ j+fee M B UP j):=
      single_le_sum (fun j _=>add_nonneg (fee_pos _ j) (fee_pos _ j)) (mem_range.mpr (by omega))
    have a:=measured H M one paid B UQ i
    have b:=measured H M one paid B UP i
    have h:|coeff i (1:PowerSeries ℝ)|≤1:=by by_cases i=0 <;>simp [*,coeff_one]
    have q:|coeff i f|≤fee M B UQ i:=by simpa [f,vocal,UQ] using a
    have p:|coeff i g|≤fee M B UP i:=by simpa [g,vocal,UP] using b
    simp only [map_sub]
    constructor
    · exact (abs_sub ..).trans (by dsimp [A];linarith [abs_nonneg (coeff i g)])
    · exact (abs_sub ..).trans (by dsimp [A];linarith [abs_nonneg (coeff i f)])
  have delta (i:ℕ)(hi:i≤n):|coeff i (f-g)|≤D:=by
    have a:=measured H M one paid B (UQ-UP) i
    have b:|coeff i (f-g)|≤fee M B (UQ-UP) i:=by simpa [f,g,vocal,UQ,UP,map_sub] using a
    exact b.trans (single_le_sum (fun j _=> fee_pos _ j) (mem_range.mpr (by omega)))
  have main:=logarithm hf0 hg0 A D ha hd (fun i hi=>(priced i hi).1) (fun i hi=>(priced i hi).2) delta
  have eq:PowerSeries.map (MvPolynomial.eval B) (Orb.out H Q-Orb.out H P)=covelog f-covelog g:=by
    rw [Orb.out,Orb.out,add_sub_add_left_eq_sub,map_sub,map_covelog _ (voice H Q hq),map_covelog _ (voice H P hp)]
  rwa [←eq,coeff_map] at main

end YM.Integration.WilsonVacuumPreResetFiniteLogBudget
end
