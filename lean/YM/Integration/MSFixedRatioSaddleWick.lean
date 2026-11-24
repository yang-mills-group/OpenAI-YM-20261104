import YM.FormalBulk08.Orb.Triplet
import YM.Integration.PeriodicMarkedHeat

/-! Literal RG02 finite Gaussian moments of the fixed-ratio saddle at every open coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioSaddleWick
open Function Finset MvPolynomial FormalBulk08 FormalBulk08.Series FormalBulk08.Wick
open FormalBulk08.Orb WilsonCoeffUV.Blue Comparison.RG02 Cumulants
open Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped Classical BigOperators
variable {I Y : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
private lemma evaluated (i : I) (A : Polynomial (MvPolynomial I ℝ)) :
    MvPolynomial.pderiv i (A.eval 1)=(Wick.grain i A).eval 1 := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp only [Polynomial.eval_add,map_add,hA,hB]
  | monomial n c =>
    have h : Wick.grain i (Polynomial.monomial n c)=Polynomial.monomial n (MvPolynomial.pderiv i c) := by
      ext k
      rw [Wick.grain_coeff]
      by_cases h:n=k
      · subst k
        simp
      · simp [Polynomial.coeff_monomial,h]
    rw [h]
    simp

omit [DecidableEq I] in
theorem derivative (Q : Matrix I I ℝ) (p : MvPolynomial I ℝ) (i : I) :
    Wick.hearth Q (MvPolynomial.pderiv i p)=MvPolynomial.pderiv i (Wick.hearth Q p) := by
  have hpow (n : ℕ) : MvPolynomial.pderiv i ((Wick.press Q ^ n) p) =
      (Wick.press Q ^ n) (MvPolynomial.pderiv i p) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Module.End.mul_apply,Module.End.mul_apply,←Wick.press_commutes,ih]
  have h : Wick.grain i (Wick.bake Q p)=Wick.bake Q (MvPolynomial.pderiv i p) := by
    apply Polynomial.ext
    intro n
    rw [Wick.grain_coeff,Wick.bake_coeff,Wick.bake_coeff,Derivation.map_smul,hpow]
  rw [Wick.hearth_def,Wick.hearth_def,evaluated,h]

omit [DecidableEq I] in
/-- Both finite heat treatments keep the complete resulting polynomial, with no evaluation
of a field direction or contraction of a color index. -/
theorem polynomial (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (p : MvPolynomial I ℝ) :
    Wick.hearth Q p=WilsonCoeffUV.Blue.glaze Q p := by
  have hs i j : Q i j=Q j i := congrFun (congrFun hQ j) i
  induction p using MvPolynomial.induction_on with
  | C a => rw [Wick.hearth_C,WilsonCoeffUV.Blue.glaze_constant]
  | add p q hp hq => rw [map_add,map_add,hp,hq]
  | mul_X p i hp =>
    calc _ = MvPolynomial.X i*Wick.hearth Q p+
          ∑j,MvPolynomial.C (Q i j)*Wick.hearth Q (MvPolynomial.pderiv j p) := by
            rw [mul_comm p (MvPolynomial.X i),Wick.hearth_X Q hs]
      _ = WilsonCoeffUV.Blue.glaze Q p*MvPolynomial.X i+
          ∑j,Q i j • WilsonCoeffUV.Blue.glaze Q (MvPolynomial.pderiv j p) := by
            simp only [derivative,WilsonCoeffUV.Blue.glaze_deriv,hp,MvPolynomial.C_mul']
            rw [mul_comm (MvPolynomial.X i)]
      _ = _ := (WilsonCoeffUV.Blue.wick_poly Q hQ p i).symm

omit [DecidableEq I] in
/-- The fixed-ratio moment equals the original complex RG02 Gaussian moment on a real
finite polynomial at the same complete covariance. -/
theorem moment (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (p : MvPolynomial I ℝ) :
    Cloud.wick Q hQ 0 (MvPolynomial.map Complex.ofRealHom p)=(Wick.moment Q p:ℂ) := by
  change MvPolynomial.aeval (0 : I→ℂ) (Normal.milk (realRank Q hQ) _) = _
  rw [PeriodicMarkedHeat.heat_real Q hQ,←polynomial Q hQ,Wick.moment_eq]
  simp only [MvPolynomial.aeval_zero,MvPolynomial.constantCoeff_map]
  rfl

/-- The external coarse field is free and is evaluated only after the genuine Gaussian
integration over the stationary fluctuation variables. -/
theorem coefficient (T : Saddle ℝ I) (B : Y→ℝ) (P : FormalBulk08.Orb.Ink I Y) (e : ℕ) :
    Cloud.wick T.q (by ext i j;exact T.ok j i) 0
      (MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (MvPolynomial.eval B) (PowerSeries.coeff e P))) =
      (MvPolynomial.eval B (PowerSeries.coeff e (beam (variation T Y).call P)):ℂ) := by
  rw [moment,coeff_beam]
  apply congrArg (fun x:ℝ=>(x:ℂ))
  change Wick.moment T.q (MvPolynomial.map (MvPolynomial.eval B) _) =
    MvPolynomial.eval B (Wick.moment _ _)
  have hQ : (fun i j=>(MvPolynomial.eval B) ((variation T Y).q i j))=T.q := by
    funext i j
    exact MvPolynomial.eval_C ..
  rw [Wick.moment_map,hQ]

/-- At the true finite saddle the full complex marked numerator is the convolution of the
same Gaussian vacuum mass and the original normalized finite mark. -/
theorem normalized (H : Hull I Y) (p q : Pap (I⊕Y)) (hp : Orb.Solved H p) (B : Y→ℝ) (e : ℕ) :
    Cloud.wick H.saddle.q (by ext i j;exact H.saddle.ok j i) 0
      (MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (MvPolynomial.eval B)
        (PowerSeries.coeff e (expan (positive H p)*toInk H q)))) =
      ∑j∈Finset.HasAntidiagonal.antidiagonal e,
        (MvPolynomial.eval B (PowerSeries.coeff j.1 (vocal H p)):ℂ)*
        (MvPolynomial.eval B (PowerSeries.coeff j.2 (flag H p q)):ℂ) := by
  rw [coefficient H.saddle B,←Orb.normalization H p hp q,PowerSeries.coeff_mul]
  simp only [map_sum,map_mul,Complex.ofReal_sum,Complex.ofReal_mul]

end YM.Integration.MSFixedRatioSaddleWick

