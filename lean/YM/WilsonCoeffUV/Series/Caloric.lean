import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import YM.WilsonCoeffUV.Series.Tensor
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Matrix.Basic

/-!
# Wick polynomial calculus using a spectator (heat time)

Polynomial and series coefficients only. Algebraic, allows *singular* covariance
so also means, shared noise, off-tree zero padding and sources in auxiliary variables.
Construction by insertion; uniqueness by entire coefficient polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function MvPolynomial Matrix
open scoped BigOperators Classical
variable {U V F : Type*}

/-! The spectator. -/
def stopT (x:ℝ) : POL (Option U) →ₐ[ℝ] POL U := MvPolynomial.aeval (fun j : Option U=> j.elim (C x) X)
def launchT : POL U→ₐ[ℝ] POL (Option U) := rename some
lemma stopT_X (i : Option U) (x:ℝ) : stopT x (X i)= i.elim (C x) X := by rw [stopT,aeval_X]
lemma stopT_launch (p:POL U)(x:ℝ) : stopT x (launchT p)=p := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [launchT,stopT,algebraMap_eq]
  | add p q a b=> simp [a,b]
  | mul_X p j h=> rw [map_mul,map_mul,h,launchT,MvPolynomial.rename_X, stopT_X]; rfl
lemma launched (p:POL U) : optionEquivLeft ℝ U (launchT p)=Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [launchT]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p j h=> rw [map_mul,map_mul,h,launchT,MvPolynomial.rename_X,optionEquivLeft_X_some,map_mul]

/-- Finite polynomial degree in heat time, no completion in that variable. -/
abbrev Scan (U:Type*) := POL (Option U)

lemma elapsed (p:Scan U)(x:ℝ): (optionEquivLeft ℝ U p).eval (C x)=stopT x p := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [stopT,algebraMap_eq]
  | add p q a b=> simp [a,b]
  | mul_X p j h=> rw [map_mul,map_mul, Polynomial.eval_mul,h,stopT_X]; cases j <;> simp

def tic (U:Type*) := (pderiv (R:=ℝ) (none:Option U)).toLinearMap
lemma tick (U:Type*)(p) : tic U p=pderiv none p:= rfl
lemma toc (p : Scan U) : optionEquivLeft ℝ U (tic U p) = (optionEquivLeft ℝ U p).derivative := by
  rw [tick]
  induction p using MvPolynomial.induction_on with
  | C a=> simp
  | add p q a b=> simp [a,b]
  | mul_X p j h => rw [pderiv_mul,map_add,map_mul,map_mul,map_mul,h, Polynomial.derivative_mul]; cases j <;> simp [add_comm]

abbrev spanT (i:ℕ) (U:Type*): Scan U →ₗ[ℝ] POL U :=
  (@Polynomial.lcoeff (MvPolynomial U ℝ) _ i).restrictScalars ℝ |>.comp (optionEquivLeft ℝ U).toLinearMap
lemma span_time (u:Scan U)(i:ℕ) : spanT i U u=(optionEquivLeft ℝ U u).coeff i:=rfl
lemma span_zero (p:Scan U) : spanT 0 U p=stopT 0 p := by rw [span_time,←elapsed, map_zero,Polynomial.coeff_zero_eq_eval_zero]
lemma span_clock (u:Scan U)(i) : spanT i U (tic U u)= (i+1) • spanT (i+1) U u := by
  rw [span_time,span_time,toc, Polynomial.coeff_derivative,nsmul_eq_mul,mul_comm]; simp
lemma span_excise (p:Scan U)(x:U)(i : ℕ) : spanT i U (pderiv (.some x) p) = pderiv x (spanT i U p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial k r=>
    rw [pderiv_monomial,span_time,span_time,optionEquivLeft_monomial,optionEquivLeft_monomial]
    have he : (k - Finsupp.single (some x) 1).some=k.some-Finsupp.single x 1 := by ext j; by_cases h:j=x <;> simp [h]
    simp_rw [he,Polynomial.coeff_monomial]; split_ifs <;> simp_all
  | add p q a b=> simp only [map_add,a,b]
lemma span_post (p:Scan U) (x:U)(v:ℝ) : stopT v (pderiv (.some x) p)= pderiv x (stopT v p) := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [stopT]
  | add p q a b=> simp [a,b]
  | mul_X p j h=> rw [pderiv_mul, map_add,map_mul,map_mul,map_mul,pderiv_mul,h,stopT_X]; cases j with
                    | none=> simp
                    | some j=> by_cases h:j=x <;> simp [h]
lemma time_only {p:Scan U} (h:pderiv none p=0) (x y:ℝ) : stopT x p=stopT y p := by
  have he := Polynomial.eq_C_of_derivative_eq_zero (p:=optionEquivLeft ℝ U p) (by rw [←toc,tick,h,map_zero]); rw [←elapsed,←elapsed,he]; simp

section Blur
variable [Fintype U]

def windowLap (G:Matrix U U ℝ)(i:U→F) : POL F→ₗ[ℝ] POL F :=
  ∑ a: U,∑ b: U,(G a b/2) • ((pderiv (i a)).toLinearMap.comp (pderiv (i b)).toLinearMap)
abbrev traceLap (G : Matrix U U ℝ) := windowLap G id

def foldsH {G : Matrix U U ℝ}(p : POL U)(f : Scan U) := tic U f=windowLap G some f ∧ stopT 0 f=p

lemma windowLap_apply (G:Matrix U U ℝ)(i:U→F)(p) : windowLap G i p=∑ a: U,∑ b:U,(G a b/2) • pderiv (i a) (pderiv (i b) p) := by unfold windowLap; simp
lemma polarLap (G:Matrix U U ℝ)(i:U→F)(p q:POL F) : windowLap G i (p*q) = windowLap G i p * q + p*windowLap G i q +∑ a:U,∑ b:U,(G a b/2) • (pderiv (i a) p * pderiv (i b) q+pderiv (i b) p*pderiv (i a) q) := by
  simp only [windowLap_apply,pderiv_mul,map_add,smul_add]; simp_rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]; simp only [smul_mul_assoc,mul_smul_comm]; ring
lemma orbitLap (G:Matrix U U ℝ)(i:U→F)(p) (x:F) : windowLap G i (pderiv x p) = pderiv x (windowLap G i p) := by
  simp_rw [windowLap_apply,map_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
  rw [Derivation.map_smul,poly_commute (i b) x,poly_commute (i a) x]
lemma cadenceLap (G:Matrix U U ℝ)(p : Scan U)(n): spanT n U (windowLap G some p)= traceLap G (spanT n U p) := by
  simp_rw [windowLap_apply,map_sum,map_smul,span_excise]; rfl
lemma definite (G:Matrix U U ℝ)(p:POL U) {f g:Scan U}(h:foldsH (G:=G) p f)(e:foldsH (G:=G) p g) : f=g := by
  apply (optionEquivLeft ℝ U).injective; apply Polynomial.ext; intro n
  change spanT n U f=spanT n U g
  induction n with
  | zero => rw [span_zero,span_zero,h.2,e.2]
  | succ n ih=> apply (smul_right_inj (M:=POL U) n.succ_ne_zero).mp; rw [←span_clock,←span_clock,h.1,e.1,cadenceLap,cadenceLap,ih]

lemma foldConstant (G:Matrix U U ℝ)(a:ℝ) : foldsH (G:=G) (C a) (C a) := by rw [foldsH,windowLap_apply,tick]; simp [stopT,algebraMap_eq]
lemma foldPlus {f g:Scan U}{G:Matrix U U ℝ}{p q:POL U}(h:foldsH (G:=G) p f)(e:foldsH (G:=G) q g) : foldsH (G:=G) (p+q) (f+g) := by
  rw [foldsH, map_add,map_add,h.1,e.1,map_add,h.2,e.2]; trivial
lemma foldScalar {f:Scan U}{G:Matrix U U ℝ}{p:POL U}(h:foldsH (G:=G) p f)(c:ℝ): foldsH (G:=G) (c•p) (c•f) := by
  simp only [foldsH,map_smul, h.1,h.2]; trivial
lemma foldPeel {f:Scan U}{G:Matrix U U ℝ}{p:POL U}(h:foldsH (G:=G) p f)(u:U) : foldsH (G:=G) (pderiv u p) (pderiv (.some u) f) := by
  rw [foldsH,orbitLap,h.1.symm,tick,tick,poly_commute none (.some u),span_post,h.2]; trivial

-- insert an X at a normal log slot into blurred polynomial. No G symmetric assumption required for existence (symmetrize weight).
def blend (G:Matrix U U ℝ)(i j:U) : ℝ := (G i j+G j i)/2
def seep (G:Matrix U U ℝ)(i:U) (f:Scan U) : Scan U := ∑ a, blend G i a • pderiv (.some a) f

def budding (G:Matrix U U ℝ) (i:U) (f : Scan U) := f*X (.some i)+ X none * seep G i f
lemma Lap_x (G:Matrix U U ℝ)(j:U→F)(y:F) : windowLap G j (X y)=0 := by
  unfold windowLap; rw [LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro a _; rw [LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro b _
  by_cases h:y=j b<;>simp [h]
lemma Lap_t (G:Matrix U U ℝ)(p) : windowLap G some (X none*p)=X none*windowLap G some p := by rw [polarLap,Lap_x]; simp
lemma Lap_var (G:Matrix U U ℝ)(i:U) (p) : windowLap G some (p*X (.some i))=windowLap G some p * X (.some i)+seep G i p := by
  rw [polarLap,Lap_x]; simp only [mul_zero,add_zero]; congr 1
  simp_rw [seep,blend,add_div,add_smul,smul_add,Finset.sum_add_distrib]
  conv_lhs => rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single i]<;>simp +contextual

  apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single i]<;>simp +contextual
lemma seepFlow (G:Matrix U U ℝ){p:Scan U}(h:tic U p=windowLap G some p)(i:U) : tic U (seep G i p)=windowLap G some (seep G i p) := by
  simp_rw [seep,map_sum,map_smul]; apply Finset.sum_congr rfl; intro a _; congr 1; rw [orbitLap,←h,tick,tick,poly_commute none _]
lemma foldBudding {G:Matrix U U ℝ}{p:POL U}{f:Scan U}(h:foldsH (G:=G) p f)(i:U) : foldsH (G:=G) (p*X i) (budding G i f) := by
  have he := h.1
  rw [foldsH,budding,map_add,map_add,Lap_t,Lap_var]
  constructor
  · simp_rw [← he,← seepFlow G he i,tick, pderiv_mul]; simp [add_assoc]
  rw [map_add,map_mul,map_mul,h.2]; simp [stopT_X]
lemma heat_exists (G:Matrix U U ℝ)(p : POL U): ∃ f:Scan U, foldsH (G:=G) p f := by
  induction p using MvPolynomial.induction_on with
  | C a=> exact ⟨_,foldConstant G a⟩
  | add p q a b=> exact ⟨_,foldPlus a.choose_spec b.choose_spec⟩
  | mul_X p i h=> exact ⟨_,foldBudding h.choose_spec i⟩

def spreadH (G:Matrix U U ℝ) : POL U→ₗ[ℝ]Scan U where
  toFun p:=(heat_exists G p).choose
  map_add' p q:=definite G (p+q) (heat_exists ..).choose_spec (foldPlus (heat_exists ..).choose_spec (heat_exists ..).choose_spec)
  map_smul' c p:= definite G (c•p) (heat_exists ..).choose_spec (foldScalar (heat_exists ..).choose_spec _)
lemma spreadSolves (G:Matrix U U ℝ)(p : POL U): foldsH (G:=G) p (spreadH G p) := (heat_exists G p).choose_spec
lemma givenSpread {G:Matrix U U ℝ}{p : POL U}{f:Scan U}(h:foldsH (G:=G) p f) : spreadH G p=f := definite G p (spreadSolves G p) h

/-- Ordinary Wick polynomial (retains all unpaired slots). -/
def glaze (G:Matrix U U ℝ) : POL U→ₗ[ℝ]POL U := (stopT 1).toLinearMap.comp (spreadH G)
lemma glazed (G:Matrix U U ℝ)(p : POL U) : glaze G p=stopT 1 (spreadH G p) := rfl
lemma glaze_constant (G:Matrix U U ℝ)(a:ℝ) : glaze G (C a)=C a := by rw [glazed,givenSpread (foldConstant ..)]; simp [stopT]
lemma glaze_one (G:Matrix U U ℝ) : glaze G 1=1 := by simpa using glaze_constant G 1
lemma glaze_deriv (G:Matrix U U ℝ)(p:POL U)(i:U) : glaze G (pderiv i p)= pderiv i (glaze G p) := by
  rw [glazed,givenSpread (foldPeel (spreadSolves G p) i),span_post,glazed]
lemma glaze_pin (G:Matrix U U ℝ)(p:POL U)(i:U) : glaze G (p*X i)=glaze G p*X i+∑ a,blend G i a • glaze G (pderiv a p) := by
  rw [glazed, givenSpread (foldBudding (spreadSolves G p) i),budding,map_add,map_mul,map_mul,seep,map_sum,glazed,stopT_X,stopT_X]; simp only [Option.elim_none,map_one,one_mul,Option.elim_some,map_smul,span_post]
  congr 1; apply Finset.sum_congr rfl; intro a _; rw [glaze_deriv,glazed]
/-- The Wick recursion knocking down one field (evaluating at zero
leaves only pairings). -/
theorem wick_poly (G:Matrix U U ℝ)(h:G.transpose=G)(p:POL U)(i:U) : glaze G (p*X i)=glaze G p*X i+∑ a,G i a • glaze G (pderiv a p) := by
  rw [glaze_pin]; congr 1; apply Finset.sum_congr rfl; intro a _; rw [blend,show G a i=G i a from congr_fun (congr_arg (fun M:Matrix _ _ ℝ=>M i) h) a]; congr 1; ring
end Blur
end YM.WilsonCoeffUV.Blue
