import YM.WilsonCoeffUV.Series.Filtered
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-! Formal real graded common calculus. Ordinary log coordinates. Exposes
X-preserving substitutions without restrictions at order zero on the *log*
variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open PowerSeries Function
open scoped BigOperators
variable {U V W R S : Type*}
abbrev POL (U:Type*) := MvPolynomial U ℝ
abbrev Ink (U:Type*) := PowerSeries (POL U)

section arrows
variable [CommRing R] [CommRing S] [Algebra ℝ R] [Algebra ℝ S]
-- enable coeffwise ops
/-- No algebraicity assumed, e.g. Wick. -/
def overlay (d:R→ₗ[ℝ]S) : PowerSeries R→ₗ[ℝ] PowerSeries S where
  toFun f := PowerSeries.mk fun i=> d (coeff i f)
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
@[simp] lemma overlay_apply (d:R→ₗ[ℝ]S) (f) (i : ℕ) : coeff i (overlay d f)=d (coeff i f) := coeff_mk i (fun j=>d (coeff j f))

/-- Lift coefficient derivation, X is independent -/
def blot (d:Derivation ℝ R R) : Derivation ℝ (PowerSeries R) (PowerSeries R) where
  toLinearMap := overlay d.toLinearMap
  map_one_eq_zero' := by ext n; rw [overlay_apply]; by_cases h:n=0 <;> simp [coeff_one,h]
  leibniz' f g := by
    ext i
    simp only [smul_eq_mul,map_add,overlay_apply,coeff_mul,map_sum]
    change ∑ j∈_, d _= _
    simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
    congr 1
    exact Finset.Nat.sum_antidiagonal_swap (f:=fun x=> (coeff x.1) g * d ((coeff x.2) f))
@[simp] lemma blot_apply (d:Derivation ℝ R R)(f)(i : ℕ) : coeff i (blot d f)=d (coeff i f) := overlay_apply d.toLinearMap f i
@[simp] lemma blot_C (d:Derivation ℝ R R)(r:R) : blot d (C r)= C (d r) := by ext n; simp only [blot_apply,coeff_C]; split_ifs <;> simp
@[simp] lemma blot_X (d:Derivation ℝ R R) : blot d X=0 := by ext n; rw [blot_apply,coeff_X]; split<;>simp
lemma blot_commute (d:Derivation ℝ R R)(f): blot d (derivative R f)= derivative R (blot d f) := by
  ext n; rw [coeff_derivative,blot_apply,blot_apply,coeff_derivative,Derivation.leibniz]; simp [mul_comm]
lemma blot_carry {f g:PowerSeries R} {k} (h:Equal k f g)(d:Derivation ℝ R R) : Equal k (blot d f) (blot d g) := by intro i hi; rw [blot_apply,blot_apply,h i hi]

lemma raise_diff [Algebra ℚ R] [IsAddTorsionFree R] {f:PowerSeries R}(h:constantCoeff f=0)(d : Derivation ℝ R R) : blot d (raiseE f)=raiseE f * blot d f := by
  let F:=raiseE f
  let u:=blot d (raiseE f)-raiseE f*blot d f
  have hu := raise_change h
  have hy : derivative R u=u*derivative R f := by
    rw [show u = _ - _ from rfl,map_sub, ←blot_commute, Derivation.leibniz,hu,Derivation.leibniz, smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul, blot_commute]; ring
  have hc : constantCoeff u=constantCoeff 0 := by
    have he g : constantCoeff (blot d g)=d (constantCoeff g):= by simpa only [coeff_zero_eq_constantCoeff_apply] using blot_apply d g 0
    unfold u; rw [map_sub,map_mul,he,he,h,raise_one h]; simp
  exact sub_eq_zero.mp (raise_unique _ hy (by simp) hc)
end arrows

/-- Log-coordinate substitution. -/
def train (φ:U→Ink V) : Ink U→+*Ink V := edit (MvPolynomial.aeval φ).toRingHom (x:=X) constantCoeff_X
@[simp] lemma train_C (φ:U→Ink V) (p:POL U) : train φ (C p)=MvPolynomial.aeval φ p := edit_C _ _ _
@[simp] lemma train_X (φ:U→Ink V) : train φ X=X := edit_X _ _
def path (i:U) : Ink U := C (MvPolynomial.X i)
@[simp] lemma train_path (φ:U→Ink V)(i:U) : train φ (path i)=φ i := by rw [path,train_C,MvPolynomial.aeval_X]

abbrev realS {U:Type*} := C.comp (MvPolynomial.C (σ:=U) (R:=ℝ))
lemma real_alg (r:ℝ) : algebraMap ℝ (Ink U) r=realS r := by
  -- tower
  rw [IsScalarTower.algebraMap_apply ℝ (POL U) (Ink U) r]; rfl
@[simp] lemma train_real (φ:U→Ink V)(r:ℝ) : train φ (realS r)=realS r := by rw [RingHom.comp_apply,train_C,MvPolynomial.aeval_C];exact real_alg r
lemma rail {f:Ink U→+*Ink V}(hx:f X=X)(hc:∀ r:ℝ,f (realS r)=realS r) : f=train (fun i=> f (path i)) := by
  apply serial_ext (by rw [hx,constantCoeff_X]) _ (by simp [hx]); intro p
  induction p using MvPolynomial.induction_on with
  | C a => rw [show C _ = realS _ from rfl,hc,train_real]
  | add p q a b => simp_rw [map_add,a,b]
  | mul_X p j a => rw [map_mul,map_mul f,map_mul,a,show C _=path j from rfl,train_path]
lemma through (φ:U→Ink V)(ψ:V→Ink W) : (train ψ).comp (train φ)= train (fun i=>train ψ (φ i)) := by
  simpa using! rail (f:=(train ψ).comp (train φ)) (by simp) (fun i=>by rw [RingHom.comp_apply,train_real,train_real])
lemma train_id : train (path (U:=U))= RingHom.id _ := by simpa using! (rail (f:=RingHom.id (Ink U)) rfl (fun _=>rfl)).symm
lemma train_smul (φ:U→Ink V)(c:ℝ)(u:Ink U) : train φ (c • u) = c • train φ u := by rw [Algebra.smul_def,Algebra.smul_def,map_mul,real_alg,train_real,real_alg]
lemma compose_vars (φ: U → POL V) : PowerSeries.map (MvPolynomial.aeval φ).toRingHom = train (C ∘ φ) := by
  have h (i:U) : PowerSeries.map (MvPolynomial.aeval φ).toRingHom (path i) = C (φ i) := by simp [path]
  simpa only [h,Function.comp_def] using! (rail (f:=PowerSeries.map (MvPolynomial.aeval φ).toRingHom) (by simp) (fun r=> by
    change PowerSeries.map _ (C _) = C _; rw [map_C]; congr 1; exact MvPolynomial.aeval_C ..))

abbrev brush (i:U) : Derivation ℝ (Ink U) (Ink U) := blot (MvPolynomial.pderiv i)
@[simp] lemma brush_path [DecidableEq U](i j:U) : brush i (path j) = if j=i then 1 else 0 := by
  rw [brush,path,blot_C]; by_cases h:j=i <;> simp [h]
lemma poly_commute (i j : U)(p:POL U) : MvPolynomial.pderiv i (MvPolynomial.pderiv j p)=MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  by_cases h:j=i
  · subst j;rfl
  apply MvPolynomial.ext; intro n
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply,Finsupp.single_eq_of_ne h,Finsupp.single_eq_of_ne (Ne.symm h), add_zero,
    add_right_comm n (Finsupp.single j 1) (Finsupp.single i 1)]
  ring
lemma brush_comm (i j:U)(f:Ink U) : brush i (brush j f)=brush j (brush i f) := by ext1; simp only [brush,blot_apply,poly_commute i j]

section chain
variable [Fintype U] (φ:U→Ink V)(j:V)
private lemma car_aux (p : POL U) : brush j (train φ (C p))=∑ i, brush j (φ i)*train φ (brush i (C p)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [show PowerSeries.C (MvPolynomial.C a)=realS a from rfl, train_real]
    simp [realS,brush]
  | add p q hp hq => simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
  | mul_X p u hp =>
    simp only [map_mul (C (R:=POL U)),show C (MvPolynomial.X u)=path u from rfl,
      Derivation.leibniz, smul_eq_mul,map_mul,map_add,train_path, hp]
    simp only [mul_add,Finset.sum_add_distrib,brush_path]
    congr 1
    · rw [Finset.sum_eq_single u];
      · simp; ring
      · intro i _ h; rw [if_neg h.symm,map_zero]; ring
      simp
    simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma reroutes (f:Ink U) : brush j (train φ f)=∑ i,brush j (φ i)*train φ (brush i f) := by
  classical
  apply PowerSeries.ext; intro n
  have hv : constantCoeff (train φ X)=0 := by simp
  have hy := shave f (n+1)
  rw [blot_carry (filtered hv hy) (MvPolynomial.pderiv j) n n.lt_succ_self]
  let A:= Finset.range (n+1)
  simp only [map_sum]
  conv_rhs =>
    enter [2,i]; rw [((Equal.refl _ _).mul (filtered hv (blot_carry hy _))) n n.lt_succ_self]; simp only [map_sum,mul_pow]
  -- use chain proof per monomial
  simp only [map_mul,map_pow,train_X,Derivation.leibniz,brush,smul_eq_mul,Finset.mul_sum,map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [←map_sum]; simp only [map_mul,map_pow,train_X,Derivation.leibniz_pow,blot_X,smul_zero,mul_zero,zero_add]; congr 1; apply blas
where
  blas (φ:U→Ink V)(m : ℕ)(p:POL U) :
      X^m*brush j (train φ (C p))=∑ i,brush j (φ i)*(X^m*train φ (brush i (C p))) := by rw [car_aux,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
end chain
end YM.WilsonCoeffUV.Blue
