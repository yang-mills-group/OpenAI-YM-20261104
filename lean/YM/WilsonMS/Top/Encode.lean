import YM.WilsonMS.Top.Pull
import YM.Next.RANK.Gaussian
import YM.XSpace.VertexTaylor

/-!
# Matching the two Wick calculators

Link `Koszul.Raw … ℂ`, with all letters even here, to MvPolynomial.
Repeated (ordinary) derivative encoding. Use it on **coefficient
polynomials**, no finiteness assumptions on total perturbative degree.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Symbols
open XSpace Next.Rank.Normal Function Filter Set Finset
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Book MS.Book.Convolve MS.Swirl MS.Orbit
  MS.Orbit.Cog
open scoped Topology ContDiff

variable {I E : Type} {p q : poly I}

abbrev plain (I : Type) : Sector I := fun _ => false

open Classical in
noncomputable def modeD (i : I) :=
  (slit (Pi.single i 1)).toLinearMap

def derivativeL : List I → poly I →ₗ[ℂ] ℂ
  | [] => (MvPolynomial.aeval (0 : I → ℂ)).toLinearMap
  | i :: l => (derivativeL l).comp (modeD i)

def encode (I : Type) : poly I →ₗ[ℂ] Raw I ℂ :=
  LinearMap.pi derivativeL

lemma encode_nil (P : poly I) : encode I P [] = MvPolynomial.aeval (0 : I → ℂ) P :=
  rfl

lemma encode_derivative (P : poly I) (i : I) : D i (encode I P) = encode I (modeD i P) :=
  rfl

lemma encode_const (x : ℂ) : encode I (MvPolynomial.C x) = coin x := by
  apply ext_D
  · exact MvPolynomial.aeval_C ..
  intro i
  rw [encode_derivative, modeD, Derivation.coeFn_coe, slit_C, map_zero, coin_nod]

lemma encode_var (x : I) : encode I (MvPolynomial.X x) = atLetter x := by
  apply ext_D
  · exact MvPolynomial.aeval_X ..
  intro i
  classical
  rw [encode_derivative, modeD, Derivation.coeFn_coe, slit_X, encode_const]
  by_cases ht : i = x
  · subst i
    rw [hear, Pi.single_eq_same]
  rw [Pi.single_eq_of_ne (Ne.symm ht), unheard _ ht]
  funext l
  cases l <;> rfl

lemma encode_product (P Q : poly I) :
    encode I (P * Q) = product (plain I) (encode I P) (encode I Q) := by
  ext l
  induction l generalizing P Q with
  | nil => rw [encode_nil, nil_product, map_mul, encode_nil, encode_nil]
  | cons x l ih =>
    rw [D_eval x (encode I (P * Q)), encode_derivative, D_eval x (product _ _ _), D_product,
      encode_derivative, encode_derivative,
      (show Koszul.sign (plain I) (plain I x) (encode I P) = _ from sign_id _ _)]
    have he : modeD x (P * Q) = modeD x P * Q + P * modeD x Q := by
      unfold modeD
      simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
      ring
    rw [he, map_add, Pi.add_apply, Pi.add_apply, ih, ih]

lemma polynomial_input (P : poly I) : encode I P ∈ FeeP (plain I) := by
  induction P using MvPolynomial.induction_on with
  | C y =>
    rw [encode_const]
    exact ⟨coin_symm _, (minH (coinN _))⟩
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | mul_X x i h =>
    rw [encode_product, encode_var]
    exact fee_pair h ⟨speaks_s _, minH (letterN _)⟩

lemma encode_t (F : I → ℂ) (P : poly I) [Fintype I] : slit F P = ∑ i : I, F i • modeD i P := by
  classical
    induction P using MvPolynomial.induction_on with
  | C a =>
    unfold modeD
    simp only [Derivation.coeFn_coe, slit_C, smul_zero, Finset.sum_const_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
  | mul_X P i ih =>
    rw [mul_comm P, slit_prod, ih]
    let Y := MvPolynomial.X (R := ℂ) i
    let p (j : I) : I → ℂ := open Classical in Pi.single j (1 : ℂ)
    have hX j : modeD j (Y * P) = Y * modeD j P + MvPolynomial.C (p j i) * P :=
      slit_prod (b := p j) ..
    unfold Y at hX
    simp_rw [hX, smul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply congr_arg₂ (· + ·)
    · apply sum_congr rfl
      intro j _
      rw [mul_smul_comm]
    rw [Finset.sum_eq_single_of_mem i (mem_univ _), show p i i = 1 from Pi.single_eq_same _ _,
      map_one, one_mul, MvPolynomial.C_mul']
    intro j _ hj
    rw [show p j i = 0 from Pi.single_eq_of_ne hj.symm _, map_zero, zero_mul, smul_zero]

section Wick
variable [Fintype I] (K : Grain I) (Q : Next.Rank.Normal.Symmetric I) (h : Cog.Sym (plain I) K)
  (he : Q.cov = Chill K)

/-- Stability under taking more derivatives. -/
private def agrees (n : ℕ) : Submodule ℂ (poly I) :=
  match n with
  | 0 => LinearMap.ker ((View K).comp (encode I) - blend Q 0)
  | n + 1 => ⨅ f : I → ℂ, (agrees n).comap (slit f).toLinearMap

private lemma eligible_zero (P : poly I) : P ∈ agrees K Q 0 ↔ View K (encode I P) = blend Q 0 P := by
  rw [agrees]
  exact sub_eq_zero

private lemma eligible (P : poly I) (n : ℕ) :
    P ∈ agrees K Q (n + 1) ↔ ∀ f : I → ℂ, slit f P ∈ agrees K Q n := by
  rw [agrees]
  exact Submodule.mem_iInf _

include h he in
private lemma multiply_X {P : poly I} (hc : ∀ n, P ∈ agrees K Q n) (n : ℕ) (i : I) :
    MvPolynomial.X i * P ∈ agrees K Q n := by
  induction n generalizing P with
  | zero =>
    have hv := fee_spec (polynomial_input P)
    rw [eligible_zero, blended, Pi.zero_apply, zero_mul, zero_add, encode_product, encode_var,
      ibpV i (fun _ _ _ => rfl : Clear (plain I) K) h hv.1 hv.2]
    simp_rw [← (eligible_zero K Q _).mp ((eligible K Q P 0).mp (hc 1) (Q.cov i)), encode_t (Q.cov i),
      map_sum, map_smul, ← encode_derivative, he]
    rfl
  | succ n ih =>
    apply (eligible K Q _ _).2
    intro f
    rw [slit_prod, MvPolynomial.C_mul']
    apply Submodule.add_mem
    · exact ih (fun t => (eligible K Q _ _).mp (hc (t + 1)) f)
    exact Submodule.smul_mem _ _ (hc n)

include h he in
theorem wick_row (P : poly I) : View K (encode I P) = blend Q 0 P := by
  suffices H : ∀ n, P ∈ agrees K Q n by exact (eligible_zero K Q _).mp (H _)
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro n
    cases n with
    | zero =>
      rw [eligible_zero, encode_const, blend_components, fine, minView]
      simp
    | succ n => exact (eligible K Q _ _).2 (fun f => slit_C f a |>.symm ▸ Submodule.zero_mem _)
  | add p q hp hq => exact fun n => Submodule.add_mem _ (hp n) (hq n)
  | mul_X P i ih =>
    rw [mul_comm P]
    exact fun n => multiply_X K Q h he ih n i
end Wick

section Taylor
open Module
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable (B : Basis I ℝ E) (f : E → ℝ) (h : germ f)
open XSpace.Taylor
include h

lemma divided_rec (n : ℕ) :
    Taylor.divided B (n + 1) (Complex.ofRealCLM ∘ f) =
      ((↑(n + 1 : ℕ) : ℂ)⁻¹) •
        ∑ j : I, MvPolynomial.X j * Taylor.divided B n (Complex.ofRealCLM ∘ layer (B j) f) := by
  apply from_real B
  intro x
  have he : germ (fderiv ℝ f) := h.fderiv_right (m := ω) (by simp)
  let T := iteratedFDeriv ℝ n (fderiv ℝ f) 0 (fun _ => x)
  have hp (j : I) : iteratedFDeriv ℝ n (layer (B j) f) 0 (fun _ => x) = T (B j) := by
    let V : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ
    change iteratedFDeriv ℝ n ((V (B j)) ∘ (fderiv ℝ f)) 0 _ = _
    rw [(V (B j)).iteratedFDeriv_comp_left he (by exact le_top)]
    rfl
  rw [map_smul, map_sum, divided_realEval _ _ f (h.of_le le_top), iteratedFDeriv_succ_apply_right,
    show iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) 0 (Fin.init (fun _ : Fin (n + 1) => x)) x = T x
      from rfl,
    smul_eq_mul]
  conv_lhs => rw [← B.sum_repr x, map_sum]; simp only [map_smul, smul_eq_mul]
  have hK : ((↑(n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp_rw [map_mul, Taylor.divided_realEval B n (layer _ f) ((germ_layer h _).of_le le_top), hp]
  rw [Nat.factorial_succ]
  push_cast
  simp_rw [Finset.mul_sum,
    show ∀ j : I, evalAt B x (MvPolynomial.X j) = _ from fun j =>
      (show evalAt B x (MvPolynomial.X j) = (↑(B.repr x j) : ℂ) from MvPolynomial.aeval_X ..)]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_inv]
  ring

lemma encode_expansion (n : ℕ) :
    encode I (Taylor.divided B n (Complex.ofRealCLM ∘ f)) = mask n (ink B f) := by
  induction n generalizing f with
  | zero =>
    rw [Taylor.divided_zero, encode_const]
    ext l
    cases l with
    | nil => simp [coin, enough]
    | cons i l =>
      symm
      exact
        strange _
          (by
            push_cast
            simp
            omega)
  | succ n ih =>
    have hT := rankMod (ink (A := I) B f) (↑(n + 1 : ℕ))
    let K := mask (↑(n + 1 : ℕ)) (ink B f)
    have hv : ∀ i : I, D i K = mask n (ink B (layer (B i) f)) := by
      intro i
      unfold K
      rw [Book.conn, inktip]
      norm_num
    have hm :=
      rank_euler (p := plain I)
        (mask_symmetric _ (ink_s _ (p := plain I) (fun _ he => Bool.noConfusion he) h)) hT
    rw [divided_rec B f h, _root_.map_smul, map_sum]
    simp_rw [encode_product, encode_var, ih (layer _ f) (germ_layer h _)]
    simp_rw [← hv]
    rw [show (∑ i, _) = _ from hm.symm,
      inv_smul_smul₀ (by exact_mod_cast Nat.succ_ne_zero n : (↑(n + 1 : ℕ) : ℂ) ≠ 0)]
end Taylor
end YM.WilsonMS.Symbols
