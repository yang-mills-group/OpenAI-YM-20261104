import YM.RG3.Pan.Hymn
/-!
# Scalar and tensor payloads of the small chart

Use paid bills for ordered jets on either inputs or path-alignment changes.
Here bring valuation powers back on composition with a physical small
coordinate by an actual Fréchet calculation; retain the profile multipliers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Function FreeResolvent TestD
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {E F Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {k : ℕ}

lemma Bill.duo (P : F→L[ℝ] Y→L[ℝ] Z) {A B C d:ℝ} {f:E→F} {g:E→Y} {x:E}
    (hP : ∀ x y,‖P x y‖ ≤ C*‖x‖*‖y‖)
    (hf : Bill k A d f x) (hg : Bill k B d g x) (hC : 0 ≤ C) (hd : 0 ≤ d) :
    Bill k (2^k*(C*A*B)) d (fun z=>P (f z) (g z)) x := by
  have hA:=hf.pos; have hB:=hg.pos
  refine ⟨TestD.smooth_product P hf.smooth hg.smooth,fun i hi=>?_⟩
  apply FreeResolvent.Affine.list_op (by positivity); intro l v hl hv
  rw [TestD.leibniz v P _ (hf.smooth.of_le (Nat.cast_le.mpr (hl.trans_le hi))) (hg.smooth.of_le (by exact_mod_cast hl.trans_le hi))]
  have e (L : List (Fin i)){φ : E→F} : ‖jet v φ L x‖ ≤ ‖iteratedFDeriv ℝ L.length φ x‖ := by
    refine (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (m:=(v ∘ L.get)) (fun j=> hv (L.get j))).trans_eq ?_
    simp
  have e' (L : List (Fin i)){φ : E→Y} : ‖jet v φ L x‖ ≤ ‖iteratedFDeriv ℝ L.length φ x‖ := by
    refine (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (m:=(v ∘ L.get)) (fun j=> hv (L.get j))).trans_eq ?_
    simp
  have he (m : Masks l) : ‖P (jet v f (lo l m) x) (jet v g (TestD.hi l m) x)‖ ≤ (C*A*B)*d^i := by
    let p:=(lo l m).length; let r:=(TestD.hi l m).length
    have hp : p+r=i:=(TestD.lengths l m).trans hl
    refine (hP _ _).trans ((mul_le_mul (mul_le_mul_of_nonneg_left ((e _).trans (hf.B p (by omega))) hC)
      ((e' _).trans (hg.B r (by omega))) (norm_nonneg _) (by positivity)).trans_eq ?_)
    rw [← hp,pow_add]; ring
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> he i)).trans ?_)
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,TestD.card]
  refine (mul_le_mul_of_nonneg_right (show (↑(2^l.length:ℕ):ℝ) ≤ 2^k by exact_mod_cast pow_le_pow_right₀ (by norm_num : 1≤(2:ℕ)) (hl.trans_le hi)) ?_).trans_eq (by ring); positivity
lemma Bill.times {A B d:ℝ} {T : Type*} [NormedRing T] [NormedAlgebra ℝ T] {f g:E→T} {x:E}
    (hf : Bill k A d f x) (hg : Bill k B d g x) (hd : 0 ≤ d) :
    Bill k (2^k*(A*B)) d (fun z=> f z*g z) x:= by
  convert (Bill.duo (ContinuousLinearMap.mul ℝ T) (C:=1) _ hf hg zero_le_one hd) using 2
  · rw [one_mul]
  · rfl
  intro x y; rw [one_mul]; exact norm_mul_le ..

variable {r : ℕ} {A d τ ε C : ℝ} {y : E} {g : E→F} {f : F→Y}

/-- Bill on the *full* map through the physical curvature palette, where
`g y` is small. Buying each higher variation of the palette (with t per
external variation) allows composition with a small-jet budget on the
palette map f. Return Bill for *unscaled* tests---division by any
threshold power must be charged on the returned fee. `d` must cover each
palette variation price per external occurrence in its test stencil; may
worsen by the hull length. -/
def erent (k r : ℕ) (A d τ ε C : ℝ): ℝ:= joinFee k * (1+A)^k * (1+d)^k * (C*τ^r+r*ε)
lemma erent_nn (k r : ℕ) (hA : 0 ≤ A) (hd : 0 ≤ d) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hC : 0 ≤ C) : 0 ≤ erent k r A d τ ε C:= by have:=joinFee_nn k; unfold erent; positivity

lemma Bill.resonance (hg : Bill k A (d*τ) g y) (hy : ‖g y‖ ≤ τ) (hf : Axial.Ordinary f r k τ ε C) (hd : 0 ≤ d):
    Bill k (erent k r A d τ ε C) 1 (f ∘ g) y:= by
  have ht:=hf.tau; have hc:=hf.small; have hd':=hf.high; have hA:=hg.pos
  let N:=C*τ^r+(r:ℝ)*ε; have hN : 0≤N:=by unfold N; positivity
  have he:=hf.germ (g y) hy
  refine ⟨he.comp _ hg.smooth,fun j hj=>?_⟩
  rw [iteratedFDeriv_comp he hg.smooth (Nat.cast_le.mpr hj),FormalMultilinearSeries.taylorComp,one_pow,mul_one]
  let F0(n):=iteratedFDeriv ℝ n f (g y); let J(n):=iteratedFDeriv ℝ n g y
  have hx (p : OrderedFinpartition j): ‖p.compAlongOrderedFinpartition (F0 p.length) (fun i=>J (p.partSize i))‖ ≤ (1+A)^k*(1+d)^k*N:= by
    refine (p.norm_compAlongOrderedFinpartition_le ..).trans ((mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> hg.B _ ((p.partSize_le i).trans hj))) (norm_nonneg _)).trans ?_)
    let I:ℝ:=‖F0 p.length‖; have hI:0≤I:=norm_nonneg _; have hz:=p.length_le
    rw [factors, mul_pow, show τ^j= τ^p.length*τ^(j-p.length) from by rw [← pow_add,Nat.add_sub_cancel' hz]]
    have hm : I*τ^p.length ≤ N:= hf.cover (g y) hy (p.length_le.trans hj)
    have ha' : A^p.length ≤ (1+A)^k:= (pow_le_pow_left₀ hA (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hA) (hz.trans hj))
    have hc' : d^j ≤ (1+d)^k:= (pow_le_pow_left₀ hd (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hd) hj)
    calc
      _ = A^p.length*d^j*τ^(j-p.length)*(I*τ^p.length) := by unfold I; ring
      _ ≤ (1+A)^k*(1+d)^k*1*N:= by gcongr; exact pow_le_one₀ ht hf.below
      _ = _:= by rw [mul_one]
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>hx i)).trans ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right (joinFee_ge k j hj) ?_).trans_eq ?_
  · positivity
  unfold erent N; ring
end YM.RG3.Pan
