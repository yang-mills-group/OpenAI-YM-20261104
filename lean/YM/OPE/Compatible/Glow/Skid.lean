import YM.OPE.Compatible.Glow.Gear
/-!
# Jet cost by stencil lengths
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{b:ℝ}
namespace Script
open Page
abbrev pricePoints (p:Chant G n):Finset (Cover × Shade G):= ((cashX p) ×ˢ univ).image (fun i:(Edge Cover)× G.ColorIndex=> (i.1.1,i.1.2,i.2))
abbrev Stall (p:Chant G n):= pricePoints p→ℝ -- sup ℓ
abbrev collectQ (p:Chant G n):fieldX (Shade G) →ₗ[ℝ] Stall p:= LinearMap.pi (fun i => LinearMap.proj i.val)
noncomputable def offerQ (p:Chant G n): Stall p→ₗ[ℝ] fieldX (Shade G):= LinearMap.pi (fun i=> if h:i∈pricePoints p then LinearMap.proj (⟨i,h⟩:pricePoints p) else 0)
def permit (p:Chant G n) (x:Stall p):= verseX p (lotU (offerQ p x))
lemma permit_atom (p:Chant G n)(x:fieldX (Shade G)): permit p (collectQ p x)=verseX p (lotU x):=by
   apply cashSafe; intro z (hz:z∈cashX p); apply congr_arg G.lieExp; ext i; change offerQ p _ (z.1,z.2,i)=_
   let t:Cover × Shade G:= (z.1,z.2,i); have he:t∈pricePoints p:=mem_image.mpr ⟨(z,i),mem_product.mpr ⟨hz,mem_univ _⟩,rfl⟩
   erw [offerQ,LinearMap.pi_apply,dif_pos he]; rfl
lemma permitS (p:Chant G n):ContDiff ℝ ⊤ (permit p):=by
   have he (i:Edge Cover): ContDiff ℝ ⊤ (fun x:Stall p=> G.mat (lotU (offerQ p x) i)):=by
       let f:Stall p→L[ℝ] G.Mat:= (G.colorMat∘ₗ indexS i∘ₗ offerQ p).toContinuousLinearMap
       have h:(fun x:Stall p=> G.mat (lotU (offerQ p x) i))=(fun t=>NormedSpace.exp (f t)):=funext fun i=> G.mat_lieExp _; rw [h]; fun_prop
   have hv (w:Walk)(i:Cover): ContDiff ℝ ⊤ (fun x:Stall p=> G.mat (travel (lotU (offerQ p x)) i w)):=by
       induction w generalizing i with
       | nil=> exact contDiff_const
       | cons a w ih=>
          simp only [travel,G.mat_mul, Step.read]; cases h:a.neg; · simp only [Bool.false_eq_true,↓reduceIte]; apply ContDiff.mul (he _) (ih _)
          simp only [if_true,G.mat_inv]; exact ((starL' ℝ).contDiff.comp (he _)).mul (ih _)
   unfold permit verseX; apply contDiff_prod; intro i _; exact (p i).f.contDiff.comp ((hv _ 0).sub (g:=fun _=>1) contDiff_const)
lemma lettersOne (G:Gauge)(n r:ℕ)(s D:ℝ)(hs:0<s)(hp:0 ≤ D):∃ A:ℝ,0≤A ∧∀ p:Chant G n,moderateX p D→∀ v:Fin r→Stall p,(∀ i,‖v i‖≤1)→‖Tensor.coeff (permit p) r 0 v‖≤ A*Real.exp (s*lawn p):=by
    obtain ⟨C,K,hC,hK,H⟩:= limelight r
    let k:ℝ:= K*Fintype.card G.ColorIndex; have h:0≤k:=mul_nonneg hK (Nat.cast_nonneg _)
    obtain ⟨A,ha,P⟩:=cashBill G n _ _ _ hs h hp r
    refine ⟨C*A,mul_nonneg hC ha,fun p ht v hv=>?_⟩; let T:=Tensor.coeff (permit p) r 0; have he(x:Stall p)(hx:‖x‖≤K): ‖Tensor.diagonal T x‖≤ A*Real.exp (s*lawn p):=by
       rw [← WardBin.leading_tensor x _ ((permitS p).contDiffAt.of_le le_top)]; let f(t:ℝ):=permit p (t • x); have hu(i:Edge Cover)(hi:i∈cashX p) : ‖indexS i (offerQ p x)‖ ≤ k:=by
           let w:=indexS i (offerQ p x); let e:=EuclideanSpace.basisFun G.ColorIndex ℝ
           have he(j:G.ColorIndex):‖e.repr w j‖≤K:=by
              change ‖(e.repr (indexS i (offerQ p x))) j‖≤_; let v:Cover × Shade G:= (i.1,i.2,j); have hy:v∈pricePoints p := mem_image.mpr ⟨(i,j),mem_product.mpr ⟨hi,mem_univ _⟩,rfl⟩; change ‖offerQ p x v‖≤_; erw [offerQ,LinearMap.pi_apply,dif_pos hy]; exact (norm_le_pi_norm x ⟨v,hy⟩).trans hx
           change ‖w‖≤_; conv_lhs => rw [← e.sum_repr w]
           apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=>K) (fun i _=> by rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; exact he i)).trans_eq; unfold k; rw [sum_const,nsmul_eq_mul,card_univ,mul_comm]
       have hE : f=fun t=>verseX p (lotU (t • offerQ p x)):=funext fun t=>by unfold f permit; rw [map_smul]
       unfold WardBin.leading; change ‖(r.factorial:ℝ)⁻¹ • iteratedDeriv r f _‖≤_; rw [hE,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Real.norm_natCast];exact inv_le_one_of_one_le₀ (by exact_mod_cast r.factorial_pos))).trans (P p _ ht hu 0)
    rw [mul_assoc]; exact H (Stall p) T _ (Tensor.coeff_symm ((permitS p).contDiffAt.of_le le_top)) (by positivity) he _ hv
end Script
end YM.OPE.Flume
