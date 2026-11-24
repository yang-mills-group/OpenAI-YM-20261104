import YM.OPE.Compatible.Grid.Lucre
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
lemma permPo (G:Gauge)(n r:ℕ)(D:ℝ)(hp:0 ≤ D):∃ A:ℝ,0≤A ∧∀ p:Chant G n,moderateX p D→∀ v:Fin r→Stall p,(∀ i,‖v i‖≤1)→‖Tensor.coeff (permit p) r 0 v‖≤ A*(lawn p+1:ℝ)^r:=by
    obtain ⟨C,K,hC,hK,H⟩:= limelight r
    let k:ℝ:= K*Fintype.card G.ColorIndex; have h:0≤k:=mul_nonneg hK (Nat.cast_nonneg _)
    obtain ⟨A,ha,P⟩:=ozone G n _ _ h hp r
    refine ⟨C*A,mul_nonneg hC ha,fun p ht v hv=>?_⟩; let T:=Tensor.coeff (permit p) r 0; have he(x:Stall p)(hx:‖x‖≤K): ‖Tensor.diagonal T x‖≤ A*(lawn p+1:ℝ)^r:=by
       rw [← WardBin.leading_tensor x _ ((permitS p).contDiffAt.of_le le_top)]; let f(t:ℝ):=permit p (t • x); have hu(i:Edge Cover)(hi:i∈cashX p) : ‖indexS i (offerQ p x)‖ ≤ k:=by
           let w:=indexS i (offerQ p x); let e:=EuclideanSpace.basisFun G.ColorIndex ℝ
           have he(j:G.ColorIndex):‖e.repr w j‖≤K:=by
              change ‖(e.repr (indexS i (offerQ p x))) j‖≤_; let v:Cover × Shade G:= (i.1,i.2,j); have hy:v∈pricePoints p := mem_image.mpr ⟨(i,j),mem_product.mpr ⟨hi,mem_univ _⟩,rfl⟩; change ‖offerQ p x v‖≤_; erw [offerQ,LinearMap.pi_apply,dif_pos hy]; exact (norm_le_pi_norm x ⟨v,hy⟩).trans hx
           change ‖w‖≤_; conv_lhs => rw [← e.sum_repr w]
           apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=>K) (fun i _=> by rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; exact he i)).trans_eq; unfold k; rw [sum_const,nsmul_eq_mul,card_univ,mul_comm]
       have hE : f=fun t=>verseX p (lotU (t • offerQ p x)):=funext fun t=>by unfold f permit; rw [map_smul]
       unfold WardBin.leading; change ‖(r.factorial:ℝ)⁻¹ • iteratedDeriv r f _‖≤_; rw [hE,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Real.norm_natCast];exact inv_le_one_of_one_le₀ (by exact_mod_cast r.factorial_pos))).trans (P p _ ht hu 0)
    rw [mul_assoc]; exact H (Stall p) T _ (Tensor.coeff_symm ((permitS p).contDiffAt.of_le le_top)) (by positivity) he _ hv
lemma coffP (G:Gauge)(n r:ℕ)(D:ℝ)(m:ℕ)(hd:0≤D): ∃ B:ℝ,0 ≤ B∧ ∀ p:Chant G n, moderateX p D→ soot m (coff p r) (B*(lawn p+1:ℝ)^(m+2*r)):=by
    obtain ⟨A,hA,H⟩:= permPo G _ r _ hd
    let N:ℕ:=Fintype.card G.ColorIndex; let t:ℝ:=r+1; have ht:0 ≤ t:=by unfold t; positivity
    let B:= (N:ℝ)^r * t^m * A
    refine ⟨B,by unfold B; positivity,fun p h=>?_⟩; let f:=coff p r; have hp(i:Page _ r)(hi:i∉rim p r):figure m i*‖coff p r i‖=0:=by rw [stair p hi,norm_zero,mul_zero]
    refine ⟨fun i=> mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _),summable_of_ne_finset_zero hp,?_⟩; let L:ℝ:=1+lawn p; have hL:1 ≤ L:=by exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    let E:= (lawn p+1:ℝ)^r; have he:0 ≤ E:=by unfold E; positivity
    have hv i(hh:i∈rim p r):figure m i*‖coff p r i‖≤ (t*L)^m*(A*E):=by
       have hP:‖coff p r i‖≤ A*E:=H p h _ (fun j=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k=>by
            change ‖Pi.single (M:=fun _=>ℝ) (i j) 1 k.val‖≤1; by_cases he:k.val=i j<;>simp [he])
       have hq : figure m i≤(t*L)^m:=by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _); apply le_trans (Nat.cast_le.mpr (rimS p i hh)); unfold L t; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]; nlinarith only [Nat.cast_nonneg (α:=ℝ) (lawn p),Nat.cast_nonneg (α:=ℝ) r]
       exact mul_le_mul hq hP (norm_nonneg _) (by positivity)
    let c i:=figure m i*‖coff p r i‖; change (∑' i,c i) ≤ _; rw [tsum_eq_sum hp]; apply (sum_le_sum hv).trans; rw [sum_const,nsmul_eq_mul]; let w:=(t*L)^m*(A*E); have hw:0 ≤ w:=by unfold w; positivity
    have hg : ((rim p r).card:ℝ)≤ ((N:ℝ)*L)^r:=by
        rw [rim, Fintype.card_piFinset]; let y:ℕ:= (mold p).card; change ((↑(∏ i:Fin r,y)):ℝ) ≤ _; rw [prod_const,card_univ,Fintype.card_fin,Nat.cast_pow]; apply pow_le_pow_left₀ (Nat.cast_nonneg _); apply (Nat.cast_le.mpr (circling p)).trans; unfold L N; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card G.ColorIndex)]
    apply (mul_le_mul_of_nonneg_right hg hw).trans; apply le_of_eq; unfold w L B E; rw [mul_pow,mul_pow,pow_add,two_mul,pow_add]; ring
end Script
end YM.OPE.Flume
