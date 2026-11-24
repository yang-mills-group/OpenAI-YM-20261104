import YM.OPE.Compatible.Glow.Skid
/-! # Snow weights on point kernels -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{b:ℝ}
namespace Script
open Page
abbrev mold (p:Chant G n):= pricePoints p
def coff (p:Chant G n)(r:ℕ)(i:Page (Shade G) r):ℝ:=Tensor.coeff (permit p) r 0 (fun j=>collectQ p (Pi.single (i j) 1))
abbrev rim (p:Chant G n) (r:ℕ):= Fintype.piFinset fun _:Fin r=> mold p
lemma mould {p:Chant G n}{i:Cover×Shade G}(h:i∈mold p):size i.1 ≤ lawn p:= by obtain ⟨⟨q,y⟩,hx,rfl⟩:=mem_image.mp h; exact cashSize _ _ (mem_product.mp hx).1
lemma circling (p:Chant G n) : (mold p).card ≤ lawn p * Fintype.card G.ColorIndex:= card_image_le.trans (((Finset.card_product ..).trans (congr_arg _ card_univ)).trans_le (Nat.mul_le_mul_right _ (cashCard _)))
lemma rimS (p:Chant G n)(v: Page _ r)(hv:v∈rim p r): notch v.xy ≤ 1+r*lawn p:=by
    change stamp v ≤ _; rw [perimeter v]; apply Nat.add_le_add_left _ 1; exact (sum_le_sum fun i _=>mould (Fintype.mem_piFinset.mp hv i)).trans_eq (by rw [Finset.sum_const, card_univ,nsmul_eq_mul,Fintype.card_fin];rfl)
lemma stair (p:Chant G n) {v:Page _ r}(hv:v∉rim p r): coff p r v=0:=by
    obtain ⟨i,hi⟩:=not_forall.mp (show ¬ ∀ i,v i∈mold p from fun t=>hv (Fintype.mem_piFinset.mpr t)); unfold coff; apply ContinuousMultilinearMap.map_coord_zero _ i; ext y; change Pi.single (M:=fun _=>ℝ) (v i) _ y.val=0; exact Pi.single_eq_of_ne (fun (h:y.val = v i)=> hi (h ▸ y.property)) _
lemma coff_price (G:Gauge)(n r:ℕ)(s D:ℝ)(m:ℕ)(hs:0<s)(hd:0≤D): ∃ B:ℝ,0 ≤ B∧ ∀ p:Chant G n, moderateX p D→ soot m (coff p r) (B*Real.exp (s*lawn p)):=by
    obtain ⟨A,hA,H⟩:= lettersOne G _ r (s/2) _ (by positivity) hd
    let N:ℕ:=Fintype.card G.ColorIndex; let t:ℝ:=r+1; let Q:= widthCost (s/2) (m+r); have ht:0 ≤ t:=by unfold t; positivity
    let B:= (N:ℝ)^r * t^m * A * Q; have hq:1≤Q:=widthCost_ge (by positivity) _ -- lemma cost for any n input from Lift
    refine ⟨B,by unfold B; positivity,fun p h=>?_⟩; let f:=coff p r; have hp(i:Page _ r)(hi:i∉rim p r):figure m i*‖coff p r i‖=0:=by rw [stair p hi,norm_zero,mul_zero]
    refine ⟨fun i=> mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _),summable_of_ne_finset_zero hp,?_⟩; let L:ℝ:=1+lawn p; have hL:1 ≤ L:=by exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    let E:= Real.exp (s/2*lawn p); have he: 0 ≤ E:=(Real.exp_pos _).le; have hv i(hh:i∈rim p r):figure m i*‖coff p r i‖≤ (t*L)^m*(A*E):=by
       have hP:‖coff p r i‖≤ A*E:=H p h _ (fun j=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k=>by
            change ‖Pi.single (M:=fun _=>ℝ) (i j) 1 k.val‖≤1; by_cases he:k.val=i j<;>simp [he])
       have hq : figure m i≤(t*L)^m:=by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _); apply le_trans (Nat.cast_le.mpr (rimS p i hh)); unfold L t; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]; nlinarith only [Nat.cast_nonneg (α:=ℝ) (lawn p),Nat.cast_nonneg (α:=ℝ) r]
       exact mul_le_mul hq hP (norm_nonneg _) (by positivity)
    let c i:=figure m i*‖coff p r i‖; change (∑' i,c i) ≤ _; rw [tsum_eq_sum hp]; apply (sum_le_sum hv).trans; rw [sum_const,nsmul_eq_mul]; let w:=(t*L)^m*(A*E); have hw:0 ≤ w:=by unfold w; positivity
    have hg : ((rim p r).card:ℝ)≤ ((N:ℝ)*L)^r:=by
        rw [rim, Fintype.card_piFinset]; let y:ℕ:= (mold p).card; change ((↑(∏ i:Fin r,y)):ℝ) ≤ _; rw [prod_const,card_univ,Fintype.card_fin,Nat.cast_pow]; apply pow_le_pow_left₀ (Nat.cast_nonneg _); apply (Nat.cast_le.mpr (circling p)).trans; unfold L N; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card G.ColorIndex)]
    apply (mul_le_mul_of_nonneg_right hg hw).trans; have hz:L^(m+r) ≤ Q* E:=widthBill _ (by positivity) _ _ (Nat.cast_nonneg _) 
    rw [show Real.exp (s*lawn p)=E*E from by unfold E;rw [← Real.exp_add]; congr 1; ring]; unfold B; calc _ = ((N:ℝ)^r*t^m*A*E) * L^(m+r):=by unfold w; ring
                                                                                                      _ ≤ _ :=by apply (mul_le_mul_of_nonneg_left hz (show 0≤ (N:ℝ)^r*t^m*A*E by positivity)).trans_eq; ring
end Script
end YM.OPE.Flume
