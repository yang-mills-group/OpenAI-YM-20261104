import YM.Frontier6.Bouquet.Atlas.Cradles

/-! All crossing factors are also smooth uniformly on the unit of this aperture
 when the scale tests in the punctured expression are used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Audit Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P: Ensemble}{i:P}
section
variable {Y X:Place}[FiniteDimensional ℝ X][FiniteDimensional ℝ Y](n:ℕ)
lemma caught {f:X→ℂ}(he:Smooth f){s C:ℝ}(h:Charge n s f C)(hs:0≤ s): Charge n s (f ∘ floorOf X Y) C:=by
    intro i hi y hy; let p:= floorOf X Y; have hp:‖p‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=>by rw [one_mul]; exact on_budget (P:=X)); let g:=iteratedFDeriv ℝ i f (p y)
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ he y (Normal.natural_le i)];
    apply le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le g (fun _=>p)) (pow_nonneg hs _))
    change s^i * (‖g‖*∏ _j:Fin i,‖p‖) ≤ C; rw [Finset.prod_const, card_univ,Fintype.card_fin,← mul_assoc]; -- typo
    exact (mul_le_of_le_one_right (mul_nonneg (pow_nonneg hs _) (norm_nonneg g)) (pow_le_one₀ (norm_nonneg p) hp)).trans (h i hi (p y) (Set.mem_univ _))
lemma unit_power (n:ℕ)(s:ℝ): Charge n s (fun _:X=> (1:ℂ)) 1:=by intro j hj x _; by_cases hh:j=0; subst j; simp; simp [iteratedFDeriv_const_of_ne hh]; have h0:= norm_zero (E:= Tensor.T X ℂ j); exact (Eq.trans (congr_arg (_ * ·) h0) (mul_zero _)).trans_le zero_le_one
lemma cure (v:Pod): ∃ C:ℝ,0 ≤ C∧∀ s:ℝ,0<s→ Charge n s (fun x:X=>(common s).blend v x.val) C:=by
   obtain ⟨C,hC,H⟩:= Normal.shrink_charge (X:=normal v) n; refine ⟨_,add_nonneg (b:=C) zero_le_one hC,fun s hs=>?_⟩
   let g:= Normal.shrink (normal v) s; simp_rw [Veins.blend, common_at hs]; exact Estimate.sub (unit_power (X:=X) n s) (caught n g.contDiff (H s hs) hs.le) contDiff_const (g.contDiff.comp (floorOf (normal v) X).contDiff) hs.le
lemma cures (A:Finset Pod):∃ C:ℝ,0 ≤ C∧∀ s:ℝ,0<s→ Charge n s (fun x:X=>(common s).cutter A x.val) C:=by
   induction A using Finset.induction_on with
   | empty=> refine ⟨1,zero_le_one,fun s hs=>?_⟩; simp_rw [Veins.cutter,Finset.prod_empty]; exact unit_power n s
   | @insert a A hh ih=>
     obtain ⟨C,hC,H⟩:=ih; obtain ⟨c,hc,G⟩:= cure (X:=X) n a; refine ⟨(2:ℝ)^n*c*C,by positivity,fun s hs=>?_⟩; simp_rw [Veins.cutter, Finset.prod_insert hh]; let p:= common s; exact Estimate.mul (G s hs) (H s hs) hc hC hs.le ((p.blend_smooth a).comp X.subtypeL.contDiff) ((p.cutter_smooth A).comp X.subtypeL.contDiff)
end
namespace Court
variable (Z:Court i)
lemma susp_shape (T:Veins)(x:fiber P): T.susp P Z.split x.val= T.susp P Z.split (rune i x).val:=by
   unfold Veins.susp Veins.cutter; refine prod_congr rfl (fun p hp=>?_); unfold Veins.blend; congr 2; exact on_lower (normal_sub (Z.scar p hp)) _
lemma film_alone (T:Veins):T.film P Z.split= paneM (T.susp P Z.split ∘ (normal i.val).subtypeL) ((T.cutter_smooth (scars ..)).comp (normal i.val).subtypeL.contDiff) :=by ext1 f; ext1 x; change T.susp P Z.split x.val*f x=T.susp P Z.split (rune i x).val*f x; rw [susp_shape]
lemma film_delayed {f:Full (fiber P)}{r u:ℝ}(hr:0<r)(hu:0<u)(he: Z.Contains r f)(hU:4*u<Z.clearance*r) : (common u).film P Z.split f=f:=by
   ext1 x; rw [Veins.filmed]; by_cases hx:x∈ tsupport f
   · unfold Veins.susp; rw [(common u).cutter_fixed,one_mul]; intro p hp; rw [Audit.common_at hu]; linarith only [Z.sensitive hr (he x hx) p hp,hU]
   rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
end Court
end YM.Frontier6.Bouquet.Atelier
