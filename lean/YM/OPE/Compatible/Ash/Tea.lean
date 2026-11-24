import YM.OPE.Compatible.Ash.Pip
/-!
# Single particle dipole. Move in ℝ⁴ before logarithmic extraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full Laurent
open scoped BigOperators Classical ContDiff
variable {n:Side}
lemma one_bead (i:Axis)(a:Cover): (a i).natAbs≤size a:= Finset.single_le_sum (f:=fun i=>(a i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)
lemma bead (x:Cover)(h:ℝ)(hh:0 ≤ h): h*(size x:ℝ) ≤ 4*‖incVec h x‖:=by
    unfold size; push_cast; rw [Finset.mul_sum]; apply le_trans (Finset.sum_le_sum (g:=fun i:Axis=> ‖incVec h x‖) ?_) (le_of_eq (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; norm_cast))
    intro i _; have hx:=coordinate_le (incVec h x) i; rw [incVec_apply,abs_mul,abs_of_nonneg hh,←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at hx; exact hx
lemma twice_bead (x:Cover)(h:ℝ)(hh:0 ≤ h):‖incVec h x‖ ≤ 2*h*(size x:ℝ):=by
    obtain ⟨i,hi⟩:=Pert.Band.max_coord (incVec h x); rw [incVec_apply,abs_mul,abs_of_nonneg hh, ← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast,← mul_assoc] at hi; grw [hi]; gcongr; exact one_bead ..
lemma gentle {x:Cover}(h:2*size x<n.val): Lattice.lift (wrap n x)=x:=by
   rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩; have hx:=one_bead i x;omega
lemma softening {z:E4}(hz:z≠0)(D:List Axis)(R:ℕ→Side)(he:Tendsto (fun i=> (R i).val) atTop atTop)(p:ℕ→Cover)(hp:Tendsto (fun i=>incVec (dew (R i)) (p i)) atTop (𝓝 z)): Tendsto (fun i=>(dew (R i)^(D.length+2))⁻¹ * hull D (p i)) atTop (𝓝 (casual D z).re):=by
   let h(i):= dew (R i); let n(i):=R i*R i; let f(i):= sizeR (R i); let x(i):=wrap (n i) (p i)
   have H(i):sizeR (n i)=f i*f i:=by unfold sizeR n f; rw [PNat.mul_coe, Nat.cast_mul]
   have he₁(i):0<f i:=val_pos _; have he₂(i):0<h i:=dew_pos _; have hx(i): sizeR (n i)*h i=f i:=by have hv:=he₁ i; rw [H]; change f i*f i*(f i)⁻¹=_; field_simp
   have hD :=tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp he; have he': Tendsto h atTop (𝓝 0):=tendsto_inv_atTop_zero.comp hD
   have HH:∀ᶠ i in atTop, 2*size (p i)< (n i).val:=by
       filter_upwards [hp.norm.eventually (ge_mem_nhds (lt_add_one ‖z‖)),hD.eventually (eventually_gt_atTop (8*(‖z‖+1)))] with i hi hk; have ht := bead (p i) _ (he₂ i).le; change _ ≤ ‖z‖+1 at hi; change 8*(‖z‖+1)< f i at hk; rw [←hx i] at hk
       have hu: (2*size (p i):ℝ)*(h i) < sizeR (n i)*(h i):=by linarith only [hi,hk,ht] -- ht uses h
       exact_mod_cast lt_of_mul_lt_mul_right hu (he₂ i).le
   have hV:= joint_casual n R h D x hz (fun i=> (hx i).symm) he₂ he he' (hp.congr' (HH.mono fun i hi=> by dsimp only; dsimp only [x,h]; rw [gentle hi]))
   obtain ⟨C,hC,M,hp⟩:=image_pebbles D; let k:=D.length+2
   have ha:Tendsto (fun i=>(h i^k)⁻¹ * seam D (n i) (p i)) atTop (𝓝 0):=by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hb:= (he'.pow k|>.const_mul C); simp only [zero_pow (by unfold k;omega:k≠0),mul_zero] at hb; apply squeeze_zero' (Eventually.of_forall (fun i=>norm_nonneg _)) _ hb; filter_upwards [HH,he.eventually (eventually_ge_atTop M)] with i hi hI
       rw [norm_mul,Real.norm_of_nonneg (by have hh:=he₂ i; positivity)]; apply (mul_le_mul_of_nonneg_left (hp (n i) (le_trans hI (Nat.le_mul_of_pos_right _ (R i).property)) (p i) hi.le) (by have hv:=he₂ i; positivity)).trans; apply le_of_eq; rw [show dew (n i)=h i*h i from by unfold h dew; rw [H,mul_inv]]; have he:=he₂ i; rw [mul_pow]; unfold k; field_simp
   have ho:= ((Complex.continuous_re.continuousAt.tendsto.comp hV).sub ha); rw [sub_zero] at ho
   apply Filter.Tendsto.congr _ ho
   intro i; change (joint _ D (x i)).re - (h i^k)⁻¹ * seam D (n i) (p i)= (h i^k)⁻¹*hull D (p i)
   unfold seam; rw [full_X _ _ _ (he₂ i)]; change _-(h i^k)⁻¹*(h i^k*(joint (h i) D (x i)).re-_) = _; have ht:=he₂ i; field_simp; ring
end YM.OPE.Balsam
