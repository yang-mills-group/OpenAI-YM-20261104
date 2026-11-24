import YM.LocalLTE.Units.Norm
/-! Off cone interpolation. Finite derivative order arbitrary, Price dimension-free. Uses one-sided PETALS and K.*, no continuation of actual interaction off Health. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric Tensor PhysicalNext.Repeat ConnectedActivityE6.Blaze Brush
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {j d m J:ℕ}
lemma highPoly (q:Pkt E j)(x:E)(h:j≤ d): iteratedFDeriv ℝ d (Cabana.actual q) x=0:=by
  have he:Cabana.actual q= ∑ i:Fin j,Tensor.diagonal (Tensor.symmetrize (q i)):= by funext i; simp_rw [Finset.sum_apply,Tensor.symmetrize_diagonal,Cabana.actual,Finset.sum_apply]
  rw [he, iteratedFDeriv_sum_apply (fun _ _=> (Tensor.diag_smooth _ _).contDiffAt)]; exact Finset.sum_eq_zero fun i _=> LocalLTE.cap _ (Tensor.symmetrize_sym _) (i.2.trans_le h) x

lemma finite_cast (n:ℕ)(q:E)(r:ℝ)(hp:0<r)[FiniteDimensional ℝ E]: ∃ L:ℝ,0≤L ∧ ∀ P:Pkt E n,(∀ i,Sym (P i))→∀ B:ℝ,0≤B→(∀ x∈closedBall q r,‖Cabana.actual P x‖≤ B)→∀ i,‖P i‖≤ L*B:=by
  let S:=closedBall q r; letI : CompactSpace (↥S) := isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
  let Q: honest E n →ₗ[ℝ] C(↥S,ℝ):= {
    toFun (p : honest E n) := ⟨fun x=> Cabana.actual p.val x.val,(moves p.val ω).continuous.comp continuous_subtype_val⟩
    map_add' P p:=ContinuousMap.ext fun x=> congr_fun (actual_add P.val p.val) x.val
    map_smul' c P:=ContinuousMap.ext fun x=> congr_fun (actual_smul c P.val) x.val }
  have hQ:Injective Q:=by
    intro i j he; apply Subtype.ext
    have hh:actual i.val=ᶠ[𝓝 q]actual j.val:= by filter_upwards [closedBall_mem_nhds q hp] with x hx using congr_arg (fun f:C(↥S,ℝ)=>f ⟨x,hx⟩) he
    have hA (g): AnalyticOnNhd ℝ (actual (E:=E) (n:=n) g) Set.univ:= fun x _=> (moves _ ω|>.contDiffAt).analyticAt
    have hZ:actual i.val=actual j.val:=AnalyticOnNhd.eq_of_eventuallyEq (hA _) (hA _) hh
    exact funext fun p=> ((reading _ i.property _).symm.trans (congr_arg (fun f=> coeff f p.val 0) hZ)).trans (reading _ j.property _)
  have hT : ∃ L > 0, AntilipschitzWith L Q:= by
    apply (LinearMap.injective_iff_antilipschitz (𝕜:=ℝ) (E:=↥(honest E n)) (F:=C(↥S,ℝ)) Q).mp; exact hQ -- edit
  obtain ⟨K,hK,H⟩:= hT
  refine ⟨K,K.coe_nonneg,fun P Hp B hb h i=>?_⟩
  let V : honest E n:= ⟨P,Hp⟩; have he: ‖Q V‖≤ B := ContinuousMap.norm_le (Q V) hb|>.mpr fun i=> h i i.2
  have hx := H.le_mul_dist V 0; rw [Q.map_zero,dist_zero_right,dist_zero_right] at hx
  exact (norm_le_pi_norm P i).trans (hx.trans (mul_le_mul_of_nonneg_left he K.coe_nonneg))

-- Angular interpolation patch. Witness column s in [λ/2,λ], transverse proportional to s.
def Dart (c:E)(r:ℝ)(x:E):Prop:= ∃ s:ℝ, s∈ Icc (0:ℝ) 1∧ ‖x-s • c‖≤ s*r
lemma charter (n:ℕ) (j:Fin n):∃ L:ℝ,0≤L ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ (P:Pkt E n)(c:E)(r M:ℝ), (∀ i,Sym (P i))→0<r→0≤M→ (∀ x:E, Dart c r x → ‖actual P x‖≤M)→‖P j‖ ≤ L*M*r⁻¹^j.val:=by
  let D:= ℝ × (Fin j.val→ℝ); let s:=1/(4*(j.val+1:ℝ)); have hs:0<s:=by unfold s; positivity
  have hS:s≤1/4:=by unfold s; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Nat.cast_nonneg (α:=ℝ) j.val]
  obtain ⟨L,hL,H⟩:= finite_cast n ((1/2,0):D) s hs
  refine ⟨L,hL,fun E _ _ P c r M ha hr hM he=>ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun x=>?_⟩
  let m (i:Fin j.val):= ‖x i‖⁻¹ • x i
  have hm i : ‖x i‖ • m i=x i:= by
    by_cases hh:x i=0
    · unfold m; simp [hh]
    unfold m; exact smul_inv_smul₀ (by simpa) _
  have h₁ i : ‖m i‖≤1:= by
    by_cases hh:x i=0; · simp [hh,m]
    rw [show m i = _ from (rfl:m i=‖x i‖⁻¹ • x i),norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (by simpa)]
  let g : (Fin j.val →ℝ)→L[ℝ] E:= ∑ i, (ContinuousLinearMap.proj i).smulRight (r • m i)
  let f : D→L[ℝ] E:= (ContinuousLinearMap.fst ℝ _ _).smulRight c + g ∘L (ContinuousLinearMap.snd ℝ _ _)
  let V:Pkt D n:= fun i=> (P i).compContinuousLinearMap (fun _=>f)
  have hF (v:D): f v= v.1 • c + r • ∑ i,v.2 i • m i:= by
    change _ + g v.2= _; congr 1; unfold g; simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>smul_comm ..
  let y (i:Fin j.val):D:= (0, Pi.single i 1)
  have hk i : f (y i)=r • m i:= by simp [hF,y]
  have hp (v:D) (hh:v∈closedBall ((1/2,0):D) s): Dart c r (f v):= by
    rw [Metric.mem_closedBall,Prod.dist_eq,max_le_iff] at hh; change dist _ _≤ s ∧ dist _ _≤ s at hh; simp only [Real.dist_eq, abs_le, dist_zero_right] at hh
    have hg:1/4≤v.1:= by linarith only [hh.1.1,hS]
    refine ⟨v.1,⟨(by linarith),(by linarith only [hh.1.2,hS])⟩,?_⟩; rw [hF,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
    apply mul_le_mul_of_nonneg_right ((stake m v.2 s h₁ hh.2).trans (le_trans ?_ hg)) hr.le
    unfold s; rw [mul_one_div,div_le_iff₀ (by positivity)]; linarith
  have he': ‖V j‖≤ L*M:= H V (fun i v s=> ha i (fun j=> f (v j)) s) _ hM (fun v hv=> ((stat P f v).symm ▸ he _ (hp v hv))) j
  have hu : ‖V j y‖ ≤ ‖V j‖:= by
    apply ContinuousMultilinearMap.unit_le_opNorm; refine (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2 ?_; intro i; change max ‖(0:ℝ)‖ ‖(Pi.single i (1:ℝ):Fin j.val→ℝ)‖ ≤_; refine max_le (by simp) ?_; apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro j; by_cases hi:i=j <;> simp [hi]
  have hZ : (V j) y=r^j.val • P j m:= by
    change P j (fun i=> f (y i))=_; simp_rw [hk, (P j).map_smul_univ]; simp
  have hr': ‖P j m‖ ≤ L*M*r⁻¹^j.val:= by rw [inv_pow,← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos hr _)).mpr; have hh:= hu.trans he'; rw [hZ,norm_smul,norm_pow,Real.norm_of_nonneg hr.le] at hh; rwa [mul_comm]
  have hp : (P j) x= (∏ i,‖x i‖) • P j m:= by rw [← (P j).map_smul_univ]; exact congr_arg _ (funext (fun i=> (hm i).symm))
  rw [hp,norm_smul,Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _=> norm_nonneg _)), mul_comm]; exact mul_le_mul_of_nonneg_right hr' (by positivity)
end YM.LocalLTE.Cabana
