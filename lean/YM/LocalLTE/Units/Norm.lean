import Mathlib.Topology.ContinuousMap.Compact
import YM.LocalLTE.Units.Forms
import YM.LocalLTE.Taylor
/-! Norm recapture from complete supported E projections. Dim-independent dense carriers. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric ContinuousMultilinearMap Tensor
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {E F A : Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] {j n:ℕ}
variable (E) in
abbrev Pkt (n:ℕ) := (i:Fin n)→ Tensor.T E ℝ i
variable (E) in
def honest (n:ℕ) : Submodule ℝ (Pkt E n) where
  carrier:= {X| ∀ i, Sym (X i)}
  add_mem' :=by intro x y h g i v s; specialize h i v s; specialize g i v s; simp [h,g]
  zero_mem' :=by intro i v s; rfl
  smul_mem' := by intro x y h i v s; simp [ (h i v s : _=_)] -- edit

def actual (P:Pkt E n) := ∑ i, Tensor.diagonal (P i)
lemma actual_add (P Q:Pkt E n):actual (P+Q)=actual P+actual Q:= by funext x; simp only [actual,Finset.sum_apply,Tensor.diagonal,Pi.add_apply,add_apply,Finset.sum_add_distrib]
lemma actual_smul (c:ℝ) (P:Pkt E n):actual (c • P)=c • actual P:= by funext x; simp only [actual,Tensor.diagonal, Finset.sum_apply,smul_apply,Pi.smul_apply,Finset.smul_sum]
lemma moves (P:Pkt E n) (k:WithTop ℕ∞) : ContDiff ℝ k (actual P):= by
  unfold actual; simp_rw [Finset.sum_fn]; exact ContDiff.sum fun _ _=> diag_smooth ..
lemma reading (P:Pkt E n)(hp:∀ i,Sym (P i))(i:Fin n) : coeff (actual P) i 0=P i:=by
  rw [actual,coeff_sum _ _ _ _ (fun i _=>diag_smooth _ _|>.contDiffAt), Finset.sum_eq_single i]
  · exact harvest _ (hp _) _
  · intro j _ h; have hk : j.val ≠ i.val:= fun e=>h (Fin.ext e); rcases lt_or_gt_of_ne hk with hu|hu
    · unfold coeff; rw [cap _ (hp j) hu, smul_zero]
    exact under _ (hp j) hu
  simp
lemma stat (P:Pkt E n)(hk:F→L[ℝ] E)(f:F): actual P (hk f)=actual (fun i:Fin n=> (P i).compContinuousLinearMap (fun _=>hk)) f := by
  unfold actual; rw [Finset.sum_apply,Finset.sum_apply]; rfl

lemma finite_norm (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E](n:ℕ)(r : ℝ)(hr:0<r):∃ L:ℝ,0≤L ∧ ∀ P:Pkt E n,(∀ i, Sym (P i))→∀ B:ℝ,0≤B→(∀ i∈closedBall (0:E) r,‖actual P i‖≤ B)→∀ j, ‖P j‖≤L*B:=by
  let S:=closedBall (0:E) r; letI : CompactSpace (↥S) := isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
  let Q: honest E n →ₗ[ℝ] C(↥S,ℝ):= {
    toFun (p : honest E n) := ⟨fun x=> actual p.val x.val,(moves p.val ω).continuous.comp continuous_subtype_val⟩
    map_add' P p:=ContinuousMap.ext fun x=> congr_fun (actual_add P.val p.val) x.val
    map_smul' c P:=ContinuousMap.ext fun x=> congr_fun (actual_smul c P.val) x.val }
  have hQ:Injective Q:=by
    intro i j he; apply Subtype.ext
    have hh:actual i.val=ᶠ[𝓝 0]actual j.val:= by filter_upwards [closedBall_mem_nhds (0:E) hr] with x hx using congr_arg (fun f:C(↥S,ℝ)=>f ⟨x,hx⟩) he
    exact funext fun p=> ((reading _ i.property _).symm.trans (GermCoeff (↑p) hh)).trans (reading _ j.property _)
  have hz: FiniteDimensional ℝ (honest E n):=inferInstance
  have hT : ∃ L > 0, AntilipschitzWith L Q:= by
    apply (LinearMap.injective_iff_antilipschitz (𝕜:=ℝ) (E:=↥(honest E n)) (F:=C(↥S,ℝ)) Q).mp; exact hQ
  obtain ⟨K,hK,H⟩:= hT
  refine ⟨K,K.coe_nonneg,fun P Hp B hb h i=>?_⟩
  let V : honest E n:= ⟨P,Hp⟩; have he: ‖Q V‖≤ B := ContinuousMap.norm_le (Q V) hb|>.mpr fun i=> h i i.2
  have hx := H.le_mul_dist V 0; rw [Q.map_zero,dist_zero_right,dist_zero_right] at hx
  exact (norm_le_pi_norm P i).trans (hx.trans (mul_le_mul_of_nonneg_left he K.coe_nonneg))

open Finset
lemma stake (m:Fin j→E) (z:Fin j→ℝ) (U:ℝ) (hp:∀ i,‖m i‖≤1) (hu: ‖z‖≤U) : ‖∑ i,z i • m i‖ ≤ j*U:= (norm_sum_le ..).trans ((sum_le_sum (s:=univ) (f:=fun i => ‖z i • m i‖) (g:=fun _=>U) (fun i _=> by rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hp i)).trans ((norm_le_pi_norm z _).trans hu))).trans_eq (by simp))
lemma price (n:ℕ)(j:Fin n) : ∃ L:ℝ,0≤L ∧ ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E],∀ (P:Pkt E n) (r M:ℝ), (∀ i, Sym (P i))→0<r → 0≤M→(∀ x,‖x‖≤r → ‖actual P x‖≤M)→ ‖P j‖ ≤ L*M*r⁻¹^j.val :=by
  let D:=Fin j.val→ℝ; let s:=1/(j.val+1:ℝ)
  have h : 0<s:=by unfold s; positivity
  obtain ⟨L,hL,H⟩:= finite_norm D n s h
  refine ⟨L,hL,fun E _ _ P r M ha hr hM he=>opNorm_le_bound (by positivity) fun x=>?_⟩
  let m (i:Fin j.val):= ‖x i‖⁻¹ • x i
  have hm i : ‖x i‖ • m i=x i:= by
    by_cases hh:x i=0
    · unfold m; simp [hh]
    unfold m; exact smul_inv_smul₀ (by simpa) _
  have h₁ i: ‖m i‖≤1:= by
    by_cases hh:x i=0; · simp [hh,m]
    rw [show m i = _ from (rfl:m i=‖x i‖⁻¹ • x i),norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (by simpa)]
  let f : D →L[ℝ] E:= ∑ i, (ContinuousLinearMap.proj i).smulRight (r • m i)
  let V:Pkt D n:= fun i=> (P i).compContinuousLinearMap (fun _=>f)
  have hF (v:D): f v= r • ∑ i,v i • m i := by unfold f; simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,Finset.smul_sum]; exact sum_congr rfl fun i _=>smul_comm ..
  have hk (i:Fin j.val) : f (Pi.single i 1)=r • m i:=by simp [hF]
  have he': ‖V j‖≤ L*M:= H V (fun i v s=> ha i (fun j=> f (v j)) s) _ hM (by
    intro i hi; rw [← stat]; refine he _ ?_
    rw [hF,norm_smul,Real.norm_of_nonneg hr.le]; apply mul_le_of_le_one_right hr.le ((stake m _ _ h₁ (mem_closedBall_zero_iff.mp hi)).trans ?_); unfold s; rw [mul_one_div,div_le_one (by positivity)]; simp) j
  let y (i:Fin j.val): D:= Pi.single i (1:ℝ)
  have hu : ‖V j y‖ ≤ ‖V j‖:= by
    apply unit_le_opNorm; refine (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2 ?_; intro i; change ‖(Pi.single i (1:ℝ):Fin j.val→ℝ)‖ ≤_; apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro j; by_cases hi:i=j <;> simp [hi]
  have hZ : (V j) y=r^j.val • P j m := by
    change P j (fun i=> f (y i))=_; unfold y; simp_rw [hk, (P j).map_smul_univ]; simp
  have hr': ‖P j m‖ ≤ L*M*r⁻¹^j.val := by rw [inv_pow,← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos hr _)).mpr; have hh:= hu.trans he'; rw [hZ,norm_smul,norm_pow,Real.norm_of_nonneg hr.le] at hh; rwa [mul_comm]
  have hp : (P j) x= (∏ i,‖x i‖) • P j m:= by rw [← (P j).map_smul_univ]; exact congr_arg _ (funext (fun i=> (hm i).symm))
  rw [hp,norm_smul,Real.norm_of_nonneg (prod_nonneg (fun _ _=> norm_nonneg _)), mul_comm]; exact mul_le_mul_of_nonneg_right hr' (by positivity)
end YM.LocalLTE.Cabana
