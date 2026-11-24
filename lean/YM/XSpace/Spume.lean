import YM.XSpace.Compat.Native
import YM.XSpace.Corn

/-!
# Estimate nearest-left quadrature error for unscaled singular-mesh f

No external smearing; no translation averaging cancels singular data. Extend prior
slope-mesh estimate to admit gaps dividing to degree negative two. Use tiny leash to
restore costs on measuring regulator choices where period overwhelms all powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open YM.XSpace.Compat.KP
open Filter Set Metric Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable (A:List Axis)

lemma pick_one {n:Side} (p:E4) (hp: pick n p≠0): leap n ≤ ‖pick n p‖:=by
  let x:=mark (leap n) p; have hx:x≠0:=fun he=> hp (by unfold pick lit; rw [show mark (leap n) p=0 from he]; ext; simp [rcast])
  obtain ⟨i,hi⟩:= Function.ne_iff.mp hx
  have he : (1:ℝ) ≤ ‖rcast x‖:= by
    have ht: (1:ℤ)≤ |x i|:= by change x i≠(0:ℤ) at hi; have hv : 0 < |x i|:= abs_pos.mpr hi; omega
    have hp : (1:ℝ) ≤ |((x i:ℤ):ℝ)|:= by exact_mod_cast ht
    apply hp.trans; rw [show ↑(x i)=(rcast x) i from rfl, ← basis_inner i (rcast x)]
    simpa only [basis_norm,one_mul] using abs_real_inner_le_norm (basis i) (rcast x)
  unfold pick lit; rw [norm_smul,Real.norm_of_nonneg (leap_pos n).le]; exact le_mul_of_one_le_right (leap_pos n).le he

private lemma charge_near {r t : ℝ} (hr:0<r) (ht:0<t) (h:r≤4*t): (r^2)⁻¹ ≤ 4*t*(r^3)⁻¹ ∧ (t^2)⁻¹ ≤64*t*(r^3)⁻¹:=by
  constructor
  · rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hr 3)]; rw [pow_succ r 2,← mul_assoc,inv_mul_cancel₀ (pow_pos hr _).ne',one_mul]; exact h
  rw [← one_div (t^2), ← div_eq_mul_inv,div_le_div_iff₀ (pow_pos ht 2) (pow_pos hr 3)]; calc
    _ = r^3:=one_mul _
    _ ≤ (4*t)^3:= pow_le_pow_left₀ hr.le h _
    _ = _:=by ring

lemma mesh_difference : ∃ C:ℝ, 0<C∧∀ n:Side,∀ p:E4,p≠0→ ‖city A (pick n p)-city A p‖ ≤ C*leap n*(‖p‖^3)⁻¹:=by
  obtain ⟨C,hC,H⟩ := (moon A).quotes 0; obtain ⟨B,hB,K⟩:=(moon A).quotes 1; let M := 1+ max C B
  have hL : C < M:= lt_add_of_pos_of_le zero_lt_one (le_max_left ..); have hM : 0<M:=lt_of_le_of_lt hC hL; have hK : B<M := lt_add_of_pos_of_le zero_lt_one (le_max_right ..)
  have hp (p:E4): ‖city A p‖≤M*(‖p‖^2)⁻¹:= by
    by_cases h:p=0; simp [h]; refine le_trans ?_ (mul_le_mul_of_nonneg_right hL.le (show 0≤ (‖p‖^2)⁻¹ by positivity)); simpa only [norm_iteratedFDeriv_zero,Nat.cast_zero,sub_zero,zpow_neg,zpow_ofNat] using H () p h
  refine ⟨128*M,by positivity,fun n p ht=>?_⟩
  let b:=pick n p; let t:=leap n; let r:=‖p‖; have hh : 0<t:=leap_pos _; have hr : 0<r:=norm_pos_iff.mpr ht; have hd : ‖b-p‖≤2*t:=pick_near n p
  by_cases hk:r≤4*t
  · obtain ⟨hy,hY⟩:=charge_near hr hh hk
    have he1 : (‖b‖^2)⁻¹ ≤ 64*t*(r^3)⁻¹:=by
      by_cases h0:b=0; rw [h0]; simp; positivity
      apply le_trans ?_ hY; gcongr; exact pick_one _ h0
    apply ((norm_sub_le ..).trans (add_le_add (hp b) (hp p))).trans; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left he1 hM.le) (mul_le_mul_of_nonneg_left hy hM.le)); change _ ≤ 128*M*t*(r^3)⁻¹; have hb : 0<M*t*(r^3)⁻¹:=by positivity
    linarith
  let s:=closedBall p (r/2); have hw (q:E4) (hq : q ∈ s): r/2 ≤ ‖q‖:=by
    have hs:= norm_sub_norm_le p q; have he:= mem_closedBall.mp hq; rw [dist_comm,dist_eq_norm] at he; change r-_≤ _ at hs; linarith
  have hu : s⊆whole.look := fun z hz=> norm_pos_iff.mp ((half_pos hr).trans_le (hw z hz))
  have he (q:E4) (hq:q∈s): ‖fderiv ℝ (city A) q‖≤M*((r/2)^3)⁻¹:=by
    rw [← norm_iteratedFDeriv_one]; apply (K () q (hu hq)).trans; rw [show (-2:ℤ) -(↑(1:ℕ):ℤ) = -3 from rfl, zpow_neg,zpow_ofNat]; gcongr; exact hw q hq
  apply (Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx=> (( (moon A).smooth ()).contDiffAt (whole.ok.mem_nhds (hu hx))).differentiableAt (by simp)) he (convex_closedBall p (r/2)) (mem_closedBall_self ((half_pos hr).le)) (show b∈s by rw [show s=closedBall p (r/2) from rfl,mem_closedBall,dist_eq_norm]; linarith)).trans
  apply le_trans (mul_le_mul_of_nonneg_left hd (by positivity)); change _ ≤ 128*M*t*(r^3)⁻¹; field_simp; nlinarith

def curtain (p:E4):= (ball (0:E4) YM.XSpace.Compat.KP.ceiling).indicator (fun x=> (‖x‖^3)⁻¹) p
lemma sight (n:Side) (p:E4) (h: p∉ball (0:E4) YM.XSpace.Compat.KP.ceiling): house p=0∧house (pick n p)=0:=by
  have he:=not_lt.mp (mt mem_ball_zero_iff.mpr h); unfold YM.XSpace.Compat.KP.ceiling at he
  have hv : leap n ≤2*Real.pi:= div_le_self (by positivity) (by exact_mod_cast (show 1≤n.val from n.property)); have hp:= norm_sub_norm_le p (pick n p); rw [norm_sub_rev] at hp
  exact ⟨door_shut (by linarith [Real.pi_pos]),door_shut (by linarith [pick_near n p])⟩
lemma curt_nonneg (p:E4): 0≤curtain p:= indicator_nonneg (fun p _=> by positivity) _
lemma curtain_ok : Integrable curtain:=by
  have he : IntegrableOn (fun x:E4=> (‖x‖^3)⁻¹) (ball (0:E4) YM.XSpace.Compat.KP.ceiling):=by
    apply integrableOn_ball_of_norm_le_rpow (by simp [E4,Axis]) (α:= (↑(3:ℕ):ℝ)) (by norm_num [E4,YM.Axis]) (C:=1) _ ((measurable_norm.pow_const _).inv.aestronglyMeasurable)
    apply Eventually.of_forall
    intro p; rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]; simp
  exact he.integrable_indicator measurableSet_ball
lemma mesh_variation : ∃ C:ℝ,0<C∧∀ n:Side,(∫ x:E4, ‖city A (pick n x)-city A x‖)≤ C/(n.val:ℝ):=by
  obtain ⟨C,hC,H⟩:= mesh_difference A
  let S:=∫ x:E4, curtain x; have hs : 0≤S:=integral_nonneg curt_nonneg
  refine ⟨C*(2*Real.pi)*(S+1),by positivity,fun n=>?_⟩
  let f:=fun x:E4=> C*leap n*curtain x; have h0:=leap_pos n
  obtain ⟨h,-⟩:= clip_pay n (uncirc A)
  refine le_trans (integral_mono_ae (f:=fun x=> ‖city A (pick n x) - city A x‖) ((show Integrable (fun p:E4=> city A (pick n p)) volume from h).sub (expense_city A)|>.norm) (curtain_ok.const_mul (C*leap n)) ?_) ?_
  · have he : ∀ᵐ x:E4,x≠0 := mem_ae_iff.mpr (by change volume ({x:E4 | x≠0}ᶜ)=0; simp)
    filter_upwards [he] with p hp; by_cases hv:p∈ball (0:E4) YM.XSpace.Compat.KP.ceiling
    · rw [curtain,indicator_of_mem hv]; exact H n p hp
    obtain ⟨hp,hq⟩:= sight n p hv; simp [curtain,hv,city,hp,hq]
  rw [integral_const_mul]; change _*S≤_; unfold leap; have h:=side_pos n; field_simp; nlinarith [Real.pi_pos]
end YM.XSpace.Sail
