import Mathlib.Analysis.Analytic.IteratedFDeriv
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.Work.G05.Taylor
import YM.Extra.WILSON_STARTUP.Taylor

/-!
# Price finite Taylor subtraction, both coupling and coordinate slots

No dimension costs; smoothness only on the indicated real germs. `forecast`
valid for external jet order **above** retained terms as well. `Brush`'s cost
carries the stated inverse field radius, crucial for `r` small. Actual masks
and release tests on these radii are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Taylor
open Function Filter Set Metric Analysis Tensor WilsonStartup Work.G05 ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f g : E→F} {j k q : ℕ} {c r : ℝ} {x : E}

/-- Local version of WilsonStartup's integral-free ball estimate. -/
lemma bound_jets (h : FlatAt q f (0:E)) (hb : ∀ y, ‖y‖ ≤ r → ContDiffAt ℝ (↑q) f y ∧ normJ q f y ≤ c)
    (hc : 0 ≤ c) : ∀ j ≤ q, ∀ x, ‖x‖ ≤ r → normJ j f x ≤ c*‖x‖^(q-j) := by
  intro j hj; induction hj using Nat.decreasingInduction with
  | self => intro x hx; simpa only [tsub_self, pow_zero, mul_one] using (hb x hx).2
  | of_succ k hk ih =>
    intro x hx
    let J := iteratedFDeriv ℝ k f
    have hm (y : E) (hy : y ∈ closedBall (0:E) ‖x‖) : ‖fderiv ℝ J y‖ ≤ c * ‖x‖ ^ (q-(k+1)) := calc
      _ = normJ (k+1) f y := norm_fderiv_iteratedFDeriv
      _ ≤ c*‖y‖^(q-(k+1)) := ih y ((mem_closedBall_zero_iff.mp hy).trans hx)
      _ ≤ c*‖x‖^(q-(k+1)) := by gcongr; exact mem_closedBall_zero_iff.mp hy
    have he := (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hb y ((mem_closedBall_zero_iff.mp hy).trans hx)).1.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hk)) hm
      (x:=0) (y:=x) (by simp) (by simp)
    rw [show q-k=(q-(k+1))+1 by omega,pow_succ,←mul_assoc]
    simpa only [h k hk,sub_zero] using! he

/- Cost of rendering homogeneous expansions. The library polarization
formula uses symmetrization at order exactly j, no finite dimension factor.
Lower slots via scaling at the origin.
-/
lemma diag_flat (A : Tensor.T E F j) : FlatAt j (diagonal A) 0 := by
  -- analogous to YM.UVNext.PricedKernels.Tools.homog_lower
  intro i hi
  let d := (2:ℝ); let g : E →L[ℝ] E := d • ContinuousLinearMap.id ℝ E
  have hg (x:E) : g x=d • x := rfl
  have he : diagonal A ∘ g=d^j • diagonal A := funext fun x=> homogeneous A x _
  have hx : iteratedFDeriv ℝ i (diagonal A ∘ g) 0=d^j • iteratedFDeriv ℝ i (diagonal A) 0:= by
    rw [he,iteratedFDeriv_const_smul_apply (diag_smooth A i).contDiffAt]
  ext1 v
  let P:= iteratedFDeriv ℝ i (diagonal A) 0
  rw [g.iteratedFDeriv_comp_right (diag_smooth A i) _ le_rfl,g.map_zero] at hx
  have ht:=DFunLike.congr_fun hx v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at ht; simp_rw [hg] at ht
  rw [P.map_smul_univ (fun _=>d) v, smul_apply] at ht
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at ht
  have hz : (d^j-d^i) • P v=0:= by rw [sub_smul]; exact sub_eq_zero.mpr ht.symm
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos_of_lt (pow_lt_pow_right₀ (by norm_num [d]) hi)))

lemma diag_top (A : Tensor.T E F j) (x : E) : normJ j (diagonal A) x ≤ j.factorial * ‖A‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro v
  unfold Tensor.diagonal
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  let Z : ℝ:= ∏ i, ‖v i‖
  have he (σ : Equiv.Perm (Fin j)) : ‖A (fun i=> v (σ i))‖ ≤ ‖A‖* Z := by
    unfold Z
    conv_rhs => enter [2]; rw [← Equiv.prod_comp σ (fun i=> ‖v i‖)]
    exact A.le_opNorm ..
  exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun σ _ => he σ)).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, mul_assoc]))

lemma diag_above (A : Tensor.T E F j) (h : j<k) : iteratedFDeriv ℝ k (diagonal A)=0 := by
  induction k, h using Nat.le_induction with
  | base =>
    let f:=diagonal A
    have he: iteratedFDeriv ℝ j f=fun _=> iteratedFDeriv ℝ j f 0:= by
      ext1 x; ext1 v; unfold f Tensor.diagonal; simp_rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
    rw [iteratedFDeriv_succ_eq_comp_left, he]; ext1 x; simp; exact map_zero ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1)=> E) F).symm.toLinearEquiv)
  | succ k h ih => rw [iteratedFDeriv_succ_eq_comp_left, ih]; ext1 x; simp; exact map_zero ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1)=> E) F).symm.toLinearEquiv)

lemma payment (a : ℝ) (hr : 0<r) {j q:ℕ} (h : j≤q) : a*r^(q-j)=a*r^q*(r⁻¹)^j := by
  have hx : r^q=r^(q-j)*r^j:= by rw [← pow_add,Nat.sub_add_cancel h]
  rw [hx, inv_pow]; field_simp

lemma diag_brush (A : Tensor.T E F j) (k : ℕ) {x:E} (hx : ‖x‖ ≤ r) (hr : 0<r) :
    Brush k ((j.factorial * ‖A‖)* r^j) (r⁻¹) (diagonal A) x := by
  refine ⟨(diag_smooth A _).contDiffAt, by positivity, fun i _ => ?_⟩
  rcases le_or_gt i j with h|h
  · exact (bound_jets (diag_flat A) (fun y (_:‖y‖≤r)=> ⟨(diag_smooth A _).contDiffAt,diag_top ..⟩) (by positivity) i h x hx).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)).trans_eq (payment _ hr h))
  unfold normJ; rw [diag_above A h,Pi.zero_apply,norm_zero]; positivity

lemma t_above (f : E → F) (h : j<k) : iteratedFDeriv ℝ k (blockTaylor j f)=0 := by
  ext1 x; rw [blockTaylor, iteratedFDeriv_sum_apply]
  · exact Finset.sum_eq_zero fun i hi => congr_fun (diag_above _ (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) h)) x
  exact fun i _ => (diag_smooth ..).contDiffAt

lemma forecast (hr₀ : 0<r) (hr : r ≤ 1) (h : j+1≤k)
    (p : ∀ y, ‖y‖ ≤ r → Brush k c 1 f y) (hx : ‖x‖ ≤ r) :
    Brush k (c*r^(j+1)) (r⁻¹) (f-blockTaylor j f) x := by
  let e:=f-blockTaylor j f
  have hp : FlatAt (j+1) e 0:= flat_sub_taylor f j ((p _ (norm_zero.trans_le hr₀.le)).smaller (by omega)).smooth
  have hb y (hy:‖y‖≤r) : ContDiffAt ℝ (↑k) e y:=(p y hy).smooth.sub (blockTaylor_contDiff ..).contDiffAt
  have he y (hy : ‖y‖ ≤ r) i (hi:j < i) (hh:i≤k) : normJ i e y ≤ c := by
    unfold normJ e; rw [iteratedFDeriv_sub_apply ((p y hy).smaller hh).smooth (blockTaylor_contDiff ..|>.contDiffAt), t_above f hi,Pi.zero_apply,sub_zero]; exact (Brush.offer.1 (p y hy)).inside i hh
  have hc := (p x hx).nonneg
  refine ⟨hb x hx,by positivity,fun i hi=>?_⟩
  rcases le_or_gt i (j+1) with h'|h'
  · exact (bound_jets hp (fun y (hy:‖y‖≤r)=> ⟨(hb y hy).of_le (Nat.cast_le.mpr h),he y hy (j+1) (by omega) h⟩) hc i h' x hx).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hc).trans_eq (payment _ hr₀ h'))
  apply (he x hx _ (by omega) hi).trans
  have H:= payment c hr₀ (le_refl (j+1)); rw [tsub_self,pow_zero,mul_one] at H
  calc
    _ = _ := H
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr₀).2 hr) h'.le) (by positivity)
end YM.AllOrder.Local.Taylor
