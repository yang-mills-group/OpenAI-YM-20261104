import YM.UVExt.MovingGram


/-! Log-det safeguard at the limiting stationary branch, sending a curvature inequality on the whole finite-dimensional axial slot, not a determinant evaluation on each root separately. Common limits here are only for the subtracted logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Set Filter Matrix Tensor
open scoped BigOperators Classical Topology ContDiff
variable {B E : Type} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]

private def supportOp (L : Tensor.T B ℝ 2) := ((continuousMultilinearCurryFin1 ℝ B ℝ).toContinuousLinearEquiv.toContinuousLinearMap) ∘L L.curryLeft
private lemma support_eval (L : Tensor.T B ℝ 2) (x y : B) : supportOp L x y = L ![x,y] := by
   unfold supportOp
   rw [ContinuousLinearMap.comp_apply] -- names
   change ((continuousMultilinearCurryFin1 ℝ B ℝ) _) y= _
   rw [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]; refine congr_arg L ?_; ext1 i; fin_cases i <;> simp
variable (e : ι→B)
lemma matrixBill (L : Tensor.T B ℝ 2) (k : ι→ℝ) :
     k ⬝ᵥ (Matrix.of (fun i j : ι=> L (![e i,e j]: Fin 2→B))) *ᵥ k = L ![∑ i:ι, k i • e i,∑ i:ι,k i • e i] := by
   let H := Matrix.of (fun i j=>L (![e i,e j]))
   let F := supportOp L
   have hp v : L ![v,v]=F v v := Eq.symm (support_eval ..)
   calc
     _ = ∑ i, k i * ∑ j : ι, H i j * k j := by change k ⬝ᵥ (H *ᵥ k) = _; rfl
     _ = ∑ i, k i * ∑ j, k j * F (e i) (e j) := by simp_rw [show ∀ i j,H i j = F (e i) (e j) from fun _ _=>(support_eval ..).symm]; exact Finset.sum_congr rfl fun i _ => congr_arg (k i * ·) (Finset.sum_congr rfl (fun j _=>by exact mul_comm ..))
     _ = _ := by
       rw [hp,map_sum]; simp only [_root_.sum_apply,map_sum,map_smul,ContinuousLinearMap.smul_apply]; change (∑ i,k i * ∑ j,k j * (F (e i)) (e j)) = ∑ i,k i * ∑ j,k j * (F (e j)) (e i); simp_rw [Finset.mul_sum]; 
       exact (show ∑ x,∑ i,k x*(k i*(F (e x)) (e i)) = _ from Finset.sum_congr rfl fun i u=>(Finset.sum_congr rfl fun j h=> Eq.symm <| mul_left_comm _ (_:ℝ) _)).trans (Finset.sum_comm) -- fix elaboration
variable {e} (hSpan : reach e)
include hSpan
lemma gram_det_ne (c : ℝ) (hv : 0<c) {Z : Matrix ι ι ℝ} (hf : ∀ k:ι→ℝ,c*‖∑ i:ι,k i • e i‖^2 ≤ k ⬝ᵥ (Z *ᵥ k)) : Z.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp <| mulVec_injective_iff_isUnit.mp (fun u v h=> by
   apply eq_of_sub_eq_zero
   apply hSpan
   change (∑ i, (u-v) i • e i) = ∑ i,(0:ι→ℝ) i • e i
   have he := mulVec_sub Z u v; rw [h,sub_self] at he
   have hneg := hf (u-v); rw [he,dotProduct_zero] at hneg -- multiplicities
   simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]; apply norm_eq_zero.mp; by_contra! hp; have hg := mul_pos hv (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)) 2); exact hneg.not_gt hg)) |>.ne_zero
-- replaced by sed

omit hSpan in
lemma shift_charge {f : E×B→ℝ} {ρ : ℝ→B} {x} (z : ι→ℝ) (h : Optimizes f x ρ) : z ⬝ᵥ (shiftedHess e f ρ x 0 *ᵥ z) = eform (iteratedFDeriv ℝ 2 f 0) (∑i,z i • e i) (∑i,z i • e i) := by
    unfold shiftedHess eform
    rw [matrixBill (L:=iteratedFDeriv ℝ 2 _ _),h.anchor,zero_smul]
    exact ((slices_snoc (f:=f) ((0:E), (0:B)) h.smooth _ _)) -- private import; expose

section both
variable {f f' : ℕ→E×B→ℝ} {ρ ρ': ℕ→ℝ→B} {x} [CompleteSpace B] [CompleteSpace E] [FiniteDimensional ℝ B] [FiniteDimensional ℝ E]
omit hSpan in
lemma gram_both (e : ι→B) (ht : reach e) (h : Junction f f' 4) (h₁ : ∀ᶠ i in atTop, Optimizes (f i) x (ρ i)) (h₂ : ∀ᶠ i in atTop, Optimizes (f' i) x (ρ' i)) (u) (hv : 0<u) (hu : clampedGap f u) (v) (hh : 0<v) (H : clampedGap f' v) :
    Joint 2 (fun n=>Real.log ∘ Matrix.det ∘ shiftedHess e (f n) (ρ n) x) (fun n=>Real.log ∘ Matrix.det ∘ shiftedHess e (f' n) (ρ' n) x) := by
   choose W hW hW' using fun i j=> (gram_entry e h₁ h₂ h hv hh hu H i j).at_zero
   let Z n : Matrix ι ι ℝ := shiftedHess e (f n) (ρ n) x 0
   have hc (k : ι→ℝ) : u*‖∑ i,k i • e i‖^2 ≤ k ⬝ᵥ W *ᵥ k := by
      have hG : Tendsto (fun i:ℕ=>k ⬝ᵥ (Z i) *ᵥ k) atTop (𝓝 (k ⬝ᵥ W *ᵥ k)):= tendsto_finsetSum _ (fun i (_ : i∈Finset.univ)=>(tendsto_finsetSum _ (fun j (_ : j∈Finset.univ)=>(hW i j).mul_const (k j))).const_mul (k i))
      exact ge_of_tendsto hG ((hu.and h₁).mono fun i ⟨hi,oh⟩ => by
        change _ ≤ k ⬝ᵥ (Z i *ᵥ k); unfold Z; rw [shift_charge k oh]; exact hi _)
   let d n := Matrix.det ∘ shiftedHess e (f n) (ρ n) x; let d' n:=Matrix.det ∘ shiftedHess e (f' n) (ρ' n) x
   obtain ⟨a,HX,HY⟩ := (det_rates e h₁ h₂ h hv hh hu H).at_zero
   have hd : a = Matrix.det W := tendsto_nhds_unique HX (show Tendsto _ atTop (𝓝 (Matrix.det W)) from ((show Continuous (Matrix.det : Matrix ι ι ℝ→ ℝ) by
       rw [show Matrix.det = fun (A : Matrix ι ι ℝ) => ∑ σ, Equiv.Perm.sign σ • ∏ j, A (σ j) j from funext (Matrix.det_apply)]; fun_prop).tendsto W).comp (tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>hW i j))
   /-simp_rw [show ∀ A : Matrix ι ι ℝ, Matrix.det A = ∑ σ, Equiv.Perm.sign σ • ∏ j, A (σ j) j from Matrix.det_apply]; fun_prop).tendsto W).comp (tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>hW i j))-/
   exact Both_comp (f:=d) (g:=d') Real.log 2 (det_rates e h₁ h₂ h hv hh hu H) HX HY (Real.contDiffAt_log.mpr (hd ▸ gram_det_ne ht u hv hc))
end both
end YM.UVExt.Paths
