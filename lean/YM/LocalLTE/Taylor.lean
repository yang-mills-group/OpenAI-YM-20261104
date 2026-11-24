import YM.Analysis.Exchange
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Pine

/-! Multidimensional Taylor prices using the same `Brush` norm as the auxiliary proof.
Does not require finite-dimensional E, except for Type here; dimension-independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE
open Set Function Filter Metric Analysis Tensor ConnectedActivityE6.Blaze PhysicalNext.Repeat
open scoped Topology ContDiff
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j k n m : ℕ}

-- Two tensor helpers adapted from YM.TraceExtension.Filch.Choir and
-- YM.Push.FINITE_DETECTION.Leading; general E, F.
open ContinuousMultilinearMap in
theorem harvest (A : Tensor.T E F j) (hA : Sym A) (x : E) : coeff (diagonal A) j x = A := by
  apply ContinuousMultilinearMap.ext; intro u
  induction j with
  | zero => rw [Tensor.coeff_apply_zero]; exact congr_arg A (Subsingleton.elim ..)
  | succ j ih =>
    rw [← Fin.cons_self_tail u]
    let v := u 0
    let w := Fin.tail u
    let B := A.curryLeft v
    let t := (↑(j+1 : ℕ) : ℝ)
    have he : D v (diagonal A) = t • diagonal B := funext fun y => by
      rw [D,differential_diagonal A hA]; change _ = (↑(j+1 : ℕ) : ℝ) • diagonal B y
      rw [Nat.cast_smul_eq_nsmul]; rfl
    have hs := ih B (freeze_sym A hA v) w
    have ht : t ≠ 0 := by dsimp [t]; positivity
    change coeff (diagonal A) (j+1) x (Fin.cons v w) = _
    rw [coeff_apply_cons (diag_smooth A _|>.contDiffAt), he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply,hs]
    change t⁻¹ • t • B w = _; rw [inv_smul_smul₀ ht]; rfl

open ContinuousMultilinearMap in
theorem under (A : Tensor.T E F j) (hA : Sym A) (hh : k < j) : coeff (diagonal A) k 0 = 0 := by
  apply ContinuousMultilinearMap.ext; intro u
  induction k generalizing j with
  | zero =>
    rw [coeff_apply_zero]
    change A (fun _ => 0) = 0
    exact A.map_coord_zero (⟨0,hh⟩ : Fin j) rfl
  | succ k ih =>
    rw [← Fin.cons_self_tail u, coeff_apply_cons (diag_smooth A _|>.contDiffAt)]
    cases j with
    | zero => omega
    | succ j =>
      let v := u 0
      let B := A.curryLeft v
      have he : D v (diagonal A) = (↑(j+1 : ℕ) : ℝ) • diagonal B := funext fun x => by
        rw [D,differential_diagonal A hA]; change _ = (↑(j+1 : ℕ) : ℝ) • diagonal B x
        rw [Nat.cast_smul_eq_nsmul]; rfl
      rw [he, Tensor.coeff_smul _ (diag_smooth _ _|>.contDiffAt), smul_apply, ih B (freeze_sym A hA v) (by omega)]
      simp

theorem cap (A : Tensor.T E F j) (hA : Sym A) (hk : j < k) (x : E) :
    iteratedFDeriv ℝ k (diagonal A) x = 0 := by
  have hg : ∀ n : ℕ, iteratedFDeriv ℝ (j+1+n) (diagonal A) = 0 := by
    intro n; induction n with
    | zero =>
      have he : iteratedFDeriv ℝ j (Tensor.diagonal A) = fun _ => (j.factorial : ℝ) • A := funext fun z => by
        conv_rhs => rw [← harvest A hA z,coeff,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
      simp only [Nat.add_zero, iteratedFDeriv_succ_eq_comp_left,he]
      funext; simp; ext; rfl
    | succ n ih => rw [← Nat.add_assoc,iteratedFDeriv_succ_eq_comp_left, ih]; funext; simp; ext; rfl
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk; exact congr_fun (hg _) x

def stem (p : ℕ) (f : E→ F) := ∑ i ∈ Finset.range p, diagonal (coeff f i 0)
theorem stem_contDiff (p : ℕ) (f : E→ F) : ContDiff ℝ m (stem p f) := by
  simp_rw [stem, Finset.sum_fn]; exact ContDiff.sum fun _ _=> diag_smooth _ _

theorem firstJet {f:E→F} (hf:ContDiffAt ℝ (↑ n) f 0) (he:k < j) (hj : j ≤ n) :
    iteratedFDeriv ℝ k (stem j f) 0 = iteratedFDeriv ℝ k f 0 := by
  have h : coeff (stem j f) k 0=coeff f k 0:= by
    rw [stem, coeff_sum k _ _ _ (fun i _=> (diag_smooth _ _).contDiffAt), Finset.sum_eq_single k]
    · exact harvest _ (coeff_symm (hf.of_le (by exact_mod_cast he.le.trans hj))) _
    · intro l hl hk; simp only [Finset.mem_range] at hl
      have hA := coeff_symm (hf.of_le (show (l : WithTop ℕ∞) ≤ n from by exact_mod_cast hl.le.trans hj))
      rcases lt_or_gt_of_ne hk with hk|hk
      · unfold coeff -- avoid inner
        change (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k (diagonal (coeff f l 0)) 0=0
        rw [cap _ hA hk,smul_zero]
      exact under _ hA hk
    simp [he]
  exact (smul_right_injective (Tensor.T E F k) (inv_ne_zero (show (k.factorial:ℝ) ≠0 by positivity))) h

theorem highJet {f:E→F} (hf:ContDiffAt ℝ (↑ n) f 0) (he:j ≤ k) (hj : j ≤ n) (x : E):
    iteratedFDeriv ℝ k (stem j f) x = 0 := by
  unfold stem; rw [iteratedFDeriv_sum_apply (fun _ _=> (diag_smooth _ _).contDiffAt)]
  refine Finset.sum_eq_zero ?_; intro m hm; simp only [Finset.mem_range] at hm
  exact cap _ (coeff_symm (hf.of_le (by exact_mod_cast hm.le.trans hj))) (hm.trans_le he) _

theorem pays {f:E→F} {a C:ℝ} (ha: 0<a) (he : a≤1) (hv:0 ≤ C) (h:j ≤ n)
    (hp: ∀ x∈ Metric.ball 0 a,ContDiffAt ℝ (↑ n) f x) (hh: ∀ x∈ Metric.ball (0:E) a,∀ i:ℕ,j ≤ i → i ≤ n → normJ i f x ≤ C)
    (x:E) (hx:x∈Metric.ball 0 a) : Brush n (C*a^j) a⁻¹ (f-stem j f) x := by
  have hf:= hp 0 (mem_ball_self ha)
  have hu := Shellac.pools (f:=f-stem j f) ha he h hv (le_refl (0:ℝ)) (fun x hx => (hp x hx).sub (stem_contDiff _ _|>.contDiffAt)) (fun i hi hm y hy=>?_) (fun i hi=>?_) x hx
  · rwa [mul_zero,add_zero] at hu
  · unfold normJ; rw [iteratedFDeriv_sub_apply ((hp _ hy).of_le (Nat.cast_le.mpr hm)) (stem_contDiff _ _|>.contDiffAt),highJet hf hi h,sub_zero]; exact hh _ hy i hi hm
  unfold normJ; rw [iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast hi.le.trans h)) (stem_contDiff _ _|>.contDiffAt), firstJet hf hi h, sub_self,norm_zero,zero_mul]
end YM.LocalLTE
