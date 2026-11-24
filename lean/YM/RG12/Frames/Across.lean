import YM.RG12.Frames.Compression

/-!
# Sufficient tests for one step of log budget

Full measurements on the moving labels need not even be within O(1/n) of a fixed/free
quadratic form. Compare *to each other* under length transport. Strict flag shears allowed,
e.g. at perturbative order one. No cross Gram between near and far reference scales used in
this criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable [FiniteDimensional ℂ (Col V)]

/-- `A` actual comparable-scale transition on pivots, `J` permitted change before comparison.
 Can use both powers (forward/back) at power a of age ratio. No power losses in coupling units
 are allowed on those two crucial lines! -/
structure Compared (A J : Col V ≃ₗ[ℂ] Col V) (before after : Col V → ℝ) (K s r : ℝ)
    (a b : ℕ) : Prop where
  earlier : Tests before K
  later : Tests after K
  lower : triangular V A.toLinearMap
  fit : triangular V J.toLinearMap ∧ ∀ i : Grade d, ∀ x : V i, block V J.toLinearMap i i x = x
  setup x : ‖J x‖ ≤ s^b * ‖x‖ ∧ ‖J.symm x‖ ≤ s^b * ‖x‖
  reads x : before (A (J x)) ≤ r ^ a * after x ∧ after x ≤ r ^ a * before (A (J x))

variable {A J : Col V ≃ₗ[ℂ] Col V} {g h : Col V → ℝ} {K s r : ℝ} {a b : ℕ}

/-- Conservative price exponent; s ≥ K absorbs the norm conversions, r ≤ s for the
consecutive age comparison. -/
theorem TestedStep (hc : Compared A J g h K s r a b) (hs : K ≤ s) (hr : 1 ≤ r) (he : r ≤ s) :
    Step A.toLinearMap (compress g) (compress h) K s r a (a+b+4) ∧
      Step A.symm.toLinearMap (compress h) (compress g) K s r a (a+b+4) := by
  let B := J.trans A
  have hK := hc.earlier.legal; have hK' := zero_le_one.trans hK
  have hp := zero_lt_one.trans_le (hK.trans hs); have hV : 0 < r ^ a := pow_pos (zero_lt_one.trans_le hr) _
  have hf:= fits_compress hc.earlier; have hF:= fits_compress hc.later
  have ht : triangular V B.toLinearMap := hc.lower.comp hc.fit.1
  have hx (i:Grade d) (x:V i) : block V B.toLinearMap i i x=block V A.toLinearMap i i x := by
    have ho := (triangular_iff_stays V _).mp hc.fit.1 _ _ (put_flag i i x le_rfl)
    change A ((J.toLinearMap) (put V i x)) i = _
    exact (same_diag hc.lower ho).trans (congr_arg _ (hc.fit.2 i x))
  have hx' (i:Grade d) (x:V i) : block V B.symm.toLinearMap i i x=block V A.symm.toLinearMap i i x := by
    have ho : Injective (block V A.toLinearMap i i) := by
      have hv (x) : block V A.symm.toLinearMap i i (block V A.toLinearMap i i x) = x := inv_diag (A:=A.symm) hc.lower.inv ..
      intro x y he; rw [← hv x,he,hv]
    apply ho; rw [← hx i (block V B.symm.toLinearMap ..),inv_diag ht, inv_diag hc.lower]
  have hA(x) : ‖A x‖ ≤ K*(r^a*(K*(s^b*‖x‖))) := by
    apply (hc.earlier.lower ..).trans
    have he := (hc.reads (J.symm x)).1; rw [J.apply_symm_apply] at he
    exact mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left ((hc.later.upper _).trans
      (mul_le_mul_of_nonneg_left (hc.setup x).2 hK')) hV.le)) hK'
  have hA'(x) : ‖A.symm x‖ ≤ K*(r^a*(K*(s^b*‖x‖))) := by
    have hz: ∀ z, h (B.symm z) ≤ r^a * g z:=by
      intro z; have he:= (hc.reads (B.symm z)).2; rwa [show A (J _) = z from B.apply_symm_apply z] at he
    have he : ‖B.symm x‖ ≤ K*(r^a*(K*‖x‖)) := by
      exact (hc.later.lower ..).trans (mul_le_mul_of_nonneg_left ((hz x).trans
        (mul_le_mul_of_nonneg_left (hc.earlier.upper _) hV.le)) hK')
    calc
      _ = ‖J (B.symm x)‖ := by
        refine congr_arg norm ?_; apply A.injective
        rw [A.apply_symm_apply, show A (J _) = x from B.apply_symm_apply x]
      _ ≤ s^b * (K*(r^a*(K*‖x‖))):= ((hc.setup ..).1).trans (mul_le_mul_of_nonneg_left he (pow_nonneg hp.le _))
      _ = _ := by ring
  have hbound {X : Col V ≃ₗ[ℂ] Col V} {g h: Currency V} (hg : Fits g K) (hh : Fits h K)
      (hσ : ∀ x, ‖X x‖ ≤ K*(r^a*(K*(s^b*‖x‖)))) (i j : Grade d) (x: V j) :
      g i (block V X.toLinearMap i j x) ≤ s^(a+b+4)*h j x := by
    have hL : ‖put V j x‖ ≤ K*h j x:= (put_norm_le ..).trans (hh.lower ..)
    refine (hg.upper ..).trans (le_trans (b:= K*(K*(r^a*(K*(s^b*(K*h j x))))))
      (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (X (put V j x)) i).trans
        ((hσ _).trans (by gcongr))) hK') ?_)
    rw [pow_add, pow_add]; exact (le_trans (b:=s*(s*(s^a*(s*(s^b*(s*h j x)))))) (by
      have h0:= hh.nonneg j x; gcongr) (by exact le_of_eq (by ring)))
  refine ⟨⟨hf,hF,hc.lower,fun i x=> ?_,fun i j _ x=> hbound (X:=A) hf hF hA ..⟩,⟨hF,hf,hc.lower.inv,fun i x=>?_,fun i j _ x=>hbound (X:=A.symm) hF hf hA' ..⟩⟩
  · rw [← hx]; exact compare_fiber ht hc.earlier hV (fun _=> (hc.reads ..).1) i x
  rw [← hx']
  exact compare_fiber ht.inv hc.later hV (fun z=> by
    have hu:= (hc.reads (B.symm z)).2
    rwa [show A (J _) = z from B.apply_symm_apply z] at hu) i x
end YM.RG12.Frames
