import YM.GradedFar.Penultimate
/-!
# Norm conventions, expenses of multilinear frame exchange

Use the sup norm in the prescribed basis, transported to and from the Sec spaces (may have
no required global norm instances), so `Box` is exactly the per-slot bound. Linear maps **on the
Sec operands** assigned their actual operator norms in this presentation when needed; not e.g.,
converting them to some angular answer or their pointwise square along a single measured column.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open MS Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ}
abbrev Sheet (G : Gauge) (h : ℕ) := Toon G h → ℂ
/-- Identify the Sec frame vectors with their (finite) complex coordinate spaces. -/
def columns (G : Gauge) (h : ℕ) : Sec G h ≃ₗ[ℂ] Sheet G h := (Theater.Daylight (Press.portDeck G) h).equivFun
lemma columns_coord (u : Sec G h) (i : Toon G h) : columns G h u i = coord i u := rfl

def width (u : Sec G h) := ‖columns G h u‖
lemma width_nn (u : Sec G h) : 0 ≤ width u := norm_nonneg _
@[simp] lemma width_zero : width (0 : Sec G h) = 0 := by rw [width,map_zero,norm_zero]
lemma width_le {u : Sec G h} {L : ℝ} (hL : 0 ≤ L) : width u ≤ L ↔ ∀ i, ‖coord i u‖ ≤ L :=
  pi_norm_le_iff_of_nonneg hL
lemma coord_le (i : Toon G h) (u : Sec G h) : ‖coord i u‖ ≤ width u := (width_le (width_nn u)).mp le_rfl i
lemma boxes {u : Inputs G d} {L : ℝ} (h : 0 ≤ L) : Box u L ↔ ∀ i, width (u i) ≤ L :=
  ⟨fun hq i => (width_le h).2 (hq i), fun hq i => (width_le h).1 (hq i)⟩
lemma width_smul (z : ℂ) (u : Sec G h) : width (z • u) = ‖z‖ * width u := by
  unfold width; rw [map_smul,norm_smul]
lemma width_add (u v : Sec G h) : width (u+v) ≤ width u + width v := by
  unfold width; rw [map_add]; exact norm_add_le ..
lemma width_sub (u v : Sec G h) : width u ≤ width (u-v) + width v := by
  simpa only [sub_add_cancel] using width_add (u-v) v
lemma width_neg (u : Sec G h) : width (-u) = width u := by unfold width; rw [map_neg,norm_neg]
lemma width_sub_symm (u v : Sec G h) : width (u-v) = width (v-u) := by rw [← width_neg, neg_sub]
lemma width_eq_zero {u : Sec G h} : width u = 0 ↔ u = 0 := by simp [width]
lemma basis_width (q : Toon G h) : width (theory q) = 1 := by
  apply le_antisymm
  · exact (width_le zero_le_one).2 (fun i => by rw [pivotδ]; split_ifs <;> simp)
  have x := coord_le q (theory q); rwa [pivotδ, if_pos rfl, norm_one] at x

/-- Every fixed norm on incoming directions can be used, by paying any fixed finite radius
containing its image. Use e.g. the constructed Maxwell label spaces. -/
lemma fits_norm {E : Fin n → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] (f : ∀ i, E i →ₗ[ℂ] Sec G (d i)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (u : ∀ i, E i), (∀ i, ‖u i‖ ≤ 1) → Box (fun i => f i (u i)) L := by
  let T (i : Fin n) := ((columns G (d i)).toLinearMap.comp (f i)).toContinuousLinearMap
  obtain ⟨C,h⟩ := Finite.exists_le (fun (i : Fin n) => ‖T i‖)
  refine ⟨max C 1,le_max_right .., fun u hu => (boxes (le_trans zero_le_one (le_max_right ..))).mpr (fun i => ?_)⟩
  exact ((T i).le_opNorm (u i)).trans ((mul_le_mul_of_nonneg_left (hu i) (norm_nonneg _)).trans
    ((mul_one _).le.trans ((h i).trans (le_max_left ..))))

section operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def row (B : Sec G l →ₗ[ℂ] E) : Sheet G l →L[ℂ] E :=
  (B.comp (columns G l).symm.toLinearMap).toContinuousLinearMap
def rowPrice (B : Sec G l →ₗ[ℂ] E) := ‖row B‖
lemma row_le (B : Sec G l →ₗ[ℂ] E) (u : Sec G l) : ‖B u‖ ≤ rowPrice B * width u := by
  have h := (row B).le_opNorm (columns G l u)
  change ‖B ((columns G l).symm (columns G l u))‖ ≤ rowPrice B * width u at h
  rwa [LinearEquiv.symm_apply_apply] at h
lemma row_pay {B : Sec G l →ₗ[ℂ] E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u, width u ≤ 1 → ‖B u‖ ≤ C) : rowPrice B ≤ C := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC (f:=row B) (fun i hi => ?_)
  exact h ((columns G l).symm i) (by rw [width, LinearEquiv.apply_symm_apply, hi])

def access (B : Sec G l →ₗ[ℂ] Sec G h) := row ((columns G h).toLinearMap.comp B)
def opField (B : Sec G l →ₗ[ℂ] Sec G h) := ‖access B‖
lemma op_use (B : Sec G l →ₗ[ℂ] Sec G h) (u : Sec G l) : width (B u) ≤ opField B * width u :=
  row_le ((columns G h).toLinearMap.comp B) u
lemma op_pay {B : Sec G l →ₗ[ℂ] Sec G h} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ u, width u ≤ 1 → width (B u) ≤ C) : opField B ≤ C :=
  row_pay (B:=(columns G h).toLinearMap.comp B) hC hv
end operator

section test
variable (B : MultilinearMap ℂ (fun i => Sec G (d i)) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ u, Box u 1 → ‖B u‖ ≤ C)
include H hC
lemma box_apply (v : Inputs G d) : ‖B v‖ ≤ C * ∏ i, width (v i) := by
  by_cases hv : ∀ i, width (v i) ≠ 0
  · let r (i : Fin n) : ℂ := ((width (v i) : ℝ) : ℂ)
    have he i : ‖r i‖ = width (v i) := by rw [show r i = _ from (rfl:r i = (width (v i):ℂ)),
      Complex.norm_real, Real.norm_of_nonneg (width_nn _)] -- clean
    let u (i : Fin n) : Sec G (d i) := (r i)⁻¹ • v i
    calc
      _ = ‖B (fun i => r i • u i)‖ := by
        congr 2; funext i; exact (smul_inv_smul₀ (by simp [r, hv i]) (v i)).symm
      _ = (∏ i, width (v i)) * ‖B u‖ := by
        rw [B.map_smul_univ, norm_smul, norm_prod]; simp_rw [he]
      _ ≤ _ := by
        rw [mul_comm C]; refine mul_le_mul_of_nonneg_left (H u ?_) (Finset.prod_nonneg fun i _ => width_nn _)
        exact (boxes zero_le_one).2 (fun i => by change width ((r i)⁻¹ • v i) ≤ 1; rw [width_smul, norm_inv, he, inv_mul_cancel₀ (hv _)])
  push Not at hv; obtain ⟨i,hi⟩ := hv
  rw [B.map_coord_zero i (width_eq_zero.mp hi), norm_zero]; exact mul_nonneg hC (Finset.prod_nonneg fun i _ => width_nn _)

-- use the sharp multilinear difference bound from mathlib, with per-leg costs, not the identical-ball radius form.
lemma box_sub (u v : Inputs G d) {f : Fin n → ℝ} {ε : ℝ} (h : ∀ i, width (u i) ≤ f i)
    (h' : ∀ i, width (v i) ≤ f i) (he : ∀ i, width (u i-v i) ≤ ε * f i) :
    ‖B u - B v‖ ≤ C * ((n:ℝ) * ε * ∏ i, f i) := by
  let r (u : Inputs G d) i := columns G (d i) (u i)
  let Φ : MultilinearMap ℂ (fun i => Sheet G (d i)) ℂ :=
    B.compLinearMap (fun i => (columns G (d i)).symm.toLinearMap)
  have hΦ : ∀ v, ‖Φ v‖ ≤ C * ∏ i, ‖v i‖ := by
    intro v; have hv := box_apply B hC H (fun i => (columns G (d i)).symm (v i))
    simp only [width, LinearEquiv.apply_symm_apply] at hv; exact hv
  have hp := Φ.norm_image_sub_le_of_bound' hC hΦ (r u) (r v)
  have hv (v) : Φ (r v) = B v := by
    change B (fun i => (columns G (d i)).symm (columns G (d i) (v i))) = _; simp only [LinearEquiv.symm_apply_apply]
  have hf (i) : ∏ j : Fin n, (if j=i then ‖r u i-r v i‖ else max ‖r u j‖ ‖r v j‖) ≤ ε * ∏ i, f i := by
    apply le_trans (Finset.prod_le_prod (g:=fun j : Fin n => (if j=i then ε else 1)*f j)
      (fun j _=> by split_ifs <;> positivity) (fun j _=> ?_))
    · rw [Finset.prod_mul_distrib]; simp
    split_ifs with hi; · subst j; unfold r; rw [← map_sub]; exact he i
    rw [one_mul]; exact max_le (h _) (h' _)
  rw [hv, hv] at hp; refine hp.trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact (Finset.sum_le_sum fun i _ => hf i).trans_eq (by simp [mul_assoc])
end test
end YM.FVA2.GradedFar
