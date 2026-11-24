import YM.Integration.WilsonCoherentPivotStencil

/-! Joint continuity in the fluctuating compact pivots and the finite
angular coordinates ensures these chart coefficients are genuine integrands. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentPivotContinuity
open Function Lattice Wilson RG Finset
open RGComparison.Core16 RGComparison.Core16.Spool WilsonCoherentPivotStencil
open scoped Classical ContDiff Matrix.Norms.Frobenius

variable {E K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace K]

private theorem angled (F : E→ℂ) (smooth : ContDiff ℝ ω F) (b A : E) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ=>F (b+t•A)) 0 = iteratedFDeriv ℝ j F b (fun _=>A) := by
  let D : ℝ→L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight A
  let H := fun z : E => F (b+z)
  have hH : ContDiff ℝ ω H := smooth.comp (contDiff_const.add contDiff_id)
  have at0 : ContDiffAt ℝ j H (D 0) := (hH.of_le (by exact_mod_cast (show (j:WithTop ℕ∞)≤ω from le_top))).contDiffAt
  change (iteratedFDeriv ℝ j (H ∘ D) 0) (fun _=>1) = _
  rw [Push.Uniform.iter_lin_at (L:=D) at0]
  simp [H,D,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_comp_add_left]

theorem coefficients (F : E→ℂ) (smooth : ContDiff ℝ ω F) (b z : K→E)
    (hb : Continuous b) (hz : Continuous z) (j : ℕ) :
    Continuous (fun k=>iteratedDeriv j (fun t : ℝ => F (b k+t•z k)) 0) := by
  simp_rw [angled F smooth]
  have jets : Continuous (fun k=>iteratedFDeriv ℝ j F (b k)) :=
    (smooth.continuous_iteratedFDeriv (by exact_mod_cast (show (j:WithTop ℕ∞)≤ω from le_top))).comp hb
  let S := E [×j]→L[ℝ] ℂ
  have ev : Continuous (fun p : S × (Fin j→E) => p.1 p.2) :=
    (ContinuousLinearMap.id ℝ S).continuous_uncurry_of_multilinear
  exact ev.comp (jets.prodMk (continuous_pi fun _=>hz))

variable {G : Gauge} {I : Type} [Fintype I] (J : I→Lamp G)
local notation "L" => Slice J

theorem row (p : ℕ) (t : ℝ) : Continuous (fun v : (L→G.El) × (L→G.Color) =>
    WilsonCoherentPivotStencil.row J v.1 v.2 p t) := by
  obtain ⟨F,smooth,rep⟩ := WilsonCoherentPivotStencil.extension J
  let b := fun v : (L→G.El) × (L→G.Color) => ((fun j=>G.mat (v.1 j)),(0:L→G.Color))
  let a := fun v : (L→G.El) × (L→G.Color) => ((0:L→G.Mat),v.2)
  have hb : Continuous b := (continuous_pi fun j=>G.continuous_mat.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_const
  have ha : Continuous a := continuous_const.prodMk continuous_snd
  have eq (v : (L→G.El) × (L→G.Color)) (h : ℝ) :
      F (b v+h•a v)= field J v.1 (h•v.2) := by simpa [b,a] using rep v.1 (h•v.2)
  apply continuous_finsetSum _ fun j _=>?_
  have q : Continuous (fun v : (L→G.El) × (L→G.Color) =>
      iteratedDeriv j (fun h : ℝ=>field J v.1 (h•v.2)) 0) := by
    simpa only [eq] using coefficients F smooth b a hb ha j
  exact (q.const_smul ((j.factorial:ℝ)⁻¹)).const_smul (t^j)

end YM.Integration.WilsonCoherentPivotContinuity
