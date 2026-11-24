import YM.Integration.WilsonPhysicalHistoryRetainedSpringVisits

/-! Integrate the signed curvature vertex before summing its original
periodic path roster. Every ordered visit uses the same measure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson Finset MeasureTheory
open WilsonMeasuredPathTaylor FundedCurvatureRayTaylor WilsonSlotContactTruncation
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

theorem atom_path_error (a : Atom G k) (x : Site n) (v : Directions G n) (q : ℕ) (t : ℝ) :
    ‖(a.unmasked (field v t) x:ℂ)-polynomial a x v q t‖≤
      ∑ b,|a.coeff b| *(score v x (letters a b)^(q+1)*|t|^(q+1)/(q+1).factorial) := by
  rw [evaluated,polynomial,←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _=>?_)
  rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (slots v x (letters a b) q t) (abs_nonneg _)

theorem measured_atom_error (μ : Measure Ω) (v : Ω→Directions G n)
    (a : Atom G k) (x : Site n) (q : ℕ) (t : ℝ) {M σ : ℝ} (pos : 0<M) (hs : 0<σ)
    (measured : ∀ b,∀ e∈contacts x (letters a b),AEStronglyMeasurable (fun z=>speed (v z) e) μ)
    (thermal : ∀ b,∀ e∈contacts x (letters a b),
      Integrable (fun z=>speed (v z) e^(q+1)) μ ∧
        (∫ z,speed (v z) e^(q+1) ∂μ)≤M^(q+1))
    (printed : AEStronglyMeasurable
      (fun z=>(a.unmasked (field (v z) t) x:ℂ)-polynomial a x (v z) q t) μ) :
    Integrable (fun z=>(a.unmasked (field (v z) t) x:ℂ)-polynomial a x (v z) q t) μ ∧
    (∫ z,‖(a.unmasked (field (v z) t) x:ℂ)-polynomial a x (v z) q t‖ ∂μ)≤
      a.budget σ*(2*M*|t|/σ)^(q+1) := by
  let fee (b : Fin k→G.ColorIndex) (z : Ω):=|a.coeff b| *
    (score (v z) x (letters a b)^(q+1)*|t|^(q+1)/(q+1).factorial)
  have income b:=score_moment μ v q pos a x b (measured b) (thermal b)
  have hi b : Integrable (fee b) μ :=
    (((income b).1.mul_const (|t|^(q+1))).div_const _).const_mul _
  have whole:=integrable_finsetSum (s:=Finset.univ) (fun b _=>hi b)
  have bounded (z : Ω):=atom_path_error a x (v z) q t
  have actual:=whole.mono' printed (ae_of_all μ bounded)
  refine ⟨actual,(integral_mono actual.norm whole bounded).trans ?_⟩
  rw [integral_finsetSum _ (fun b _=>hi b)]
  apply le_trans _ (length_taylor a hs pos.le q t)
  unfold Atom.magnitude
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  simp only [fee,integral_const_mul,integral_div,integral_mul_const]
  gcongr
  exact (income b).2

end YM.Integration.OriginalMarkedRunAction
