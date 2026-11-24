import YM.Integration.WilsonPositionProgramNormalizedInversion

/-! Real angular series and the finite complex inversion Taylor series
can be compared at the actual full-link tangent of the inversion tree. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramRayChart
open Function Filter Set Finset PowerSeries Lattice WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology ContDiff
variable {I J E : Type*} [Fintype I] [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diagonal (f : Lawn I → ℝ) (n : ℕ) (v : Lawn I) :
    MvPolynomial.eval v (coeff n (jet f)) =
      (n.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _=>v) := by
  rw [jet_apply, toll]
  let A := iteratedFDeriv ℝ n f 0
  have expand := A.map_sum (fun (_ : Fin n) i => v i • pebble i)
  simp only [←redeploy v] at expand
  change (∑ i : Fin n→I, rye f n i * ∏ j, v (i j)) =
    (n.factorial:ℝ)⁻¹ * A (fun _=>v)
  rw [expand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [A.map_smul_univ (fun j=>v (i j)) (fun j=>pebble (i j))]
  change (n.factorial:ℝ)⁻¹ * A (pebble ∘ i) * _ = _ * (_ * A (pebble ∘ i))
  ring

theorem composition (F : E →L[ℝ] Lawn I) (f : Lawn I → ℝ) (green : Green f) (n : ℕ) :
    iteratedFDeriv ℝ n (f ∘ F) 0 =
      (iteratedFDeriv ℝ n f 0).compContinuousLinearMap (fun _ => F) := by
  obtain ⟨V,V0,hV⟩ := green.contDiffOn (m:=(n:ℕ∞ω)) le_top (fun _=>rfl)
  let O := interior V
  have opened : IsOpen O := isOpen_interior
  have above : (0:Lawn I)∈O := mem_interior_iff_mem_nhds.mpr V0
  have below : (0:E)∈F ⁻¹' O := by simpa only [Set.mem_preimage,map_zero] using above
  have op := opened.preimage F.continuous
  have s := F.iteratedFDerivWithin_comp_right (hV.mono interior_subset) opened.uniqueDiffOn op.uniqueDiffOn
    (x:=0) (show F 0∈O from below) le_rfl
  have h := green.of_le (show (n:ℕ∞ω)≤ω from le_top)
  have h' : ContDiffAt ℝ n (f ∘ F) 0 := (by simpa only [map_zero] using h : ContDiffAt ℝ n f (F 0)).comp 0 F.contDiff.contDiffAt
  rw [map_zero,
    iteratedFDerivWithin_eq_iteratedFDeriv opened.uniqueDiffOn h above,
    iteratedFDerivWithin_eq_iteratedFDeriv op.uniqueDiffOn h' below] at s
  exact s

def coefficients (b : Module.Basis J ℝ E) (F : E →L[ℝ] Lawn I) : Matrix I J ℝ :=
  fun i j => F (b j) i

omit [Fintype I] in
theorem coordinates (b : Module.Basis J ℝ E) (F : E →L[ℝ] Lawn I) (x : E) :
    Matrix.mulVec (coefficients b F) (fun j=> b.repr x j) = F x := by
  funext i
  calc
    _ = F (∑ j, b.repr x j • b j) i := by
      rw [map_sum, Finset.sum_apply]
      simp only [map_smul,Pi.smul_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = _ := congrArg (fun v=> F v i) (b.sum_repr x)

def pull (b : Module.Basis J ℝ E) (F : E →L[ℝ] Lawn I) :
    Ink I →+* PowerSeries (XSpace.Taylor.Pol J) :=
  (PowerSeries.map (MvPolynomial.map (algebraMap ℝ ℂ))).comp (loom (coefficients b F))

omit [Fintype J] in
theorem painted (b : Module.Basis J ℝ E) (x : E) (q : MvPolynomial J ℝ) :
    XSpace.Taylor.evalAt b x (MvPolynomial.map (algebraMap ℝ ℂ) q) =
      (MvPolynomial.eval (fun j=>b.repr x j) q : ℝ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [XSpace.Taylor.evalAt]
  | add p q h k => simp only [map_add,h,k,Complex.ofReal_add]
  | mul_X p j h => simp [XSpace.Taylor.evalAt] at h ⊢; exact Or.inl h

theorem original (b : Module.Basis J ℝ E) (F : E →L[ℝ] Lawn I) (f : Lawn I→ℝ) (green : Green f) :
    pull b F (jet f) = XSpace.Taylor.expandTaylor b (Complex.ofRealCLM ∘ (f ∘ F)) := by
  apply PowerSeries.ext
  intro n
  apply XSpace.Taylor.from_real b
  intro x
  have hn : ContDiffAt ℝ n (f ∘ F) 0 := (by simpa only [map_zero] using
    (green.of_le (show (n:ℕ∞ω)≤ω from le_top)) : ContDiffAt ℝ n f (F 0)).comp 0 F.contDiff.contDiffAt
  rw [pull,RingHom.comp_apply,coeff_map,loom,coeff_map,XSpace.Taylor.expandTaylor,coeff_mk]
  rw [painted]
  change ((MvPolynomial.eval (fun j=>b.repr x j)
    (cord (coefficients b F) (coeff n (jet f)))) : ℂ) =
      XSpace.Taylor.evalAt b x (XSpace.Taylor.divided b n (Complex.ofRealCLM ∘ (f ∘ F)))
  rw [cord_apply,coordinates,diagonal,XSpace.Taylor.divided_realEval b n _ hn,composition F f green]
  rfl

end YM.Integration.WilsonPositionProgramRayChart
end
