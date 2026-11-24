import YM.Integration.FVA1Physical.Wilson.LogTilt
import YM.PECompat4984.Donor.BetaBlock

/-! Replacing the inherited interacting action in an actual tagged transition, on
regular blocks of bounded total coordinate excursion. The full kernel, Haar choice,
all mixed insertions and the output vacuum denominator are common to the two tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson
open scoped Classical
variable {G : Gauge} {c f : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 850000 in
theorem kernel_tilt (S : StepData c f) (h : S.patch.Branches S.kernel G) (β : ℝ) (V : Config G c)
    (Q : Config G f → ℝ) (hQ : RG.Envelope Q) (pos : ∀ U, 0<Q U) (P : Config G f → ℝ)
    (μ : Measure (Config G f)) [IsFiniteMeasure μ] (hmass : 0<μ Set.univ)
    (hP : AEMeasurable P μ) (center δ : ℝ) (hδ : 0 ≤ δ)
    (relative : ∀ᵐ U ∂μ, |Real.log (Q U)-P U-center| ≤ δ)
    (F : Config G f→E) (hF : AEStronglyMeasurable F μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ U ∂μ, ‖F U‖ ≤ M) :
    ‖patchMean μ (fun U=>S.density (G:=G) β U V * Q U) F -
      patchMean μ (fun U=>S.density (G:=G) β U V * Real.exp (P U)) F‖ ≤ (Real.exp (2*δ)-1)*M := by
  let K := fun U : Config G f => S.density (G:=G) β U V
  have kp (U : Config G f) : 0 < K U := Push.BetaTransport.density_pos S h β U V
  have km : Measurable K := by
    change Measurable ((fun p : Config G f × Config G c=> S.density (G:=G) β p.1 p.2) ∘ fun U : Config G f=>(U,V))
    exact (S.density_meas h β).comp (measurable_id.prodMk measurable_const)
  obtain ⟨D,hD⟩ := S.density_bound h β
  have env : RG.Envelope K := ⟨km,D,fun U=>by rw [Real.norm_of_nonneg (kp U).le];exact hD U V⟩
  exact log_tilt K Q P μ hmass kp pos km ((env.mul hQ).integrable μ) hP center δ hδ relative F hF hM hbound

end YM.Integration.FVA1Physical.Wilson
