import YM.Integration.FVA1Physical.Wilson.ForestAverageData

/-! Integration over the genuine forest conditional. The analytic error is proportional
to the integrated physical reading, uniformly over the height of the forest density. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson Tree MSbar MSbar.Bulk MSbar.Heath MSbar.Heath.Cottage
open scoped Classical Topology

private theorem average_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p s : Ω→ℝ} {D a δ b v : ℝ} (pint : Integrable p μ) (sm : Measurable s)
    (a₀ : 0 ≤ a) (bound : ∀ x,|s x-p x|≤D+a*(p x+D))
    (physical : |(∫ x,p x ∂μ)-v| ≤ δ) (read : v ≤ b) :
    |(∫ x,s x ∂μ)-v| ≤ D+a*(b+δ+D)+δ := by
  let major := fun x=>D+a*(p x+D)
  have hD : Integrable (fun _ : Ω=>D) μ := integrable_const _
  have hM : Integrable major μ := hD.add ((pint.add hD).const_mul a)
  have hd : Integrable (fun x=>s x-p x) μ := hM.mono'
    (sm.aestronglyMeasurable.sub pint.aestronglyMeasurable) (Eventually.of_forall fun x=>
      (Real.norm_eq_abs _).trans_le (bound x))
  have hi : Integrable s μ := (hd.add pint).congr (Eventually.of_forall fun x=>sub_add_cancel ..)
  have est := norm_integral_le_of_norm_le hM (Eventually.of_forall fun x=>
    (Real.norm_eq_abs (s x-p x)).trans_le (bound x))
  rw [Real.norm_eq_abs,integral_sub hi pint] at est
  have hm : (∫ x,major x ∂μ)=D+a*((∫ x,p x ∂μ)+D) := by
    change ∫ x,D+a*(p x+D) ∂μ=_
    have ha : Integrable (fun x=>a*(p x+D)) μ := (pint.add hD).const_mul a
    rw [integral_add hD ha,integral_const_mul,integral_add pint hD]
    simp
  have hval : (∫ x,p x ∂μ) ≤ b+δ := by linarith only [(abs_le.mp physical).2,read]
  rw [hm] at est
  exact (abs_sub_le _ (∫ x,p x ∂μ) _).trans (add_le_add
    (est.trans (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left hval D) a₀) D)) physical)

variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f}
variable {V : Config G c} {F : Forest S.ratio} {X Y : Support f}
variable {A : Set (Config G f)} {r : Config G f→ℝ} {a κ σ C δ Λ w b ε ψ χ : ℝ}
local notation "I" => board F X
local notation "E" => expect S R V

/-- The free-link Haar probabilities average the true forest resampler. In the
resulting Wilson cost, the coefficient of the local analytic error sees the measured
test bound and the calibration error. The forced-gas charge remains explicit. -/
theorem forest_average (adm : Admitted V R S σ C δ Λ w) (rota : Rota (S:=S) R V Y F I A r a κ)
    (tact : Tonic.Loan.Tact (S:=S) F X A r Y R V b χ) (B : Config G f→ℝ) (meas : Measurable B)
    (φ : Config G f→ℝ) (localφ : GaugeLocal S Y φ) (_φ₀ : 0≤φ) (φb : ∀ U,φ U≤b) (e₀ : 0≤ε)
    (tracked : ∀ θ : IV F I G,
      let q := Rota.ghat (F:=F) (X:=I) r θ φ A
      |compass S R V F X A r B φ θ-E q| ≤ ψ+ε*(E q+ψ)) :
    |(∫ θ,compass S R V F X A r B φ θ ∂fence F I G)-E φ| ≤ ψ+ε*(b+χ+ψ)+χ := by
  let W := fun θ : IV F I G=> E (Rota.ghat (F:=F) (X:=I) r θ φ A)
  have hW : Integrable W (fence F I G) := by
    unfold W; simp_rw [readsX adm]
    exact ((unroll (μ:=prior G f) (Rota.modern adm rota φ localφ)).integrable (fence F I G)).div_const _
  have physical := tact.main φ localφ _φ₀ φb
  rw [Rota.lands adm rota φ localφ] at physical
  have direct : E φ≤b := (nn V adm (Envelope.const b) localφ.currency φb).trans_eq (e_const V adm b)
  exact average_error (p:=W) (s:=compass S R V F X A r B φ) (D:=ψ) (a:=ε) (δ:=χ) (v:=E φ) (b:=b)
    (fence F I G) hW (compass_meas adm rota meas localφ) e₀ tracked physical direct
end YM.Integration.FVA1Physical.Wilson
