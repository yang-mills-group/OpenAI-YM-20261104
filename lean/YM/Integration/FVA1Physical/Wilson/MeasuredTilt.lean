import YM.Integration.FVA1Physical.Wilson.ForcedTransport
import YM.MSbar.Cottage.Draw

/-! Defect after a tracked forest change, relative to the mass of the actual test. This form can be averaged over the forest group without the large pointwise height of the resampling density. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set MeasureTheory RG Lattice YM.Wilson MSbar MSbar.Bulk PhysicalNext.Repeat.Lotus
open scoped Topology Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f}

/-- `bank` approximates the exponent change on the support of the tested local
move. The tested error is normalized by the true interacting partition function,
with all actual failed arrangements present. The test can have either sign after
taking differences of the two nonnegative parts. -/
theorem tracked_mass_price {σ C δ Λ w v y a ε : ℝ} {X : Support f}
    {κ : Config G f → Config G f} {q : Config G f→ℝ} (V : Config G c)
    (adm : Admitted V R S σ C δ Λ w) (track : Tracks R X κ q S a) (qa : ∀ U, 0≤q U)
    (arsenal : MergeProof.Menu.Arsenal R) (psalm : Psalm S R v y) (hy : 0≤y) (out : flags v V=∅)
    (bank : Config G f→ℝ) (mBank : Measurable bank) (ε₀ : 0≤ε) (small : ε≤1)
    (price : ∀ U, q U≠0 → |bank U-(R.exponent U - R.exponent (κ U))|≤ε) :
    let Z := S.push R.beta R.eval V
    let charge := y * (R.p.mass X (a*2) * Real.exp (X.card*w))
    |(S.push R.beta (fun U=>q U*(R.eval (κ U)*Real.exp (bank U))) V -
      S.push R.beta (fun U=>q U*R.eval U) V)/Z| ≤ charge + 2*ε*(expect S R V q+charge) := by
  intro Z charge
  let μ := prior G f
  let K := fun U=>S.density R.beta U V
  let E := fun U=>R.exponent U-R.exponent (κ U)
  let T₀ := fun U=>K U*(q U*R.eval U)
  let T₁ := fun U=>K U*(q U*(R.eval (κ U)*Real.exp (E U)))
  let T₂ := fun U=>K U*(q U*(R.eval (κ U)*Real.exp (bank U)))
  have qenv : Envelope q := ⟨track.track,a,track.blood⟩
  have revenv := R.envelope adm.lawful
  have Eenv : Envelope E := by
    unfold E; simp_rw [sub_eq_add_neg]; exact (R.exponentEnv adm.lawful).add (MSbar.Heath.Cottage.backdrop (R.exponentEnv adm.lawful) track.live).neg
  have i₀ : Integrable T₀ μ := StepData.push_slice adm.kernel V _ ((qenv.mul revenv).integrable _)
  have i₁ : Integrable T₁ μ := StepData.push_slice adm.kernel V _
    ((qenv.mul ((MSbar.Heath.Cottage.backdrop revenv track.live).mul Eenv.exp)).integrable _)
  have hZ : 0<Z := adm.mass
  have T₁pos U : 0≤T₁ U := mul_nonneg (adm.kernel.positive ..)
    (mul_nonneg (qa _) (mul_nonneg (adm.positive _) (Real.exp_pos _).le))
  have base : (∫ U,T₀ U ∂μ)=expect S R V q*Z := by
    change (∫ U,T₀ U ∂μ)=((∫ U,T₀ U ∂μ)/Z)*Z
    exact (div_mul_cancel₀ _ hZ.ne').symm
  have exactGas := Recenter.accurate track adm.lawful arsenal psalm adm.kernel V out hZ.le hy
  have realGas : |(∫ U,T₁ U ∂μ)-(∫ U,T₀ U ∂μ)|≤Z*charge := by
    have id : (∫ U,T₁ U ∂μ)-(∫ U,T₀ U ∂μ)=S.push R.beta
        (fun U=>q U*(R.eval (κ U)*Real.exp (E U)-R.eval U)) V := by
      rw [←integral_sub i₁ i₀]
      apply integral_congr_ae; filter_upwards with U
      change K U*(q U*(R.eval (κ U)*Real.exp (E U)))-K U*(q U*R.eval U)=
        K U*(q U*(R.eval (κ U)*Real.exp (E U)-R.eval U));ring
    rw [id];exact exactGas
  have upper : (∫ U,T₁ U ∂μ)≤Z*(expect S R V q+charge) := by linarith only [(abs_le.mp realGas).2,base]
  have bound U : ‖T₂ U-T₁ U‖≤(2*ε)*T₁ U := by
    by_cases blank : q U=0
    · simp only [T₂,T₁,blank,zero_mul,mul_zero,sub_self,norm_zero,le_refl]
    have h := (Real.abs_exp_sub_one_le ((price U blank).trans small)).trans (mul_le_mul_of_nonneg_left (price U blank) zero_le_two)
    have eq : T₂ U-T₁ U=(Real.exp (bank U-E U)-1)*T₁ U := by
      dsimp only [T₂,T₁]; rw [show Real.exp (bank U)= Real.exp (bank U-E U)*Real.exp (E U) by rw [←Real.exp_add,sub_add_cancel]]; ring
    rw [eq,norm_mul,Real.norm_of_nonneg (T₁pos _)]
    exact mul_le_mul_of_nonneg_right h (T₁pos U)
  have m₂ : Measurable T₂ := (adm.kernel.meas.comp (measurable_id.prodMk measurable_const)).mul
    (track.track.mul ((revenv.meas.comp track.live).mul (Real.measurable_exp.comp mBank)))
  have dI : Integrable (fun U=>T₂ U-T₁ U) μ := (i₁.const_mul (2*ε)).mono'
    (m₂.aestronglyMeasurable.sub i₁.aestronglyMeasurable) (Eventually.of_forall bound)
  have i₂ : Integrable T₂ μ := (dI.add i₁).congr (Eventually.of_forall fun U=> sub_add_cancel ..)
  have err := norm_integral_le_of_norm_le (i₁.const_mul (2*ε)) (Eventually.of_forall bound)
  rw [integral_sub i₂ i₁,integral_const_mul,Real.norm_eq_abs] at err
  change |((∫ U,T₂ U ∂μ)-(∫ U,T₀ U ∂μ))/Z| ≤ _
  rw [abs_div,abs_of_pos hZ,div_le_iff₀ hZ]
  apply (abs_sub_le (∫ U,T₂ U ∂μ) (∫ U,T₁ U ∂μ) (∫ U,T₀ U ∂μ)).trans
  have second := mul_le_mul_of_nonneg_left upper (mul_nonneg zero_le_two ε₀)
  calc
    _ ≤ (2*ε)*(Z*(expect S R V q+charge)) + Z*charge := add_le_add (err.trans second) realGas
    _ = _ := by ring

end YM.Integration.FVA1Physical.Wilson
