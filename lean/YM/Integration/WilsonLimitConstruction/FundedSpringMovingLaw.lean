import YM.Integration.WilsonBoundedActionTilt
import YM.Integration.WilsonMovingKernelProfile
import YM.Integration.PhysicalWilsonActionConvention

/-! Native normalized angular conditionals along the true positive-coupling
Wilson family on every surviving original finite lattice. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringMovingLaw
open Function Filter Finset MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato
open RG01 RG01.Kernel Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G : Gauge} {c f : Side}

section Step
variable (S : StepData c f) (b : ℝ) (D : Config G f → ℝ)

def weight (V : Config G c) (i : S.Choices) (U : Config G f) : ℝ :=
  S.likelihood U i*S.noise b (S.prediction U i) V*D U/(S.push b D V)

private theorem measurable_tag (hh : S.patch.Branches S.kernel G) (V : Config G c)
    (i : S.Choices) :
    Measurable (fun U : Config G f => S.likelihood U i*S.noise b (S.prediction U i) V) := by
  have pair : Measurable (fun U : Config G f => (S.prediction U i,V)) :=
    (S.prediction_meas hh i).prodMk measurable_const
  have noise := Measurable.comp (S.noise_cont (G:=G) b |>.measurable) pair
  exact (S.likelihood_meas hh i).mul noise

/-- The real finite mixture on the true fine Haar prior and a positive
moving incoming density has total mass exactly one. -/
theorem caliber (hh : S.patch.Branches S.kernel G) (he : ∀ U,0<D U)
    (hD : Integrable D (prior G _)) (V : Config G c) (hd : 0<S.push b D V) :
    Kernel.Caliber (weight S b D V) (prior G f) := by
  let μ := prior G f
  let u (i : S.Choices) (U : Config G f) := S.likelihood U i*S.noise b (S.prediction U i) V
  have hp (i : S.Choices) (U : Config G f) : 0≤u i U :=
    mul_nonneg (S.likelihood_pos ..) (prod_nonneg fun j _ =>
      mul_nonneg (inv_nonneg.mpr (S.penaltyZ_pos _).le) (Real.exp_pos _).le)
  have ht (i : S.Choices) : Measurable (u i) := measurable_tag S b hh V i
  obtain ⟨C,hC⟩ := S.density_bound hh b
  have hK (i : S.Choices) (U : Config G f) : ‖u i U‖≤C := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hp _ _)]
    exact (Finset.single_le_sum (f:=fun i=>u i U) (fun _ _=>hp _ _) (mem_univ i)).trans (hC U V)
  have hi i : Integrable (fun U => u i U*D U) μ :=
    hD.bdd_smul C (ht i).aestronglyMeasurable (ae_of_all _ (hK i))
  refine ⟨fun i => (hi i).div_const _,fun i U => div_nonneg (mul_nonneg (hp i U) (he U).le) hd.le,?_⟩
  change ∑ i : S.Choices,(∫ U, u i U*D U/(S.push b D V) ∂μ)=_
  conv_lhs => enter [2,i]; rw [integral_div]
  rw [←Finset.sum_div]
  apply (div_eq_one_iff_eq hd.ne').mpr
  change ∑ i : S.Choices, (∫ U,u i U*D U ∂μ) = ∫ U, (∑ i : S.Choices,u i U)*D U ∂μ
  rw [←integral_finsetSum univ (fun i _=>hi i)]
  simp only [Finset.sum_mul]

/-- The full original signed observation may be marked independently on
every block choice and fine field. -/
theorem transfer (V X : Config G c) (positive : 0<S.push b D X)
    (a : S.Choices → Config G f → ℂ) (e : Edge (Site c) → ℝ)
    (support : ∀ i,e i=0 → X i=V i) :
    Kernel.generating (weight S b D V) (Kernel.channel S b e V) (prior G f) a
        (Kernel.encoded e V X) =
      ((S.push b D X : ℝ):ℂ)/((S.push b D V:ℝ):ℂ) * Kernel.moment (weight S b D X) (prior G f) a := by
  unfold Kernel.generating Kernel.moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  let Z (Y : Config G c) : ℂ := S.noise b (S.prediction U i) Y
  let q := Complex.exp (Kernel.script S b e V i U (Kernel.encoded e V X))
  have hx : q*Z V=Z X := Kernel.noiseReal S b e V i X support U
  have hX : ((S.push b D X:ℝ):ℂ)≠0 := by exact_mod_cast positive.ne'
  change (↑(S.likelihood U i*S.noise b (S.prediction U i) V*D U / S.push b D V):ℂ)*(a i U*q) =
    _*((↑(S.likelihood U i*S.noise b (S.prediction U i) X*D U/S.push b D X):ℂ)*a i U)
  push_cast
  change (↑(S.likelihood U i)*Z V*↑(D U)/((S.push b D V:ℝ):ℂ))*(a i U*q) =
    _*((↑(S.likelihood U i)*Z X*↑(D U)/((S.push b D X:ℝ):ℂ))*a i U)
  rw [←hx]
  by_cases hv : ((S.push b D V:ℝ):ℂ)=0
  · simp [hv]
  · field_simp [hX,hv]

theorem ratio (hh : S.patch.Branches S.kernel G) (he : ∀ U,0<D U)
    (hD : Integrable D (prior G _)) (V X : Config G c) (hX : 0<S.push b D X)
    (e : Edge (Site c) → ℝ) (support : ∀ i,e i=0 → X i=V i) :
    Kernel.generating (weight S b D V) (Kernel.channel S b e V) (prior G f) 1
        (Kernel.encoded e V X) = ((S.push b D X:ℝ):ℂ)/((S.push b D V:ℝ):ℂ) := by
  simpa only [(caliber S b D hh he hD X hX).unit,mul_one] using
    transfer S b D V X hX 1 e support
end Step

variable (R : Run G) (N p : ℕ) (t : ℝ)
local notation "γ" => WilsonMovingKernelProfile.value R N p t

def density (m : ℕ) (h : m≤N) : Config G (R.family.side m p) → ℝ :=
  WilsonCouplingTransport.density R.family N p (γ N) γ m h

def action (m : ℕ) (h : m≤N) (U : Config G (R.family.side m p)) : ℝ :=
  -Real.log (density R N p t m h U)

theorem positive (m : ℕ) (h : m≤N) (U : Config G (R.family.side m p)) : 0<density R N p t m h U :=
  WilsonBoundedActionTilt.carry_positive R.family p N γ (bare (γ N)) (bare_integrable _)
    (bare_pos _) m h U

/-- Every actual original survivor on the selected schedule is recovered
exactly, without changing the path or the bare Wilson density. -/
theorem endpoint (m : ℕ) (h : m≤N) (U : Config G (R.family.side m p)) :
    action R N p (regulatorRun R.family N p N) m h U =
      PhysicalWilsonActionConvention.physicalAction R N p m U := by
  unfold action density PhysicalWilsonActionConvention.physicalAction
  rw [WilsonMovingKernelProfile.endpoint]
  exact congrArg (fun f : Config G (R.family.side m p) → ℝ => -Real.log (f U))
    (WilsonCouplingTransport.physical_density R.family R.makes N p h)

theorem bare_action (ht : t≠0) (U : Config G (R.family.side N p)) :
    action R N p t N le_rfl U=(t^2)⁻¹*Wilson.energy U := by
  unfold action density WilsonCouplingTransport.density
  rw [WilsonCouplingTransport.top,WilsonMovingKernelProfile.at_top R N p ht,Wilson.bare,Real.log_exp]
  ring

/-- The original Haar angular generating law computes the exact positive
moving action difference for every cutoff, surviving station and opening. -/
theorem conditional {m : ℕ} (h : m<N) (V X : Config G (R.family.side m p))
    (e : Edge (Site (R.family.side m p)) → ℝ) (support : ∀ i,e i=0 → X i=V i) :
    let S := R.family.path.levels.clock.op m p
    let D := density R N p t (m+1) h
    (-Real.log ‖Kernel.generating (weight S (γ (m+1)) D V) (Kernel.channel S (γ (m+1)) e V)
      (prior G _) 1 (Kernel.encoded e V X)‖) =
      action R N p t m h.le X-action R N p t m h.le V := by
  intro S D
  have step : S.push (γ (m+1)) D=density R N p t m h.le :=
    (WilsonCouplingTransport.step R.family p N γ (bare (γ N)) h).symm
  have hp (U : Config G (R.family.side (m+1) p)) : 0<D U := positive R N p t (m+1) h U
  have integrated : Integrable D (prior G _) :=
    WilsonCouplingTransport.integrable R.family p N γ (bare_integrable (γ N)) h
  have hX := positive R N p t m h.le X
  have hV := positive R N p t m h.le V
  have px : 0<S.push (γ (m+1)) D X := by rw [step]; exact hX
  rw [ratio S (γ (m+1)) D (R.family.path.levels.blocks m p).branches hp integrated V X px e support,step,
    norm_div,Complex.norm_real,Real.norm_of_nonneg hX.le,Complex.norm_real,Real.norm_of_nonneg hV.le,
    Real.log_div hX.ne' hV.ne']
  unfold action
  ring

end YM.Integration.WilsonLimitConstruction.FundedSpringMovingLaw
end
