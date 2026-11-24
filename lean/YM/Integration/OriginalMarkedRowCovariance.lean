import YM.Integration.OriginalMarkedRunCovariance

/-! Restore the actual omitted regular potentials one by one, preserving
the entire retained physical weight and the normalization at each step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedRowCovariance
open Filter Function MeasureTheory Lattice Wilson RG
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open OriginalMarkedRunAction OriginalMarkedRunCovariance
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.alloy.B.a.S.side m p)
local notation "P" => approximation R (p:=p) hm d
local notation "I" => remainder R (p:=p) hm d
local notation "B" => R.alloy.B.a.budget m
local notation "η" => prior G (R.alloy.B.a.S.side m p)

def row (d i : ℕ) (U : Ω) : ℝ := (remainder R (p:=p) hm d).regularOccurrence B i U

def «prefix» (d j : ℕ) (U : Ω) : ℝ :=
  Real.exp (-(∑ i ∈ Finset.range j, row R (p:=p) hm d i U))

def local_weight (d i : ℕ) (U : Ω) : ℂ := (Real.exp (-row R (p:=p) hm d i U) : ℂ)

theorem flagged (U : Ω) (i : ℕ) (h : ¬ Healthy (B).threshold ((I).reg i).support U) :
    local_weight R (p:=p) hm d i U = 1 := by
  simp [local_weight,row,Activities.regularOccurrence,h]

def «partial» (d j : ℕ) (f : Ω → ℂ) : ℂ :=
  let z := fun U : Ω => («prefix» R (p:=p) hm d j U : ℂ)
  mean (approximation R (p:=p) hm d) (z*f) / mean (approximation R (p:=p) hm d) z

def density (d j : ℕ) (U : Ω) : ℝ :=
  (approximation R (p:=p) hm d).eval U * «prefix» R (p:=p) hm d j U

def read {X : Type*} [MeasurableSpace X] (μ : Measure X) (k : X → ℝ) (f : X → ℂ) : ℂ :=
  (Complex.ofReal (∫ U,k U ∂μ))⁻¹ * ∫ U,(k U:ℂ)*f U ∂μ

def local_ratio (d i : ℕ) (f : Ω → ℂ) : ℂ :=
  let L := «partial» R (p:=p) hm d i
  let z := local_weight R (p:=p) hm d i
  (L (z*f) - L f * L z) / L z

local notation "z" j:max => fun U : Ω => («prefix» R (p:=p) hm d j U : ℂ)
local notation "w" => fun U : Ω => (weight R (p:=p) hm d U : ℂ)
variable (A : Comparison R (p:=p) hm d)
include A

private theorem prefix_measurable (j : ℕ) : Measurable («prefix» R (p:=p) hm d j) := by
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  exact Finset.measurable_fun_sum _ fun i _ =>
    masked_measurable _ _ _ (A.posterior.cut.regular.smooth i).borel

private theorem prefix_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ j U, «prefix» R (p:=p) hm d j U ≤ c := by
  obtain ⟨b,sum,bound⟩ := Activities.ESeries A.posterior.cut
  have bpos (i : ℕ) : 0 ≤ b i := (norm_nonneg _).trans (bound i 1)
  refine ⟨Real.exp (∑' i,b i),(Real.exp_pos _).le,fun j U => Real.exp_le_exp.mpr ?_⟩
  calc -(∑ i ∈ Finset.range j,row R (p:=p) hm d i U) ≤
        |∑ i ∈ Finset.range j,row R (p:=p) hm d i U| := neg_le_abs _
       _ ≤ ∑ i ∈ Finset.range j,|row R (p:=p) hm d i U| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ i ∈ Finset.range j,b i :=
         Finset.sum_le_sum fun i _ => (Real.norm_eq_abs _).symm.le.trans (bound i U)
       _ ≤ _ := sum.sum_le_tsum _ fun i _ => bpos i

theorem density_envelope (j : ℕ) : Envelope (density R (p:=p) hm d j) := by
  obtain ⟨c,_,hc⟩ := prefix_bound R hm A
  have env : Envelope («prefix» R (p:=p) hm d j) :=
    ⟨prefix_measurable R hm A j,c,fun U => (Real.norm_of_nonneg (Real.exp_pos _).le).le.trans (hc j U)⟩
  exact (keep_envelope R hm A).mul env

theorem density_positive (j : ℕ) (U : Ω) : 0 < density R hm d j U :=
  mul_pos (keep_positive R hm A U) (Real.exp_pos _)

theorem normalizer_positive (j : ℕ) : 0 < ∫ U,density R (p:=p) hm d j U ∂η := by
  have positive := density_positive R hm A j
  apply (integral_pos_iff_support_of_nonneg (fun U => (positive U).le)
    ((density_envelope R hm A j).integrable η)).mpr
  rw [show Function.support (density R (p:=p) hm d j) = Set.univ from
    Set.eq_univ_of_forall fun U => (positive U).ne']
  simp

private theorem prefix_nonzero (j : ℕ) : mean P (z j) ≠ 0 := by
  unfold mean
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (mass_positive R hm A).ne'))
    (Complex.ofReal_ne_zero.mpr (normalizer_positive R hm A j).ne')

omit A in
private theorem scalar_read {s k t : ℂ} (h : s≠0) : (s⁻¹*t)/(s⁻¹*k) = k⁻¹*t := by
  rw [div_eq_mul_inv,mul_inv_rev,inv_inv]
  rw [show s⁻¹*t*(k⁻¹*s) = (s⁻¹*s)*(k⁻¹*t) by ring,inv_mul_cancel₀ h,one_mul]

theorem partial_read (j : ℕ) (f : Ω → ℂ) :
    «partial» R (p:=p) hm d j f = read η (density R (p:=p) hm d j) f := by
  have numerator : (∫ U,((P).eval U:ℂ)*((«prefix» R (p:=p) hm d j U:ℂ)*f U) ∂η) =
      ∫ U,(density R (p:=p) hm d j U:ℂ)*f U ∂η := by
    apply integral_congr_ae
    exact ae_of_all _ fun U => by simp [density,Complex.ofReal_mul,mul_assoc]
  have denominator : (∫ U,((P).eval U:ℂ)*(«prefix» R (p:=p) hm d j U:ℂ) ∂η) =
      Complex.ofReal (∫ U,density R (p:=p) hm d j U ∂η) := by
    simp_rw [← Complex.ofReal_mul]
    exact integral_complex_ofReal (μ:=η) (f:=density R (p:=p) hm d j)
  unfold «partial» mean read
  dsimp only [Pi.mul_apply]
  rw [numerator,denominator,scalar_read (Complex.ofReal_ne_zero.mpr (mass_positive R hm A).ne')]

theorem successive (i : ℕ) (f : Ω → ℂ) :
    «partial» R (p:=p) hm d (i+1) f - «partial» R (p:=p) hm d i f = local_ratio R (p:=p) hm d i f := by
  let W := z i
  let K := local_weight R (p:=p) hm d i
  let V := z (i+1)
  have append : W*K = V := by
    funext U
    simp only [W,K,V,Pi.mul_apply,«prefix»,local_weight,Finset.sum_range_succ,neg_add,
      Real.exp_add,Complex.ofReal_mul]
  have payload : W*(K*f) = V*f := by rw [← mul_assoc,append]
  change mean P (V*f)/mean P V - mean P (W*f)/mean P W =
    (mean P (W*(K*f))/mean P W - (mean P (W*f)/mean P W)*(mean P (W*K)/mean P W)) /
      (mean P (W*K)/mean P W)
  rw [append,payload]
  have hw : mean P W ≠ 0 := prefix_nonzero R hm A i
  have hv : mean P V ≠ 0 := prefix_nonzero R hm A (i+1)
  field_simp [hw,hv]

private theorem initial (f : Ω → ℂ) : «partial» R (p:=p) hm d 0 f = mean P f := by
  have one : (z 0) = 1 := by funext U; simp [«prefix»]
  unfold «partial»
  dsimp only
  rw [one,one_mul,mean_one R hm A,div_one]

private theorem prefix_tends (U : Ω) :
    Tendsto (fun j => «prefix» R (p:=p) hm d j U) atTop (𝓝 (weight R (p:=p) hm d U)) :=
  Real.continuous_exp.continuousAt.tendsto.comp
    (((Activities.ESeries A.posterior.cut).summable U).hasSum.tendsto_sum_nat.neg)

private theorem moment_tends (f : Ω → ℂ) (meas : Measurable f) (b : ℝ) (bounded : ∀ U, ‖f U‖ ≤ b) :
    Tendsto (fun j => mean P ((z j)*f)) atTop (𝓝 (mean P ((w)*f))) := by
  obtain ⟨c,hc,bound⟩ := prefix_bound R hm A
  have env := keep_envelope R hm A
  let M := fun U : Ω => (P).eval U * (c*b)
  have lim : Tendsto (fun j => ∫ U,((P).eval U:ℂ)*((«prefix» R (p:=p) hm d j U:ℂ)*f U) ∂η) atTop
      (𝓝 (∫ U,((P).eval U:ℂ)*((weight R (p:=p) hm d U:ℂ)*f U) ∂η)) := by
    apply tendsto_integral_of_dominated_convergence M
    · exact fun j => ((Complex.measurable_ofReal.comp env.meas).mul
        ((Complex.measurable_ofReal.comp (prefix_measurable R hm A j)).mul meas)).aestronglyMeasurable
    · exact (env.integrable η).mul_const _
    · refine fun j => ae_of_all _ fun U => ?_
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (keep_positive R hm A U),
        abs_of_pos (show 0<«prefix» R (p:=p) hm d j U from Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (bound j U) (bounded U) (norm_nonneg _) hc) (keep_positive R hm A U).le
    · exact ae_of_all _ fun U => tendsto_const_nhds.mul
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (prefix_tends R hm A U)).mul tendsto_const_nhds)
  exact lim.const_mul _

private theorem partial_tends (f : Ω → ℂ) (meas : Measurable f) (b : ℝ) (bounded : ∀ U, ‖f U‖ ≤ b) :
    Tendsto (fun i => «partial» R (p:=p) hm d i f) atTop (𝓝 (ActualRunCoarseReadout.expectation R N p m f)) := by
  have pop := moment_tends R hm A (1:Ω→ℂ) measurable_const 1 (fun _ => by simp)
  simp only [mul_one] at pop
  rw [ratio R hm A f]
  exact (moment_tends R hm A f meas b bounded).div pop (vacuum_ne_zero R hm A)

/-- Each summand contains one normalized covariance with one authentic
local masked row. Its normalized vacuum includes the previous rows and
the complete inherited forced gas. The cutoff comparison at the end is
the original signed physical expectation. -/
theorem localized (f : Ω → ℂ) (meas : Measurable f) (b : ℝ) (bounded : ∀ U, ‖f U‖ ≤ b) :
    Tendsto (fun j => ∑ i ∈ Finset.range j, local_ratio R (p:=p) hm d i f) atTop
      (𝓝 (ActualRunCoarseReadout.expectation R N p m f - mean P f)) := by
  have eqn (j : ℕ) :
      (∑ i ∈ Finset.range j,local_ratio R (p:=p) hm d i f) = «partial» R (p:=p) hm d j f - mean P f := by
    simp_rw [← successive R hm A]
    exact (Finset.sum_range_sub (fun i => «partial» R (p:=p) hm d i f) j).trans
      (congrArg («partial» R (p:=p) hm d j f - ·) (initial R hm A f))
  simpa only [eqn] using (partial_tends R hm A f meas b bounded).sub_const (mean P f)

end YM.Integration.OriginalMarkedRowCovariance
