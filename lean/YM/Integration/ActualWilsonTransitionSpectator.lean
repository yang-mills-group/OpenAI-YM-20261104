import YM.Integration.ActualWilsonAbsoluteTransport
import YM.Push.SECTOR_MEASURE.Bounds

/-! The actual Bayes read of a signed insertion depending on the original tag,
the fine field and the very same outgoing field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonTransitionSpectator
open Function Filter Finset MeasureTheory Lattice Wilson RG OPE.Therm
open YM.Push.SectorMeasure
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} (S : StepData c f)
    (h : S.patch.Branches S.kernel G) (β : ℝ)

theorem sum_kernel (U : Config G f) (V : Config G c) :
    ∑ t:S.Choices,taggedKernel S β t U V = S.density β U V := rfl

include h in
theorem density_pos (U : Config G f) (V : Config G c) : 0 < S.density β U V := by
  rw [←sum_kernel]
  have hu : ∃ t:S.Choices,0<S.likelihood U t := by
    by_contra! hn
    have he : ∑ t:S.Choices,S.likelihood U t=0 :=
      Finset.sum_eq_zero fun i _=>le_antisymm (hn i) (S.likelihood_pos U i)
    linarith [S.chosen h U]
  obtain ⟨t,ht⟩ := hu
  exact Finset.sum_pos' (fun i _=>kernel_nonneg β i U V)
    ⟨t,Finset.mem_univ _,mul_pos ht (noise_pos β _ _)⟩

def share (t : S.Choices) (U : Config G f) (V : Config G c) : ℝ :=
  taggedKernel S β t U V / S.density β U V

theorem share_nonneg (t : S.Choices) (U : Config G f) (V : Config G c) : 0 ≤ share S β t U V :=
  div_nonneg (kernel_nonneg ..) (S.density_positive ..)

include h in
theorem share_total (U : Config G f) (V : Config G c) : ∑ t:S.Choices,share S β t U V=1 := by
  unfold share
  rw [←Finset.sum_div,sum_kernel,div_self (density_pos S h β U V).ne']

def tagged (Z : S.Choices → Config G f × Config G c → ℂ) (U : Config G f) (V : Config G c) : ℂ :=
  ∑ t:S.Choices,share S β t U V • Z t (U,V)

include h in
theorem tagged_bound (Z : S.Choices → Config G f × Config G c → ℂ)
    (U : Config G f) (V : Config G c) (b : ℝ) (hz : ∀ t,‖Z t (U,V)‖≤b) :
    ‖tagged S β Z U V‖≤b := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ t:S.Choices,‖share S β t U V • Z t (U,V)‖ ≤ ∑ t:S.Choices,share S β t U V*b := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul,Real.norm_of_nonneg (share_nonneg S β t U V)]
      exact mul_le_mul_of_nonneg_left (hz t) (share_nonneg S β t U V)
    _ = b := by rw [←Finset.sum_mul,share_total S h β U V,one_mul]

include h in
theorem tagged_meas (Z : S.Choices → Config G f × Config G c → ℂ) (hz : ∀ t,Measurable (Z t)) :
    Measurable fun z : Config G f × Config G c=>tagged S β Z z.1 z.2 := by
  apply Finset.measurable_sum
  intro t _
  exact (((env_tagged β t h measurable_fst measurable_snd).meas).div (S.density_meas h β)).smul (hz t)

variable (C : Family G) {N m p : ℕ} (hC : C.Makes) (hm : m<N)
local notation "op" => C.path.levels.clock.op m p
local notation "rate" => C.path.β N p (m+1)
local notation "fine" => Config G (C.side (m+1) p)
local notation "coarse" => Config G (C.side m p)

def read (Z : (op).Choices → (fine) × (coarse) → ℂ) (V : coarse) :=
  actualAverage C (N:=N) (fun U=>tagged op rate Z U V) V

include hC hm in
theorem realized (Z : (op).Choices → (fine) × (coarse) → ℂ) (V : coarse) :
    read C (N:=N) Z V = ((C.path.rep N p m).eval V)⁻¹ •
      ∫ U,∑ t:(op).Choices,taggedKernel op rate t U V • ((C.path.rep N p (m+1)).eval U • Z t (U,V))
        ∂prior G (C.side (m+1) p) := by
  unfold read actualAverage
  rw [←integral_smul]
  apply integral_congr_ae
  filter_upwards with U
  simp only [tagged,actualConditionalDensity,share,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  have hr := (density_pos op (C.path.levels.blocks m p).branches rate U V).ne'
  have hv := (Multi.AxisShift.chosen_positive hC.wilson hm.le V).ne'
  field_simp [hr,hv]

include hC hm in
theorem measurable (Z : (op).Choices → (fine) × (coarse) → ℂ) (hz : ∀ t,Measurable (Z t)) : Measurable (read C (N:=N) Z) := by
  let P (z : coarse×fine) := actualConditionalDensity C N p m z.1 z.2
  have hb := (C.path.levels.blocks m p).branches
  have hF := ((C.path.rep N p (m+1)).envelope (hC.wilson.represents N p (m+1) hm).good).meas
  have hB := ((C.path.rep N p m).envelope (hC.wilson.represents N p m hm.le).good).meas
  have hp : Measurable P := ((((op).density_meas hb rate).comp measurable_swap).mul
    (hF.comp measurable_snd)).div (hB.comp measurable_fst)
  have hZ := (tagged_meas op hb rate Z hz).comp measurable_swap
  change Measurable (fun V=>∫ U,P (V,U) • tagged op rate Z U V ∂prior G (C.side (m+1) p))
  exact (hp.smul hZ).stronglyMeasurable.integral_prod_right'.measurable

include hC hm in
theorem bounded (Z : (op).Choices → (fine) × (coarse) → ℂ) (b : ℝ) (hz : ∀ t U V,‖Z t (U,V)‖≤b) (V : coarse) :
    ‖read C (N:=N) Z V‖≤b :=
  actualAverage_norm_le C hC hm (fun U=>tagged_bound op (C.path.levels.blocks m p).branches rate Z U V b
    (fun t=>hz t U V)) V

end YM.Integration.ActualWilsonTransitionSpectator
end
