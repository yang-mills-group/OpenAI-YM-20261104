import YM.Integration.OriginalMarkedExteriorReweight

/-! Redrawing a finite block with a relative action of bounded oscillation
has a pointwise Radon--Nikodym bound against the original full density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRelativeMoment
open Lattice Wilson RG MeasureTheory SelectedCofactorChamberMarginal OriginalMarkedExteriorHaar
open scoped Classical
variable {G : Gauge} {n : Side}
local notation "Ω" => Config G n

private theorem compare {P Q J : Ω→ℝ} (given : ∀ U,P U=Q U*Real.exp (-J U)) (U Y : Ω) :
    Q U*P Y=(P U*Q Y)*Real.exp (J U-J Y) := by
  have charge : Real.exp (-J U)*Real.exp (J U-J Y)=Real.exp (-J Y) := by
    rw [←Real.exp_add,show -J U+(J U-J Y)= -J Y by ring]
  rw [given Y,given U,←charge]
  ring

/-- Absolute continuity for the actual full redraw. Each fiber comparison
is centered at the field being evaluated, giving one exponential. -/
theorem ratio (A : Set (Edge (Site n))) {P Q J : Ω→ℝ} (hp : Envelope P) (hq : Envelope Q)
    (given : ∀ U,P U=Q U*Real.exp (-J U)) {floor : ℝ} (good : 0<floor) (low : ∀ U,floor≤Q U)
    {a : ℝ} (osc : ∀ U Y,((cut G A) U).1=((cut G A) Y).1 → |J U-J Y|≤a) (U : Ω) :
    Real.exp (-a)*P U≤OriginalMarkedExteriorReweight.density A P Q U ∧
      OriginalMarkedExteriorReweight.density A P Q U≤Real.exp a*P U := by
  let u := ((cut G A) U).1
  let μ := sheet G Aᶜ
  let z (y : Fields G Aᶜ) := (cut G A).symm (u,y)
  have mx : Measurable z := (cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)
  have pi : Integrable (fun y => P (z y)) μ := by
    obtain ⟨c,hc⟩ := hp.cost
    exact (⟨hp.meas.comp mx,c,fun y => hc (z y)⟩ : Envelope (fun y => P (z y))).integrable μ
  have qi : Integrable (fun y => Q (z y)) μ := by
    obtain ⟨c,hc⟩ := hq.cost
    exact (⟨hq.meas.comp mx,c,fun y => hc (z y)⟩ : Envelope (fun y => Q (z y))).integrable μ
  have qp (y) : 0<Q y := good.trans_le (low y)
  have pu : 0<P U := by rw [given U]; exact mul_pos (qp U) (Real.exp_pos _)
  have pair (y) :
      (Real.exp (-a)*P U)*Q (z y)≤Q U*P (z y) ∧ Q U*P (z y)≤(Real.exp a*P U)*Q (z y) := by
    have same : ((cut G A) U).1=((cut G A) (z y)).1 := by simp only [z,MeasurableEquiv.apply_symm_apply,u]
    obtain ⟨lo,hi⟩ := abs_le.mp (osc U (z y) same)
    have h := compare given U (z y)
    rw [h]
    constructor
    · calc
        _ = (P U*Q (z y))*Real.exp (-a) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr lo) (mul_nonneg pu.le (qp _).le)
    · calc
        _ ≤ (P U*Q (z y))*Real.exp a := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) (mul_nonneg pu.le (qp _).le)
        _ = _ := by ring
  have l := integral_mono (qi.const_mul (Real.exp (-a)*P U)) (pi.const_mul (Q U)) (fun y => (pair y).1)
  have h := integral_mono (pi.const_mul (Q U)) (qi.const_mul (Real.exp a*P U)) (fun y => (pair y).2)
  simp only [integral_const_mul] at l h
  have den : 0 < marginal A Q u := good.trans_le (marginal_lower A hq low u)
  have eq : OriginalMarkedExteriorReweight.density A P Q U=
      (Q U*marginal A P u)/marginal A Q u := by
    unfold OriginalMarkedExteriorReweight.density OriginalMarkedExteriorReweight.ratio
    rw [div_eq_mul_inv,mul_assoc]
  rw [eq]
  exact ⟨(le_div_iff₀ den).2 l,(div_le_iff₀ den).2 h⟩

theorem deviation {p h a : ℝ} (pp : 0≤p) (lo : Real.exp (-a)*p≤h) (hi : h≤Real.exp a*p) :
    |p-h|≤(Real.exp a-1)*p := by
  have convex : 2-Real.exp a≤Real.exp (-a) := by linarith [Real.add_one_le_exp a,Real.add_one_le_exp (-a)]
  have lower := (mul_le_mul_of_nonneg_right convex pp).trans lo
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The invoice is the true original first absolute moment. Only the
reference normalization and the measured marked mass occur in the price. -/
theorem integral (A : Set (Edge (Site n))) {P Q J : Ω→ℝ} (hp : Envelope P) (hq : Envelope Q)
    (given : ∀ U,P U=Q U*Real.exp (-J U)) {floor : ℝ} (good : 0<floor) (low : ∀ U,floor≤Q U)
    {a : ℝ} (osc : ∀ U Y,((cut G A) U).1=((cut G A) Y).1 → |J U-J Y|≤a)
    (f : Ω→ℂ) (hf : Envelope f) :
    ‖average (prior G n) P f-average (prior G n) P (projected A Q (fun U => Q U • f U))‖ ≤
      (Real.exp a-1)*((∫ U,P U ∂prior G n)⁻¹ * ∫ U,P U*‖f U‖ ∂prior G n) := by
  letI : IsFiniteMeasure (prior G n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Edge (Site n) => G.probHaar))
  let μ := prior G n
  let D := OriginalMarkedExteriorReweight.density A P Q
  let Z := ∫ U,P U ∂μ
  have pp (U) : 0<P U := by rw [given U]; exact mul_pos (good.trans_le (low U)) (Real.exp_pos _)
  have zp : 0<Z := by
    apply (integral_pos_iff_support_of_nonneg (fun U => (pp U).le) (hp.integrable μ)).2
    rw [show Function.support P=Set.univ from Set.eq_univ_of_forall fun U => (pp U).ne']
    simp [μ]
  have enD : Envelope D := OriginalMarkedExteriorReweight.bounded A hp hq good low
  have pi : Integrable (fun U => (P U:ℂ)*f U) μ := weighted_integrable hp hf μ
  have di : Integrable (fun U => (D U:ℂ)*f U) μ := weighted_integrable enD hf μ
  have normf : Envelope (fun U => ‖f U‖) := by
    obtain ⟨c,hc⟩ := hf.cost
    exact ⟨hf.meas.norm,c,fun U => (Real.norm_of_nonneg (norm_nonneg _)).le.trans (hc U)⟩
  have fin := (hp.mul normf).integrable μ
  have adj (U) : |P U-D U|≤(Real.exp a-1)*P U :=
    let h := ratio A hp hq given good low osc U
    deviation (pp U).le h.1 h.2
  have bound : ‖∫ U,(P U:ℂ)*f U-(D U:ℂ)*f U ∂μ‖ ≤ (Real.exp a-1)*(∫ U,P U*‖f U‖ ∂μ) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le (fin.const_mul (Real.exp a-1))
    apply ae_of_all
    intro U
    rw [←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (adj U) (norm_nonneg _)).trans_eq (by ring)
  rw [OriginalMarkedExteriorReweight.physical A hp hq hf good low]
  simp only [OriginalMarkedExteriorHaar.average,integral_complex_ofReal]
  change ‖(Z:ℂ)⁻¹*(∫ U,(P U:ℂ)*f U ∂μ)-(Z:ℂ)⁻¹*(∫ U,(D U:ℂ)*f U ∂μ)‖≤_
  rw [←mul_sub,←integral_sub pi di,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg zp.le]
  exact (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr zp.le)).trans_eq (by ring)

end YM.Integration.OriginalMarkedRelativeMoment

