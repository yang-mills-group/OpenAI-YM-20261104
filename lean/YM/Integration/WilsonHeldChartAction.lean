import YM.Integration.WilsonHeldExteriorLaw

/-! Signed mixed variation of the inherited log action under the actual
fixed-exterior Wilson law at an arbitrary held coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldChartAction
open Function Set MeasureTheory Lattice RG Wilson
open PhysicalNext.Repeat.Legato WilsonHeldExteriorLaw
open scoped Classical
variable {G : Gauge}

def assembled (R : Run G) (per j : ℕ)
    (frozen : Set (Edge (Site (R.family.side (j+1) per)))) (outside : Fields G frozen)
    (z : Fields G frozenᶜ) : Config G (R.family.side (j+1) per) := (cut G frozen).symm (outside,z)

def weight (R : Run G) (N per j : ℕ)
    (frozen : Set (Edge (Site (R.family.side (j+1) per)))) (outside : Fields G frozen)
    (V : Config G (R.family.side j per)) (z : Fields G frozenᶜ) : ℝ :=
  WilsonHeldExteriorLaw.weight R N per j V (R.family.path.rep N per (j+1))
    (assembled R per j frozen outside z)

def law (R : Run G) (N per j : ℕ)
    (frozen : Set (Edge (Site (R.family.side (j+1) per)))) (outside : Fields G frozen)
    (E : Set (Fields G frozenᶜ)) (V : Config G (R.family.side j per)) : Measure (Fields G frozenᶜ) :=
  let base := (sheet G frozenᶜ).restrict E
  let w := weight R N per j frozen outside V
  base.withDensity (fun z => ENNReal.ofReal (w z/(∫ u,w u ∂base)))

variable (R : Run G) (N per j : ℕ)
local notation "n" => R.family.side (j+1) per
local notation "Q" => R.family.path.rep N per (j+1)
variable (frozen : Set (Edge (Site (R.family.side (j+1) per)))) (outside : Fields G frozen)
variable (E : Set (Fields G frozenᶜ)) (V : Config G (R.family.side j per))
local notation "Ω" => Fields G frozenᶜ
local notation "μ" => Measure.restrict (sheet G frozenᶜ) E

private theorem normed {X : Type*} [MeasurableSpace X] (m : Measure X) {w : X → ℝ}
    (e : Integrable w m) (h : ∀ z,0 ≤ w z)
    (mass : 0 < ∫z,w z ∂m) :
    IsProbabilityMeasure (m.withDensity (fun z=>ENNReal.ofReal (w z/(∫u,w u ∂m)))) where
  measure_univ := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal (e.div_const _)
        (ae_of_all m fun z=>div_nonneg (h z) mass.le),integral_div,div_self mass.ne',ENNReal.ofReal_one]

theorem probability (hi : j+1 ≤ N) (positive : 0 < (sheet G frozenᶜ) E) :
    IsProbabilityMeasure (law R N per j frozen outside E V) := by
  let w := weight R N per j frozen outside V
  obtain ⟨a,ha,wa⟩ := upper_floor R N per j hi
  obtain ⟨ew,t,ht,lt⟩ := regularity R N per j hi V Q
    ((Q).envelope (R.makes.wilson.represents N per (j+1) hi).good) ha wa
  have assembled_meas : Measurable (assembled R per j frozen outside) :=
    (cut G frozen).symm.measurable.comp (measurable_const.prodMk measurable_id)
  have e : Envelope w :=
    ⟨ew.meas.comp assembled_meas,ew.cost.imp fun _ cap z => cap (assembled R per j frozen outside z)⟩
  have pos (z : Ω) : 0 < w z := ht.trans_le (lt _)
  have mass : 0 < ∫z,w z ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun z=>(pos z).le) (e.integrable μ)).mpr
    rw [show Function.support w = univ from eq_univ_of_forall fun z=>(pos z).ne',Measure.restrict_apply_univ]
    exact positive
  exact normed μ (e.integrable μ) (fun z=>(pos z).le) mass

/-- The original and rendered actions each subtract their own fixed exterior
reference. The remaining factor is centered on the true held probability. -/
theorem mixed (Y : Ω → ℝ) (y₀ : ℝ) (U₀ : Config G n) (H : Config G n → ℂ) {δ : ℝ}
    (price : ∀ᵐ z ∂μ,
      |(Real.log ((Q).eval (assembled R per j frozen outside z))-Real.log ((Q).eval U₀)) -
       (Y z-y₀)| ≤ δ)
    (hi : j+1 ≤ N) (positive : 0 < (sheet G frozenᶜ) E) :
    let ν := law R N per j frozen outside E V
    let U := assembled R per j frozen outside
    let B := H ∘ U
    let centered := fun z => B z - ∫ w,B w ∂ν
    let error := fun z => (Real.log ((Q).eval (U z))-Real.log ((Q).eval U₀))-(Y z-y₀)
    Integrable B ν →
    ‖∫ z,error z • centered z ∂ν‖ ≤ δ * ∫ z, ‖centered z‖ ∂ν := by
  intro ν U B centered error hB
  letI : IsProbabilityMeasure ν := probability R N per j frozen outside E V hi positive
  have hC : Integrable centered ν := hB.sub (integrable_const _)
  have law_ac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have ep : ∀ᵐ z ∂ν, |error z| ≤ δ := law_ac.ae_le price
  have bound : ∀ᵐ z ∂ν, ‖error z • centered z‖ ≤ δ * ‖centered z‖ :=
    ep.mono fun z hz=>by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  exact (norm_integral_le_of_norm_le (hC.norm.const_mul δ) bound).trans_eq (integral_const_mul ..)

end YM.Integration.WilsonHeldChartAction
end
