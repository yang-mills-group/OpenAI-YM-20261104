import YM.Integration.WilsonPhysicalHistoryKioskHeat
import YM.Integration.WilsonPositionSeparatedProfileReportingPrimary
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Repaid

/-! The physical cost of the mask on one actual signed, translated activity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Set Finset MeasureTheory Lattice Wilson RG OPE.Therm
open IterationFour PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonPositionSeparatedProfileReportingPrimary
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

private theorem face_card (X : Support n) :
    (cover X).card ≤ X.card*625*Fintype.card PlaqAxes := by
  rw [cover,card_product,card_univ]
  exact Nat.mul_le_mul_right _ (Corona.halo_size X 2)

private theorem measured_mask {μ : Measure (Config G n)} [IsFiniteMeasure μ]
    (X : Support n) (s : Signed) (x : Site n) (θ : ℝ) (f : Config G n→ℝ)
    (mf : Measurable f) {C : ℝ} (cap : ∀ U, ‖f U‖≤C) :
    let T:=cover (X.image (affine s x))
    ∫ U, ‖masked θ X f (pull s x U)-f (pull s x U)‖ ∂μ ≤
      C*μ.real (House.chilly (G:=G) T θ)ᶜ := by
  intro T
  let F (U : Config G n) := masked θ X f (pull s x U)-f (pull s x U)
  let E := (House.chilly (G:=G) T θ)ᶜ
  have hc : 0≤C := (norm_nonneg (f 1)).trans (cap 1)
  have mF : Measurable F := ((masked_measurable θ X f mf).sub mf).comp (continuous_pull s x).measurable
  have bF (U) : ‖F U‖≤C := by
    by_cases h : Healthy θ X (pull s x U)
    · simpa only [F,masked_eq _ _ _ _ h,sub_self,norm_zero] using hc
    · simpa only [F,masked_ne _ _ _ _ h,zero_sub,norm_neg] using cap (pull s x U)
  have onE (U) : U∉E → F U=0 := by
    intro h
    have rain : U∈House.chilly T θ := not_not.mp h
    have good := WilsonPositionSeparatedProfileReportingPrimary.healthy
      (X.image (affine s x)) (A:=T) (fun _ hx=>hx) le_rfl rain
    dsimp only [F]
    rw [masked_eq _ _ _ _ ((Turn.vigor s x U (X:=X) (Y:=X.image (affine s x)) θ rfl).mpr good),sub_self]
  have mE : MeasurableSet E := (House.bath T).compl
  have inside (U) : ‖F U‖ ≤ E.indicator (fun _=>C) U := by
    by_cases h : U∈E
    · simpa only [Set.indicator_of_mem h] using bF U
    · simp [h,onE U h]
  have fh : Integrable F μ := Integrable.of_bound mF.aestronglyMeasurable C (ae_of_all _ bF)
  apply (integral_mono fh.norm ((integrable_const C).indicator mE) inside).trans_eq
  rw [integral_indicator mE,setIntegral_const]
  simp [E,smul_eq_mul,mul_comm]

/-- Each submitted physical support pays for only its own incident plaquettes,
including its actual signed orientation. -/
theorem spring_mask_faces (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels)
    (q : ℕ) : ∀ᶠ j : ℕ in atTop, ∀N,j≤N→∀per (X : Support (R.family.side j per))
      (s : Signed) (x : Site (R.family.side j per)) (f : Config G (R.family.side j per)→ℝ)
      (C : ℝ),Measurable f→(∀U,‖f U‖≤C)→
      let θ:=(R.family.path.rep N per j).p.threshold
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j ^ q
      ∫ U,‖masked θ X f (pull s x U)-f (pull s x U)‖ ∂scene R.family.path N per j≤C*(X.card*fee) := by
  filter_upwards [PhysicalWilsonHotAllowance.faces heat simple R.makes.wilson (ρ:=1) zero_lt_one q]
    with j bill N date per X s x f C mf cap θ fee
  letI : IsProbabilityMeasure (scene R.family.path N per j) := probability R.makes.wilson date
  have cn : 0≤C := (norm_nonneg (f 1)).trans (cap 1)
  apply (measured_mask X s x θ f mf cap).trans
  apply mul_le_mul_of_nonneg_left _ cn
  let A:=cover (X.image (affine s x))
  have use := bill N date per A
  rw [one_mul] at use
  apply use.trans
  have count : (A.card:ℝ)≤(X.card:ℝ)*625*Fintype.card PlaqAxes := by
    exact_mod_cast ((face_card _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ card_image_le)))
  have kn : 0≤R.family.path.levels.clock.forcedAllowance j := (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_right count (pow_nonneg kn q)).trans_eq (by dsimp [fee];ring)

end YM.Integration.OriginalMarkedRunAction
