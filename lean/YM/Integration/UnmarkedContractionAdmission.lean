import YM.Integration.WilsonLimitConstruction.FundedSameOrderPrice
import YM.Integration.ActualRunCouplingChart
import YM.Integration.ActualRunBetaResetSmall
import YM.Integration.UnmarkedReclosureFamily

/-! A strict contraction of the extracted inherited coefficient suffices
for the original uniform same-order admission, with any fixed margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UnmarkedContractionAdmission

open Filter Lattice Wilson RG Marker FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato Pert.Asymptotics MatchingLedger.Compass.Income
open WilsonLimitConstruction
open scoped Topology

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}

/-- At every fixed real power the actual adjacent regulators have
arbitrarily small relative loss, before the cutoff and physical torus. -/
theorem adjacent (R : Run G) (hG : G.Simple) (s : ℝ) {T : ℝ} (hT : 1 < T) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m < N →
      regulatorRun R.family N per (m+1)^s ≤ T*regulatorRun R.family N per m^s := by
  let f (t : ℝ) := ((Real.sqrt (1-t))⁻¹)^s
  have hc : ContinuousAt f 0 := by unfold f; fun_prop (disch := norm_num)
  have he : f 0 < T := by simpa [f] using hT
  obtain ⟨δ, hδ, near⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (eventually_lt_nhds he))
  filter_upwards [ActualRunBetaResetSmall.eventually_small R hG (half_pos hδ)] with m hm
  intro N per hN
  let gf := regulatorRun R.family N per (m+1)
  let gc := regulatorRun R.family N per m
  have hf : 0 < gf := Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) per
  have hg : 0 < gc := Weather.runs_pos R.family R.makes hN.le per
  let t := (R.family.path.β N per m - R.family.path.β N per (m+1))*gc^2
  have ht : |t| < δ := (hm N per hN).trans_lt (half_lt_self hδ)
  have hratio : (gf/gc)^s ≤ T := by
    change (regulatorRun R.family N per (m+1)/gc)^s ≤ T
    rw [← ActualRunCouplingChart.unit_coarse R N per m hN]
    have hnear : f t < T := near (by simpa only [Real.dist_eq, sub_zero] using ht)
    exact hnear.le
  calc
    gf^s = ((gf/gc)*gc)^s := by rw [div_mul_cancel₀ _ hg.ne']
    _ = (gf/gc)^s*gc^s := Real.mul_rpow (div_nonneg hf.le hg.le) hg.le
    _ ≤ T*gc^s := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hg.le _)

/-- Any actual fixed contraction coefficient below one is sufficient at
the exact inherited exponent. The same numeric grant, irregular incoming
state, canonical error price and separate calibration are retained. -/
theorem admission (R : Run G) (hG : G.Simple) (J : Request V)
    (hc : 0 < J.inheritedConstant) (A : NumericSchedule R.family J) (K : NumericPrices A)
    (η : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := R.family) J η)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (weighted : ∀ᶠ m : ℕ in atTop, ActualNextInheritedPrice.extractionFactor R A m *
      FundedSameOrderPrice.retained R K m ≤ θ) :
    UnmarkedReclosureFamily.Inherited R K (Γ := Γ) (η := η) := by
  let s : ℝ := (J.order:ℝ)+1-J.eta
  let T : ℝ := 2-θ
  let c := J.inheritedConstant
  let C := ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0)
  let D := ActualCanonicalPayloadPrice.degree (A.outputNorm 0)
  have hT : 1 < T := by dsimp only [T]; linarith only [hθ1]
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hgap : 0 < 1-θ*T := by
    rw [show 1-θ*T=(1-θ)^2 by dsimp only [T]; ring]
    exact sq_pos_of_pos (sub_pos.mpr hθ1)
  have hC : 0 < C := ActualCanonicalPayloadPrice.coefficient_positive G (A.outputNorm 0)
  have hsmall := ActualNumericGeometrySmallness.eventually_cost_geometry_coupling_small
    R hG A K (2*C*T) (by positivity) D ((1-θ*T)*c) (mul_pos hgap hc) J.eta J.eta_pos
  obtain ⟨first,hcal⟩ := flat.2 (J.order+1)
  filter_upwards [weighted, hsmall, adjacent R hG s hT, eventually_ge_atTop first] with m hweight hsmall hpower hm
  intro datum hlevel F I
  subst m
  let m := datum.level
  let gf := regulatorRun R.family datum.cutoff datum.period (m+1)
  let gc := regulatorRun R.family datum.cutoff datum.period m
  let B := ActualNextInheritedPrice.extractionFactor R A m
  let q := FundedSameOrderPrice.retained R K m
  let z := η datum.cutoff datum.period m
  let P := C * A.admittedCost m^D
  have hf : 0 < gf := IterationFour.Currency.g_pos R.makes _ _ _ datum.below
  have hg : 0 < gc := IterationFour.Currency.g_pos R.makes _ _ _ datum.below.le
  have hP : 0 ≤ P := mul_nonneg hC.le (pow_nonneg (A.admitted_cost_nonnegative _) _)
  have hBP : B ≤ P := ActualCanonicalPayloadPrice.scheduled_factor R A m
  have hK := K.geometry_nonnegative m
  have power : gf^s ≤ T*gc^s := hpower datum.cutoff datum.period datum.below
  have leading : B*q*I.inherited ≤ (θ*T*c)*gc^s := by
    calc
      _ ≤ θ*I.inherited := mul_le_mul_of_nonneg_right hweight I.inherited_nonnegative
      _ ≤ θ*(c*(T*gc^s)) := mul_le_mul_of_nonneg_left
        (I.inherited_bound.trans (mul_le_mul_of_nonneg_left power hc.le)) hθ
      _ = _ := by ring
  have hz : 0 ≤ z := flat.1 _ _ _ datum.below F.physical_period
  have hzf : z ≤ gf^(J.order+1) := hcal _ _ _ hm datum.below F.physical_period
  have split : gf^(J.order+1) = gf^J.eta * gf^s := by
    rw [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one,
      show (J.order:ℝ)+1 = J.eta+s by dsimp only [s]; ring, Real.rpow_add hf]
  have fresh : B*(gf^(J.order+1)*K.geometry m+K.geometry m*z) ≤ ((1-θ*T)*c)*gc^s := by
    calc
      _ ≤ P*(gf^(J.order+1)*K.geometry m+K.geometry m*z) := mul_le_mul_of_nonneg_right hBP
        (add_nonneg (mul_nonneg (pow_nonneg hf.le _) hK) (mul_nonneg hK hz))
      _ ≤ P*(gf^(J.order+1)*K.geometry m+K.geometry m*gf^(J.order+1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzf hK)) hP
      _ = (2*C*A.admittedCost m^D*K.geometry m*gf^J.eta)*gf^s := by
        rw [split]; dsimp only [P]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left power (by
        have := A.admitted_cost_nonnegative m
        positivity)
      _ = (2*C*T*A.admittedCost m^D*K.geometry m*gf^J.eta)*gc^s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hsmall datum.cutoff datum.period datum.below)
        (Real.rpow_nonneg hg.le _)
  rw [ActualNextInheritedPrice.errorPrice_terms R (I:=I) (K:=K)]
  change B*q*I.inherited+B*gf^(J.order+1)*K.geometry m+B*K.geometry m*z ≤ c*gc^s
  calc
    _ = B*q*I.inherited+B*(gf^(J.order+1)*K.geometry m+K.geometry m*z) := by ring
    _ ≤ (θ*T*c)*gc^s+((1-θ*T)*c)*gc^s := add_le_add leading fresh
    _ = _ := by ring

end YM.Integration.UnmarkedContractionAdmission
