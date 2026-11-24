import YM.Integration.WilsonLimitConstruction.FundedExtractionPolicy
import YM.Integration.ActualRunAdjacentCoupling
import YM.Integration.ActualNumericGeometrySmallness

/-! The native chart's preselected retention pays same-exponent reentry for
the original full input whenever its selected coefficient is covered by that
physical charge. Both fresh Taylor and calibration terms are included. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSameOrderPrice

open Filter Lattice Wilson RG Marker FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato Pert.Asymptotics

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}

/-- The coefficient actually multiplying the inherited bill in the canonical
source before extracting the requested norm. -/
def retained (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    (K : NumericPrices A) (m : ℕ) : ℝ :=
  K.vacuumConstant / ((R.family.S.block m).val:ℝ) + K.vanishing m

omit [Fintype V] [DecidableEq V] in
theorem nonnegative (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    (K : NumericPrices A) (m : ℕ) : 0 ≤ retained R K m :=
  add_nonneg (div_nonneg K.vacuum_constant_nonnegative (Nat.cast_nonneg _)) (K.vanishing_nonnegative m)

/-- A contraction of the weighted actual coefficient suffices on the full
original input domain, including inputs priced exactly at the requested order. -/
theorem admission (R : Run G) (hG : G.Simple) (J : Request V)
    (hc : 0 < J.inheritedConstant) (A : NumericSchedule R.family J) (K : NumericPrices A)
    (eta : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C:=R.family) J eta)
    (weighted : ∀ᶠ m : ℕ in atTop, ActualNextInheritedPrice.extractionFactor R A m *
      retained R K m ≤ 1/(2*(2:ℝ)^((J.order:ℝ)+1-J.eta))) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum R.family Γ, datum.level = m →
      ∀ (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta datum.cutoff datum.period datum.level)),
      ActualCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
        regulatorRun R.family datum.cutoff datum.period datum.level^((J.order:ℝ)+1-J.eta) := by
  let s : ℝ := (J.order:ℝ)+1-J.eta
  let T := (2:ℝ)^s
  let c := J.inheritedConstant
  let C := ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0)
  let D := ActualCanonicalPayloadPrice.degree (A.outputNorm 0)
  have hs : 0 ≤ s := by
    have ho : (2:ℝ) ≤ J.order := by exact_mod_cast J.order_ge_two
    dsimp only [s]; linarith only [ho, J.eta_lt_half]
  have hT : 0 < T := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := ActualCanonicalPayloadPrice.coefficient_positive G (A.outputNorm 0)
  have hsmall := ActualNumericGeometrySmallness.eventually_cost_geometry_coupling_small
    R hG A K (2*C*T) (by positivity) D (c/2) (half_pos hc) J.eta J.eta_pos
  obtain ⟨first,hcal⟩ := flat.2 (J.order+1)
  filter_upwards [weighted, hsmall, ActualRunAdjacentCoupling.eventually_ratio R hG,
    eventually_ge_atTop first] with m hweight hsmall hratio hm
  intro datum hlevel F I
  subst m
  let m := datum.level
  let gf := regulatorRun R.family datum.cutoff datum.period (m+1)
  let gc := regulatorRun R.family datum.cutoff datum.period m
  let B := ActualNextInheritedPrice.extractionFactor R A m
  let q := retained R K m
  let z := eta datum.cutoff datum.period m
  let P := C * A.admittedCost m^D
  have hf : 0 < gf := IterationFour.Currency.g_pos R.makes _ _ _ datum.below
  have hg : 0 < gc := IterationFour.Currency.g_pos R.makes _ _ _ datum.below.le
  have hP : 0 ≤ P := mul_nonneg hC.le (pow_nonneg (A.admitted_cost_nonnegative _) _)
  have hBP : B ≤ P := ActualCanonicalPayloadPrice.scheduled_factor R A m
  have hK := K.geometry_nonnegative m
  have power : gf^s ≤ T*gc^s := (Real.rpow_le_rpow hf.le
    ((div_le_iff₀ hg).mp (hratio datum.cutoff datum.period datum.below).2) hs).trans_eq
    (Real.mul_rpow (by norm_num) hg.le)
  have leading : B*q*I.inherited ≤ (c/2)*gc^s := by
    calc
      _ ≤ (1/(2*T))*I.inherited := mul_le_mul_of_nonneg_right hweight I.inherited_nonnegative
      _ ≤ (1/(2*T))*(c*(T*gc^s)) := mul_le_mul_of_nonneg_left
        (I.inherited_bound.trans (mul_le_mul_of_nonneg_left power hc.le)) (by positivity)
      _ = _ := by field_simp [hT.ne']
  have hz : 0 ≤ z := flat.1 _ _ _ datum.below F.physical_period
  have hzf : z ≤ gf^(J.order+1) := hcal _ _ _ hm datum.below F.physical_period
  have split : gf^(J.order+1) = gf^J.eta * gf^s := by
    rw [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one,
      show (J.order:ℝ)+1 = J.eta+s by dsimp only [s]; ring, Real.rpow_add hf]
  have fresh : B*(gf^(J.order+1)*K.geometry m+K.geometry m*z) ≤ (c/2)*gc^s := by
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
    _ ≤ (c/2)*gc^s+(c/2)*gc^s := add_le_add leading fresh
    _ = _ := by ring

/-- One physical chart can serve the entire heterogeneous request list.
Each particular granted family needs only the indicated comparison of its
own retained coefficient to the purchased source coefficient. -/
theorem of_native {U : ℕ → Type} (requests : (k : ℕ) → Request (U k))
    (R : Run G) (hG : G.Simple) (X : RG01Estimate.Chart.Demand G)
    (H : RG01Estimate.Chart.Stamped
      (FundedExtractionPolicy.demand X (FundedExtractionPolicy.profiles requests G)) R.kit)
    (k : ℕ) [Fintype (U k)] [DecidableEq (U k)] {book : Census (U k)}
    (hJ : 0 < (requests k).inheritedConstant)
    (A : NumericSchedule R.family (requests k)) (K : NumericPrices A)
    (eta : ℕ → ℕ → ℕ → ℝ)
    (flat : Retained.UniformlyFlat (C:=R.family) (requests k) eta)
    (native : ∀ᶠ m : ℕ in atTop,
      retained R K m ≤ max 0 (RG01Estimate.Routed.retention R.kit m)) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum R.family book, datum.level = m →
      ∀ (F : AnalyticInput (requests k) A datum)
        (I : FullPreparedInputAt F (eta datum.cutoff datum.period datum.level)),
      ActualCanonicalInputPayload.errorPrice R I K ≤ (requests k).inheritedConstant *
        regulatorRun R.family datum.cutoff datum.period datum.level^
          (((requests k).order:ℝ)+1-(requests k).eta) := by
  apply admission R hG (requests k) hJ A K eta flat
  filter_upwards [native, FundedExtractionPolicy.extracted requests R X H k A
    (1/(2*(2:ℝ)^(((requests k).order:ℝ)+1-(requests k).eta))) (by positivity)] with m hNative h
  exact h _ (nonnegative R K m) hNative

end YM.Integration.WilsonLimitConstruction.FundedSameOrderPrice
end
