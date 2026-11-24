import YM.Integration.ActualNextInheritedPrice
import YM.Integration.ActualNumericGeometrySmallness
import YM.Integration.ActualRunAdjacentCoupling

/-! A surplus regulator order in the actual input pays the complete requested-
norm extraction at the next step. The target exponent and output coefficient
are prescribed before the common cutoff and period tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSurplusPrice

open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- Every positive-order surplus pays a fixed polynomial in the actual
admitted schedule, uniformly on the fine physical regulators. -/
theorem cost_small (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      C*A.admittedCost m^d * regulatorRun R.family N p (m+1)^a ≤ ε := by
  let n : ℝ := ((d+1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp only [n]; positivity
  let e := a/(2*n)
  have he : 0 < e := div_pos ha (mul_pos (by norm_num) hn)
  obtain ⟨first, hFirst⟩ := A.cost_subpower e he
  let v := (ε/(C+1))^(2/a)
  have hC1 : 0 < C+1 := by linarith only [hC]
  have hv0 : 0 < v := Real.rpow_pos_of_pos (div_pos hε hC1) _
  have hv : v^(a/2) = ε/(C+1) := by
    have hprod : (2/a)*(a/2) = (1 : ℝ) := by field_simp
    rw [show v = (ε/(C+1))^(2/a) from rfl, ← Real.rpow_mul (div_pos hε hC1).le,
      hprod, Real.rpow_one]
  have heq : -e*n = -(a/2) := by
    dsimp only [e]
    field_simp [hn.ne']
  filter_upwards [eventually_ge_atTop first, (tendsto_add_atTop_nat 1).eventually
    (Currency.g_small hG R.makes v hv0)] with m hm hFine
  intro N p hN
  let g := regulatorRun R.family N p (m+1)
  have hg : 0 < g := Currency.g_pos R.makes N p (m+1) hN
  have hx : A.admittedCost m^d ≤ g^(-(a/2)) := by
    calc
      _ ≤ A.admittedCost m^(d+1) := by
        rw [pow_succ]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (A.admitted_cost_ge_one m) (pow_nonneg (A.admitted_cost_nonnegative m) d)
      _ ≤ (g^(-e))^(d+1) := pow_le_pow_left₀ (A.admitted_cost_nonnegative m)
        (hFirst m hm N p hN) _
      _ = g^(-(a/2)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le, heq]
  have hhalf : g^(a/2) ≤ ε/(C+1) :=
    (Real.rpow_le_rpow hg.le (hFine N p hN).le (half_pos ha).le).trans_eq hv
  calc
    _ ≤ C*g^(-(a/2))*g^a := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx hC) (Real.rpow_nonneg hg.le _)
    _ = C*g^(a/2) := by rw [mul_assoc, ← Real.rpow_add hg]; congr 2; ring
    _ ≤ (C+1)*g^(a/2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hg.le _)
    _ ≤ (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hhalf hC1.le
    _ = ε := (mul_comm _ _).trans (div_mul_cancel₀ _ hC1.ne')

variable [Fintype V] [DecidableEq V] {Γ : Census V}

/-- The entire canonical vacuum error price, including the genuine
polynomial extraction, fits any smaller regulator order with an arbitrarily
chosen positive coarse coefficient. -/
theorem price (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A)
    (eta : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C:=R.family) J eta)
    (s δ M ε : ℝ) (hs : 0 ≤ s) (horder : s < (J.order : ℝ)+1)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum R.family Γ, datum.level = m →
      ∀ (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta datum.cutoff datum.period datum.level)),
      I.inherited ≤ M * regulatorRun R.family datum.cutoff datum.period
        (datum.level+1)^(s+δ) →
      ActualCanonicalInputPayload.errorPrice R I K ≤
        ε * regulatorRun R.family datum.cutoff datum.period datum.level^s := by
  let T := (2 : ℝ)^s
  let C := ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0)
  let D := ActualCanonicalPayloadPrice.degree (A.outputNorm 0)
  let U := K.vacuumConstant+1
  let a := (J.order : ℝ)+1-s
  have hT : 0 < T := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := ActualCanonicalPayloadPrice.coefficient_positive G (A.outputNorm 0)
  have hU : 0 ≤ U := add_nonneg K.vacuum_constant_nonnegative zero_le_one
  have ha : 0 < a := sub_pos.mpr horder
  obtain ⟨first,hCal⟩ := flat.2 (J.order+1)
  have hLead := cost_small R hG A (C*U*M*T) (by positivity) D δ (ε/2) hδ (half_pos hε)
  have hFresh := ActualNumericGeometrySmallness.eventually_cost_geometry_coupling_small
    R hG A K (2*C*T) (by positivity) D (ε/2) (half_pos hε) a ha
  filter_upwards [hLead, hFresh, ActualRunAdjacentCoupling.eventually_ratio R hG,
      K.vanishing_tendsto.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop first]
    with m hLead hFresh hRatio hvan hm
  intro datum hlevel F I hInput
  subst m
  let m := datum.level
  let gf := regulatorRun R.family datum.cutoff datum.period (m+1)
  let gc := regulatorRun R.family datum.cutoff datum.period m
  let B := ActualNextInheritedPrice.extractionFactor R A m
  let L := ((R.family.S.block m).val : ℝ)
  let q := K.vacuumConstant/L+K.vanishing m
  let P := C*A.admittedCost m^D
  let z := eta datum.cutoff datum.period m
  have hf : 0 < gf := Currency.g_pos R.makes _ _ _ datum.below
  have hc : 0 < gc := Currency.g_pos R.makes _ _ _ datum.below.le
  have hL : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr (R.family.S.block m).pos
  have hq : 0 ≤ q := add_nonneg
    (div_nonneg K.vacuum_constant_nonnegative (zero_le_one.trans hL)) (K.vanishing_nonnegative m)
  have hqU : q ≤ U := by
    refine add_le_add ((div_le_iff₀ (zero_lt_one.trans_le hL)).mpr ?_) hvan.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL K.vacuum_constant_nonnegative
  have hP : 0 ≤ P := mul_nonneg hC.le (pow_nonneg (A.admitted_cost_nonnegative m) _)
  have hBP : B ≤ P := ActualCanonicalPayloadPrice.scheduled_factor R A m
  have hA := A.admitted_cost_nonnegative m
  have hK := K.geometry_nonnegative m
  have hlong : gf^s ≤ T*gc^s :=
    (Real.rpow_le_rpow hf.le
      ((div_le_iff₀ hc).mp (hRatio datum.cutoff datum.period datum.below).2) hs).trans_eq
      (Real.mul_rpow (by norm_num) hc.le)
  have hInt : 0 ≤ I.inherited := I.inherited_nonnegative
  have hz : 0 ≤ z := flat.1 datum.cutoff datum.period m datum.below F.physical_period
  have hzf : z ≤ gf^(J.order+1) :=
    hCal datum.cutoff datum.period m hm datum.below F.physical_period
  have hTaylor : gf^(J.order+1) = gf^a * gf^s := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hf]
    congr 1
    dsimp only [a]
    push_cast
    ring
  have hp : B*q*I.inherited ≤ (ε/2)*gc^s := by
    calc
      _ ≤ P*U*(M*gf^(s+δ)) :=
        (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hBP hq).trans (mul_le_mul_of_nonneg_left hqU hP)) hInt).trans
          (mul_le_mul_of_nonneg_left hInput (mul_nonneg hP hU))
      _ = (C*U*M*A.admittedCost m^D*gf^δ)*gf^s := by
        rw [Real.rpow_add hf]; dsimp only [P]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlong (by positivity)
      _ = (C*U*M*T*A.admittedCost m^D*gf^δ)*gc^s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hLead datum.cutoff datum.period datum.below)
        (Real.rpow_nonneg hc.le _)
  have hn : B*(gf^(J.order+1)*K.geometry m + K.geometry m*z) ≤ (ε/2)*gc^s := by
    calc
      _ ≤ P*(gf^(J.order+1)*K.geometry m + K.geometry m*z) :=
        mul_le_mul_of_nonneg_right hBP
          (add_nonneg (mul_nonneg (pow_nonneg hf.le _) hK) (mul_nonneg hK hz))
      _ ≤ P*(gf^(J.order+1)*K.geometry m + K.geometry m*gf^(J.order+1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzf hK)) hP
      _ = (2*C*A.admittedCost m^D*K.geometry m*gf^a)*gf^s := by
        rw [hTaylor]; dsimp only [P]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlong (by positivity)
      _ = (2*C*T*A.admittedCost m^D*K.geometry m*gf^a)*gc^s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hFresh datum.cutoff datum.period datum.below)
        (Real.rpow_nonneg hc.le _)
  rw [ActualNextInheritedPrice.errorPrice_terms R (I:=I) (K:=K)]
  change B*q*I.inherited + B*gf^(J.order+1)*K.geometry m + B*K.geometry m*z ≤ ε*gc^s
  calc
    _ = B*q*I.inherited+B*(gf^(J.order+1)*K.geometry m+K.geometry m*z) := by ring
    _ ≤ (ε/2)*gc^s + (ε/2)*gc^s := add_le_add hp hn
    _ = _ := by ring

end YM.Integration.WilsonLimitConstruction.FundedSurplusPrice
end
