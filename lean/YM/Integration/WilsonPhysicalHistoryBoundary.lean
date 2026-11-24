import YM.Integration.WilsonPhysicalHistoryBirthClock
import YM.Integration.WilsonDyadicReportingPrice
import YM.Integration.WilsonWindowOriginalRun
import YM.Integration.ActualWilsonGraphBoundary
import YM.Integration.FineBoundaryTransfer

/-! The actual represented Wilson graph at the prescribed first UV cut, and
the price of its stable contribution after propagation to the measuring cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryBoundary

open Filter Real Lattice Wilson RG RG16 RG16.Literal Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops IterationFour.Currency
open RegulatorWindowRemainder Trace.Physical Trace.Physical.GermGraph WilsonLimitConstruction
open RG16.Guarding
open scoped Topology

variable {G : Gauge}

/-- At this specific first physical crossing the genuine scale distance is
    already enough for each fixed fine polynomial and general stable rate. -/
theorem margins (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c γ : ℝ} (hc : 1<c) (hγ : 0<γ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᶠ k : ℕ in atTop, let u := ultraviolet R.family c k
      k ≤ u ∧ t*G.slopeConstant ≤ γ*R.family.path.levels.clock.hatBeta k ∧
      (s+t)*log (R.family.path.levels.clock.hatBeta k) ≤ γ*(R.family.S.scale u-R.family.S.scale k) := by
  let C := R.family
  let L := Lambda C.path.levels
  have grow := ((tendsto_rpow_atTop (sub_pos.mpr hc)).comp (lambda_leads C hG)).eventually_ge_atTop ((s+t)/γ)
  filter_upwards [grow,(WardBin.bell C.path.levels hG).eventually_ge_atTop (t*G.slopeConstant/γ),
    ultraviolet_window C hG slow.2 c] with k hpow heat span
  have L0 : 0 < L k := lambda_pos C k
  have logL : log (C.path.levels.clock.hatBeta k) ≤ L k := by dsimp [L,Lambda]; linarith
  have exponent : (L k)^(c-1) * L k = (L k)^c := by
    calc
      _ = (L k)^(c-1)*(L k)^(1:ℝ) := by rw [rpow_one]
      _ = (L k)^((c-1)+1) := (rpow_add L0 _ _).symm
      _ = _ := by rw [sub_add_cancel]
  have spend : s+t ≤ (L k)^(c-1)*γ := (div_le_iff₀ hγ).mp hpow
  refine ⟨span.1.le,?_,?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hγ).mp heat
  calc
    _ ≤ (s+t)*L k := mul_le_mul_of_nonneg_left logL (add_nonneg hs ht)
    _ ≤ ((L k)^(c-1)*γ)*L k := mul_le_mul_of_nonneg_right spend L0.le
    _ = γ*(L k)^c := by rw [mul_comm ((L k)^(c-1)) γ,mul_assoc,exponent]
    _ ≤ _ := mul_le_mul_of_nonneg_left span.2.1 hγ.le

/-- The terminal stable debit is flat to every order in the actual coupling
    at the reporting level, uniformly in all physical cutoffs and periods. -/
theorem price (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c γ : ℝ} (hc : 1<c) (hγ : 0<γ) (p : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, let u := ultraviolet R.family c k
      u ≤ N → transfer R.family γ k u * ((2*exp 1) * (regulatorRun R.family N n u)⁻¹)
        ≤ ε*(regulatorRun R.family N n k)^p := by
  let C := R.family
  let A := 2*exp 1
  let F := (4:ℝ)^((1:ℝ)/2)
  let K := A*F*(2:ℝ)^(p+1)
  have A0 : 0≤A := by unfold A; positivity
  have F0 : 0≤F := by unfold F; positivity
  have K0 : 0≤K := mul_nonneg (mul_nonneg A0 F0) (by positivity)
  have cash := WilsonDyadicReportingPrice.reserve (C:=C) hG R.makes K 0 ε K0 hε
  filter_upwards [margins R hG slow hc hγ (s:=((p+1:ℕ):ℝ)) (t:=1) (by positivity) zero_le_one,cash] with k h money
  intro N n
  dsimp only
  intro live
  let u := ultraviolet C c k
  let g := regulatorRun C N n
  have kill := FineBoundaryTransfer.boundary_transfer (C:=C) (s:=((p+1:ℕ):ℝ)) (t:=1)
    (N:=N) (period:=n) R.makes zero_le_one h.1 live h.2.1 h.2.2
  have weight := (g_weight (C:=C) R.makes (q:=n) (h.1.trans live) ((p+1:ℕ):ℝ) (by positivity)).1
  simp only [rpow_natCast] at weight
  rw [rpow_neg_one] at kill
  have lower : 0≤g k := (g_pos R.makes (h.1.trans live)).le
  have funds : K*g k ≤ ε := by simpa only [rpow_zero,mul_one] using money n N (h.1.trans live)
  calc
    _ = A*(transfer C γ k u * (g u)⁻¹) := by ring
    _ ≤ A*(F*IterationFour.Currency.weight C.path.levels ((p+1:ℕ):ℝ) k) := mul_le_mul_of_nonneg_left kill A0
    _ ≤ A*(F*((2:ℝ)^(p+1)*(g k)^(p+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left weight F0) A0
    _ = (K*g k)*(g k)^p := by unfold K; rw [pow_succ (g k)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right funds (pow_nonneg lower _)

/-- Whole stable representative for the original Wilson primary column at
    the UV endpoint; one amount pays it and becomes flat after transport. -/
theorem represented {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (hG : G.Simple) {penalty : ℝ} (original : FundedOriginalProperties hG penalty W)
    (slow : WilsonWindowReportingPace.Slow R.kit) {c γ : ℝ} (hc : 1<c) (hγ : 0<γ)
    (d p : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, let u := ultraviolet R.family c k
      u ≤ N → ∃ a : ℝ, 0≤a ∧ Grown R.family N n d u a (ActualWilsonGraphBoundary.primaryChart R.family d N n) ∧
        transfer R.family γ k u * a ≤ ε*(regulatorRun R.family N n k)^p := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp
    (ActualWilsonGraphBoundary.inverse_boundary (d:=d) R hG original.2.1.paid.paced.grade)
  filter_upwards [price R hG slow hc hγ p hε,ultraviolet_window R.family hG slow.2 c,
    eventually_ge_atTop b] with k paid span bk
  intro N n
  dsimp only
  intro live
  let u := ultraviolet R.family c k
  have positive : 0 < regulatorRun R.family N n u := g_pos R.makes live
  exact ⟨(2*exp 1)*(regulatorRun R.family N n u)⁻¹,by positivity,
    hb u (bk.trans span.1.le) N n live,paid N n live⟩

end YM.Integration.WilsonPhysicalHistoryBoundary

