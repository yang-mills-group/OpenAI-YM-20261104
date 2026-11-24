import YM.Integration.ActualOneMarkGraphStep
import YM.RG16.GaugeCredit.Curve

/-! On the purchased Wilson clock the represented singleton graph and its
actual transfer matrix keep a fixed coupling exponent throughout descent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualOneMarkGraphRecurrence

open Function Filter Lattice Wilson RG Source Labels Extra.Histories Relay Bid
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open OPE Pert Pert.Asymptotics RG16 RG16.Guarding Literal Work.G08
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) (hG : G.Simple) (d : ℕ)
local notation "A" => R.family
local notation "L" => GermGraph.factor A
local notation "Λ" => RG16.Lambda (A).path.levels
local notation "σ" => ((A).labels.level d).coeffSize
local notation "μ" => coin A

include hG

/-- The actual funded clock has subexponential block length on the
log-coupling scale. This uses precisely the bound held by `Flick.grade`. -/
theorem block_subpower (pace : ∀ i, (((A).S.block i).val : ℝ) ≤
    Real.log ((A).path.levels.clock.hatBeta i)) : RateIs atTop Λ L 0 :=
  RateIs.of_sandwich (f := fun _ : ℕ => 1)
    (RateIs.const (lambda_leads A hG) zero_lt_one)
    ((blue A hG).pays (lambda_leads A hG))
    (Eventually.of_forall fun i => (factor_positive A i).le)
    (Eventually.of_forall fun i => by
      change (((A).S.block i).val : ℝ) ≤ 2 + Real.log ((A).path.levels.clock.hatBeta i)
      linarith only [pace i]) (lambda_leads A hG)

private theorem prices (pace : RateIs atTop Λ L 0) {x y γ : ℝ}
    (hx : 0<x) (hxy : x<y) (hγ : 0<γ) (hr : γ<rate) :
    ∀ᶠ t : ℕ in atTop, ∀ i≥t, ∀ p N : ℕ, i<N →
      ((Opened A d i p ∧ Opened A d (i+1) p) ∧ Gate A d N p i γ 1) ∧
      2*L i^γ*(μ y i + L i^(-rate)*μ x (i+1)) ≤ min (μ x i) 1 := by
  have hp : RateLE atTop Λ (fun i => 4*(L i^γ)) 0 := by
    simpa only [zero_add, mul_zero] using!
      (RateLE.const 4 (lambda_leads A hG)).mul ((pace.rpow γ).pays (lambda_leads A hG))
  obtain ⟨n, hn⟩ := eventually_atTop.mp ((quarter A hr).and (spend A hG hxy hp))
  filter_upwards [ActualOneMarkGraphStep.gates R hG d hγ zero_lt_one,
    eventually_ge_atTop n] with t ht hnt i hi p N hN
  refine ⟨ht i hi p N hN, ?_⟩
  rw [min_eq_left (smaller_receipt A hx.le i)]
  have hD := coin_down A hG hx.le (Nat.le_succ i)
  have ⟨hcon, hpay⟩ := hn i (hnt.trans hi)
  have hprod := mul_le_mul hcon hD (coin_pos A x (i+1)).le (by norm_num)
  linarith only [hprod, hpay, coin_pos A x i]

private theorem descend (pace : RateIs atTop Λ L 0) {x y : ℝ}
    (hx : 0<x) (hxy : x<y) : ∀ᶠ t : ℕ in atTop, ∀ N p : ℕ, t≤N →
    ∀ (M : ℕ → Mat A d) (Y : Chart A p d),
    Grown A N p d N (μ y N) Y →
    (∀ i≥t, i<N → Inked A N p d i Y (M i) (μ y i)) →
    (∀ i≥t, i≤N → Grown A N p d i (μ x i) Y) ∧
    (∀ i≥t, i<N → ∀ w : (A).label d,
      σ (measuring A d N p i w - M i (measuring A d N p (i+1) w)) ≤
        μ x i*mCost A d N p (i+1) w) := by
  have hr : 0 < rate := by unfold rate; norm_num
  filter_upwards [prices R hG d pace hx hxy (half_pos hr) (half_lt_self hr)] with t ht N p _ M Y htop hloc
  have hg (i : ℕ) (h : t ≤ i) (hi : i≤N) : Grown A N p d i (μ x i) Y := by
    induction hi using Nat.decreasingInduction with
    | self =>
      exact fun w => Ink.inc (htop w)
        (mul_le_mul_of_nonneg_right (coin_weaken A hxy.le _) (size_nonneg ..))
    | of_succ j hj ih =>
      have step := ht j h p N hj
      exact grow_step A R.makes N p d (coin_pos A x (j+1)).le
        (coin_pos A y j).le hj step.1.1.1 step.1.1.2 step.1.2
        (ih (h.trans j.le_succ)) (hloc j h hj) step.2
  refine ⟨hg, fun i hi hN w => ?_⟩
  have step := ht i hi p N hN
  have hb := (held A R.makes N p d hN step.1.1.1 step.1.1.2 step.1.2
    (hg (i+1) (hi.trans i.le_succ) hN) (hloc i hi hN) w).choose_spec.2.2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (size_nonneg ..)
  have hl := factor_positive A i
  have hinv : 1 ≤ 2*L i^(rate/2) := one_le_mul_of_one_le_of_one_le
    (by norm_num) (Real.one_le_rpow hl.le (half_pos hr).le)
  have hn := add_nonneg (coin_pos A y i).le
    (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hl).le (-rate)) (coin_pos A x (i+1)).le)
  exact (le_mul_of_one_le_left hn hinv).trans (step.2.trans (min_le_left ..))

/-- Full cutoff-uniform descent in the physical regulator coupling.
The boundary and local signed defects are priced at their original fine
scale. The output retains a complete germ-null representative for each
calibration vector and controls the transfer of that same vector. -/
theorem coupling_descent (pace : ∀ i, (((A).S.block i).val : ℝ) ≤
    Real.log ((A).path.levels.clock.hatBeta i)) {s t : ℝ} (ht : 0<t) (hst : t<s)
    (boundary localCost : ℝ) : ∀ᶠ k : ℕ in atTop, ∀ N p : ℕ, k≤N →
    ∀ (M : ℕ → Mat A d) (Y : Chart A p d),
    Grown A N p d N (boundary * (regulatorRun A N p N)^s) Y →
    (∀ i≥k, i<N → Inked A N p d i Y (M i) (localCost * (regulatorRun A N p (i+1))^s)) →
    (∀ i≥k, i≤N → Grown A N p d i ((regulatorRun A N p i)^t) Y) ∧
    (∀ i≥k, i<N → ∀ w : (A).label d,
      σ (measuring A d N p i w - M i (measuring A d N p (i+1) w)) ≤
        (regulatorRun A N p i)^t * mCost A d N p (i+1) w) := by
  let x := (2*t+s)/3
  let y := (t+2*s)/3
  have htx : t<x := by dsimp [x]; linarith
  have hxy : x<y := by dsimp [x,y]; linarith
  have hys : y<s := by dsimp [y]; linarith
  have hbase := convert_in A R.makes hG (RateLE.const boundary (lambda_leads A hG)) hys (ht.trans hst).le
  have hstep := convert_in A R.makes hG (RateLE.const localCost (lambda_leads A hG)) hys (ht.trans hst).le
  have hout := convert_out A R.makes hG ((coin_exact A hG x).pays (lambda_leads A hG)) htx ht.le
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hbase.and (hstep.and hout))
  filter_upwards [descend R hG d (block_subpower R hG pace) (ht.trans htx) hxy,
    eventually_ge_atTop n] with k hk nk N p kN M Y htop hloc
  have hin : Grown A N p d N (μ y N) Y := fun w => Ink.inc (htop w)
    (mul_le_mul_of_nonneg_right ((hn N (nk.trans kN)).1 p N le_rfl) (size_nonneg ..))
  have hloc' (i : ℕ) (hi : k ≤ i) (hN : i<N) : Inked A N p d i Y (M i) (μ y i) := by
    have h := hloc i hi hN
    have he := ((hn (i+1) ((nk.trans hi).trans i.le_succ)).2.1 p N hN).trans
      (coin_down A hG ((ht.trans htx).trans hxy).le i.le_succ)
    refine ⟨h.1, fun w => ?_⟩
    obtain ⟨a,q,ha,hq,hsize,hval,hw⟩ := h.2 w
    exact ⟨a,q,ha,hq,hsize,hval,hw.trans (mul_le_mul_of_nonneg_right he (size_nonneg ..))⟩
  obtain ⟨g,m⟩ := hk N p kN M Y hin hloc'
  refine ⟨fun i hi hN w => Ink.inc (g i hi hN w) ?_, fun i hi hN w => (m i hi hN w).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right ((hn i (nk.trans hi)).2.2 p N hN) (size_nonneg ..)
  · exact mul_le_mul_of_nonneg_right ((hn i (nk.trans hi)).2.2 p N hN.le) (size_nonneg ..)

end YM.Integration.ActualOneMarkGraphRecurrence
