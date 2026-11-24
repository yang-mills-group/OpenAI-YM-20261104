import YM.Integration.ActualOneMarkGraphRecurrence

/-! The Wilson factory column and its measured primary source use one
physical vacuum. Their difference has a complete zero-germ representation
with an explicit uniform inverse-coupling price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonGraphBoundary

open Filter Lattice Wilson RG Source Labels Extra.Histories Relay Bid
open Analysis Next.Foundations ProjectorNext.Equivariance Push.Local
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.Germ
open Trace.Physical.GermGraph Pert Pert.Asymptotics RG16 RG16.Guarding
open Literal OPE Work.G08
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) (d N p : ℕ)

/-- The primary source at the readout's actual threshold. -/
def primaryChart : Chart C p d := fun i v =>
  value d N p i (primary (0 : Site (C.side i p)) v)

private theorem primary_page (i : ℕ) (v : C.label d) :
    page d p i (primary (0 : Site (C.side i p)) v) = v := by
  let F := C.labels.level d
  let o : Site (C.side i p) := 0
  let q : store C d p i := primary o v
  change projection F C.params (plank C i).threshold o q = v
  have hz : label C.params o (0 : Config G (C.side i p) → ℂ) d = 0 := by
    have ht : JetTest C.params o (0 : Label G d) 0 :=
      (jetTest_zero_iff C.params o _ _).mpr (Extra.Histories.vanishing0 d _ C.params)
    have he : ∃ l : Label G d, JetTest C.params o l 0 := ⟨0, ht⟩
    rw [label, dif_pos he]
    exact JetTest.unique he.choose_spec ht
  have hv (j : ℕ) : vector F C.params (plank C i).threshold o (q.regular j) = 0 := by
    change F.scaled _ (F.coords (label C.params o 0 d)) = _
    rw [hz, map_zero, map_zero]
  simp only [projection, hv, tsum_zero, add_zero]
  rfl

/-- At the original ultraviolet cutoff the readout of the true calibrated
column is its original label. -/
theorem top_readout (H : C.Makes) (hr : C.ref d ≤ N) (v : C.label d) :
    measuring C d N p N v = v := by
  have h := H.calibrated d N p hr
  change page d p N ((C.factory d N p).entries N v) = v
  calc
    _ = page d p N (primary 0 v) := by
      unfold page projection
      rw [h.bare_coord, h.bare_germ]
      rfl
    _ = v := primary_page C d p N v

/-- A whole-column price bounds the difference from its measured primary,
retaining the original forced partners. -/
theorem measured_price (H : C.Makes) {i : ℕ} (ho : Opened C d i p) (hi : i≤N)
    {b : ℝ} (hb : ∀ w, reads d N p i ((C.factory d N p).entries i w)
      (b*mCost C d N p i w)) :
    Grown C N p d i b (primaryChart C d N p) := by
  intro w
  let x := measuring C d N p i w
  have he : Ink C N p d i (calValues (C := C) d N p i w) x
      (b*mCost C d N p i w) :=
    ⟨(C.factory d N p).entries i w, hb w, rfl, rfl⟩
  have hp' : Ink C N p d i (primaryChart C d N p i x) x 0 :=
    ⟨primary 0 x, ⟨primary_format _, primary_rem _ (Real.sqrt_pos.2 (Extra.Histories.forcedPos ..))⟩,
      primary_page C d p i x, rfl⟩
  have hp := hp'.scale (-1 : ℂ) H ho.post hi
  simpa only [neg_smul, one_smul, norm_neg, norm_one, mul_zero, add_zero,
    add_neg_cancel, sub_eq_add_neg] using he.combine hp H ho.post hi

/-- Every open upper cut has this complete primary comparison. -/
theorem measured (H : C.Makes) {i : ℕ} (ho : Opened C d i p) (hi : i≤N) :
    Grown C N p d i (2*stock C i) (primaryChart C d N p) :=
  measured_price C d N p H ho hi (fun w => graph_cost d N p i H ho hi w)

variable (R : Run G) (hG : G.Simple)
local notation "A" => R.family
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "L" => GermGraph.factor R.family
include hG

/-- The width price is uniform in cutoff and volume with just the purchased
one-log clock pace. The constant is explicit. -/
theorem stock_price (pace : ∀ i, ((R.family.S.block i).val : ℝ) ≤
    Real.log (R.family.path.levels.clock.hatBeta i)) :
    ∀ᶠ i : ℕ in atTop, ∀ N p : ℕ, i≤N →
    2*stock A i ≤ (2*Real.exp 1) * (regulatorRun A N p i)⁻¹ := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp (factor_large A 1 zero_lt_one)
  have hl := spend A hG (show (0 : ℝ)<1 by norm_num)
    ((blue A hG).pays (lambda_leads A hG))
  filter_upwards [eventually_ge_atTop (k+1), hl] with i hi hs N p hN
  have hL : 2*stock A i ≤ Λ i := by
    have hlt : 0 < i := by omega
    let j := i-1
    have hji : j+1=i := Nat.sub_add_cancel hlt
    have hj := hk j (by dsimp [j]; omega)
    rw [Real.rpow_one, hji] at hj
    have hu : 2*stock A i ≤ L j := by
      have hs : 1 ≤ stock A i := (stage A i).columns_ge
      linarith only [hj.2, hs]
    apply hu.trans
    apply le_trans _ ((lambda_mono A hG).monotone (show j ≤ i by dsimp [j]; omega))
    change ((R.family.S.block j).val : ℝ) ≤ 2 + Real.log (R.family.path.levels.clock.hatBeta j)
    linarith only [pace j]
  rw [coin_zero] at hs
  have hv := (g_band A R.makes (p := p) hN).2
  have hg : 0 < regulatorRun A N p i := g_pos R.makes hN
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hg).mpr
  calc
    2*stock A i*regulatorRun A N p i ≤ Λ i * (2*Real.exp 1*coin A 1 i) :=
      mul_le_mul hL hv hg.le (lambda_pos A i).le
    _ = (2*Real.exp 1)*(Λ i*coin A 1 i) := by ring
    _ ≤ _ := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*Real.exp 1 by positivity)

/-- The complete Wilson boundary for the primary source directly in
physical coupling units, simultaneously at every available upper cut. -/
theorem inverse_boundary (pace : ∀ i, ((R.family.S.block i).val : ℝ) ≤
    Real.log (R.family.path.levels.clock.hatBeta i)) :
    ∀ᶠ i : ℕ in atTop, ∀ N p : ℕ, i≤N →
    Grown A N p d i ((2*Real.exp 1)*(regulatorRun A N p i)⁻¹)
      (primaryChart A d N p) := by
  filter_upwards [open_late A hG d, stock_price R hG pace] with i ho hc N p hN w
  exact Ink.inc (measured A d N p R.makes (ho p) hN w)
    (mul_le_mul_of_nonneg_right (hc N p hN) (size_nonneg ..))

end YM.Integration.ActualWilsonGraphBoundary
