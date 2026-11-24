import YM.Integration.WilsonLimitConstruction.FundedChartDemand
import YM.Integration.ActualNextInheritedPrice
import YM.Integration.FullQLocalRawInheritedRate

/-! One native pre-length chart purchase pays every prescribed requested-norm
extraction against the physical retained coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedExtractionPolicy

open Filter Lattice RG RG01Estimate RG01Estimate.Chart FullQLocal FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato
open scoped BigOperators Topology

variable {G : Gauge}

def prefixCost (rows : ℕ → Stage → ℝ) (s : Stage) (j : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (j+1), |rows k s|

theorem prefixCost_pos (rows : ℕ → Stage → ℝ) (s : Stage) (j : ℕ) :
    0 < prefixCost rows s j := by
  unfold prefixCost
  positivity

theorem row_le (rows : ℕ → Stage → ℝ) (s : Stage) {k j : ℕ} (hk : k ≤ j) :
    |rows k s| ≤ prefixCost rows s j := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (j+1)) => abs_nonneg (rows i s))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  unfold prefixCost
  linarith only [h]

/-- The original shipping request is retained verbatim. At stage j only the
first j+1 prescribed extraction costs enter the pre-length retention target. -/
def demand (X : Demand G) (rows : ℕ → Stage → ℝ) : Demand G where
  wish := X.wish
  retention s z j i := min (X.retention s z j i)
    (((j:ℝ)+1) * prefixCost rows (s i) j)⁻¹
  available s z j i := lt_min (X.available s z j i)
    (inv_pos.mpr (mul_pos (Nat.cast_add_one_pos _) (prefixCost_pos ..)))

theorem original (R : Run G) {X : Demand G} {rows : ℕ → Stage → ℝ}
    (H : Stamped (demand X rows) R.kit) : Stamped X R.kit where
  allowed := H.allowed
  earned m := (H.earned m).trans (min_le_left _ _)
  shipping := H.shipping

/-- The native source's actual retention, multiplied by any prescribed row,
has an explicit decreasing bound on the very same factor. -/
theorem weighted (R : Run G) {X : Demand G} {rows : ℕ → Stage → ℝ}
    (H : Stamped (demand X rows) R.kit) (k m : ℕ)
    (hk : k ≤ R.family.path.levels.clock.J (m+1)) :
    |rows k (R.family.path.levels.params m)| * max 0 (Routed.retention R.kit m) ≤
      ((R.family.path.levels.clock.J (m+1):ℝ)+1)⁻¹ := by
  let j := R.family.path.levels.clock.J (m+1)
  let i := R.family.path.levels.clock.J m
  let s := R.metals.p.profile i
  let d := prefixCost rows s j
  let u := (j:ℝ)+1
  have hd : 0 < d := prefixCost_pos ..
  have hu : 0 < u := Nat.cast_add_one_pos _
  have hstage : R.family.path.levels.params m = s := Push.PriceCompiler.params_eq R.alloy.B.valid m
  have hfee : max 0 (Routed.retention R.kit m) ≤ (u*d)⁻¹ :=
    max_le (inv_nonneg.mpr (mul_pos hu hd).le) ((H.earned m).trans (min_le_right _ _))
  rw [hstage]
  calc
    _ ≤ d * max 0 (Routed.retention R.kit m) := mul_le_mul_of_nonneg_right
      (row_le rows s hk) (le_max_left _ _)
    _ ≤ d * (u*d)⁻¹ := mul_le_mul_of_nonneg_left hfee hd.le
    _ = u⁻¹ := by field_simp

variable {V : ℕ → Type} (J : (k : ℕ) → Request (V k))

def profiles (G : Gauge) : ℕ → Stage → ℝ := fun k => RawInherited.profileCost G (J k)

/-- The schedule is arbitrary after this one chart has been selected. Each
physical coefficient bounded by its native retention pays the exact extraction
factor to any prescribed positive tolerance on the original calendar. -/
theorem extracted (R : Run G) (X : Demand G)
    (H : Stamped (demand X (profiles J G)) R.kit) (k : ℕ)
    (A : NumericSchedule R.family (J k)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ max 0 (Routed.retention R.kit m) →
      ActualNextInheritedPrice.extractionFactor R A m * q ≤ ε := by
  let floor := Nat.ceil ε⁻¹
  filter_upwards [(R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop
    (max k floor)] with m hm
  intro q hq hq'
  let j := R.family.path.levels.clock.J (m+1)
  have hk : k ≤ j := (le_max_left _ _).trans hm
  have hf : ε⁻¹ ≤ (j:ℝ)+1 := by
    have hcast : (floor:ℝ) ≤ j := by exact_mod_cast (le_max_right _ _).trans hm
    exact (Nat.le_ceil _).trans (by linarith only [hcast])
  have cheap : ((j:ℝ)+1)⁻¹ ≤ ε := by
    rw [← one_div]
    apply (div_le_iff₀ (Nat.cast_add_one_pos _)).mpr
    exact (mul_inv_cancel₀ hε.ne').symm.trans_le (mul_le_mul_of_nonneg_left hf hε.le)
  have hP := RawInherited.profileCost_pos G (J k) (R.family.path.levels.params m)
  calc
    _ ≤ RawInherited.profileCost G (J k) (R.family.path.levels.params m) * q :=
      mul_le_mul_of_nonneg_right (RawInherited.extraction_le A m) hq
    _ ≤ |profiles J G k (R.family.path.levels.params m)| * max 0 (Routed.retention R.kit m) := by
      rw [profiles, abs_of_pos hP]
      exact mul_le_mul_of_nonneg_left hq' hP.le
    _ ≤ _ := (weighted R H k m hk).trans cheap

end YM.Integration.WilsonLimitConstruction.FundedExtractionPolicy
end
