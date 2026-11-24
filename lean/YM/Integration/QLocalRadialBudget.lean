import YM.Integration.QLocalRadialPublication
import YM.Integration.LocalComparisonInterface

/-! Publication of native marked bands and their actual supplied captions.
The radial regular and forced invoices give separate manuscript totals at the
original physical budget point. Each independent test shares the same mode
and support indices. Only the regular derivative bill pays the factorial sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRadialBudget
open Function Lattice Wilson RG Marker Overlay FVA1 RG3.Held RG3.Script.Picnic
open Extra.Multi Push.AbsoluteSums LocalComparison QLocalRadialPublication ComparisonDensity.Address
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {P : Rep G n} {V X : Type} [DecidableEq V] [Fintype V]

def view (a : Bands (Stock.census V) P) (γ : X → V → ℂ) : View X V G n P (Stock.census V) where
  origins := a.origins
  rays := a.rays
  branch := a.support
  marks := a.marks
  global x := (bands a (γ x)).units
  regular x := (bands a (γ x)).H
  force x := (bands a (γ x)).entries

def taste (a : Bands (Stock.census V) P) (γ : X → V → ℂ)
    (tag : ℕ → (Stock.census V).Mode) (site : ℕ → Support n) (score : X → ℕ → ℂ) :
    Taste X a.origins P (Stock.census V) := ⟨view a γ, rfl, tag, site, score⟩

variable (a : Bands (Stock.census V) P) (ha : a.Active) {u w M : V → ℝ}
    (hw : ∀ i, 0 < w i) (hM : ∀ i, 0 ≤ M i) (cap : ∀ i, w i * M i ≤ u i)
    {U C D b : ℝ} (hr : a.Radial u U C D b) (γ : X → V → ℂ) (hγ : ∀ x i, ‖γ x i‖ ≤ M i)

include ha hw hM cap hr hγ

theorem passport : Nonempty ((view a γ).Passport w U C D b) := by
  obtain ⟨t, h, g, ht, hc, hh, hf, hu⟩ := common a hw hM cap hr γ hγ
  exact ⟨⟨t, h, fun x => active a ha (γ x), hw, hr.factor,
    fun x v => (mul_le_mul_of_nonneg_left ((hu v).2.1 x) (hw v).le).trans (hu v).2.2,
    ht, hc, hh, hf⟩⟩

theorem budget (tag : ℕ → (Stock.census V).Mode) (site : ℕ → Support n) (score : X → ℕ → ℂ)
    (gold : ℕ → ℝ) (hgold : ∀ i, 0 ≤ gold i) (hs : ∀ x i, ‖score x i‖ ≤ gold i)
    (hcapt : ∀ x, ((taste a γ tag site score).leaf x).captions.Sound a.origins)
    {Z κ : ℝ} (hκ : 0 < κ) (hticket : ∀ v, SumBudget
      (fun i => if v ∈ (tag i).val then Poly.toll w (tag i) * P.p.mass (site i) (gold i) else 0) Z) :
    Nonempty (FullBudget P.p (taste a γ tag site score) w κ (U + Real.exp 1 * C + Z) (D*b/κ)) := by
  obtain ⟨t, h, g, ht, hc, hh, hf, hu⟩ := common a hw hM cap hr γ hγ
  refine ⟨{
    white := fun i => Real.exp 1 * t i
    black := h
    gold := gold
    unitBound := g
    active := fun x => ⟨active a ha (γ x), hcapt x⟩
    radii := hw
    divisor := hκ
    white_nonnegative := fun i => mul_nonneg (Real.exp_nonneg _) (ht i).1
    regular := fun i => ⟨fun x v hv => grain_of_sup ((ht i).2 x v hv)⟩
    regular_law := fun x i => (active a ha (γ x)).regular i
    black_nonnegative := fun i => (hh i.1 i.2).1
    forced := fun x i j z => (hh i j).2 x z
    gold_nonnegative := hgold
    caption := hs
    unit_nonnegative := fun i => (hu i).1
    unit := fun x i => (hu i).2.1 x
    regularTotal := ?_
    forcedTotal := ?_ }⟩
  · intro v
    refine ⟨Real.exp 1 * C, Z, ?_, hticket v, by linarith [(hu v).2.2]⟩
    have hp := budget_scale (Real.exp_nonneg 1) (hc v)
    have he : (fun i => if v ∈ (a.rays i).val then Poly.toll w (a.rays i) *
        P.p.mass (a.support i) (Real.exp 1 * t i) else 0) = fun i => Real.exp 1 *
        (if v ∈ (a.rays i).val then Poly.toll w (a.rays i) * P.p.mass (a.support i) (t i) else 0) := by
      funext i
      split <;> simp_all [BudgetPoint.mass, mul_left_comm]
    exact he.symm ▸ hp
  · intro v
    rw [show κ * (D*b/κ) = D*b by field_simp]
    exact hf v

omit ha hw hM cap hr hγ

/-- An explicit paid radius for the original reader at each marker, including
markers for which the exact reader invoice vanishes. -/
def radius {O : Run G} {p L k : ℕ} {hk : k ≤ L} (I : ActualRunQlocalNativeTuple.Datum O p L k hk V)
    (v : V) : ℝ := (max 1 (ActualOriginalQReaders.readerPrice I v))⁻¹

theorem native {O : Run G} {p L k : ℕ} {hk : k ≤ L} (I : ActualRunQlocalNativeTuple.Datum O p L k hk V)
    (N m : ℕ) (A : Bands (Stock.census V) (O.family.path.rep N p m)) (hA : A.Active)
    {U C D b : ℝ} (hr : A.Radial (fun _ => 1) U C D b)
    (tag : ℕ → (Stock.census V).Mode) (site : ℕ → Support (O.family.side m p))
    (score : IndependentTests (ActualRunQlocalNativeTuple.orbit I) → ℕ → ℂ)
    (gold : ℕ → ℝ) (hgold : ∀ i, 0 ≤ gold i) (hs : ∀ x i, ‖score x i‖ ≤ gold i)
    (hcapt : ∀ x, ((taste A (QLocalNativeReaderPublication.coefficients I) tag site score).leaf x).captions.Sound A.origins)
    {Z κ : ℝ} (hκ : 0 < κ) (hticket : ∀ v, SumBudget
      (fun i => if v ∈ (tag i).val then Poly.toll (radius I) (tag i) *
        (O.family.path.rep N p m).p.mass (site i) (gold i) else 0) Z) :
    Nonempty (FullBudget (O.family.path.rep N p m).p
      (taste A (QLocalNativeReaderPublication.coefficients I) tag site score) (radius I) κ
      (U + Real.exp 1 * C + Z) (D*b/κ)) := by
  let M (v : V) := max 1 (ActualOriginalQReaders.readerPrice I v)
  have hM (v : V) : 0 < M v := zero_lt_one.trans_le (le_max_left _ _)
  exact budget A hA (fun v => inv_pos.mpr (hM v)) (fun v => (hM v).le)
    (fun v => (inv_mul_cancel₀ (hM v).ne').le) hr _
    (fun x i => (QLocalNativeReaderPublication.coefficient_bound I x i).trans (le_max_right _ _))
    tag site score gold hgold hs hcapt hκ hticket

end YM.Integration.QLocalRadialBudget
end
