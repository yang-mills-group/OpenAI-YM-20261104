import YM.Integration.FVA1Physical.Exchange.FibreGibbsPair
import YM.Integration.FVA1Physical.CommonCover.ConditionalCutLoss
import Mathlib.MeasureTheory.Integral.Prod

/-! Compare two draws from two separately normalized laws. The antisymmetric
part sees only the variation of the action difference within the same exterior.
A common proposal or blocking weight may vanish. The bound saturates on the
exceptional region, without any exponential moment of the action error. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory Filter RG FibreMeasure
open scoped Classical BigOperators

def cap (t : ℝ) : ℝ := min 1 (|t|/2)

private theorem capped_odds {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    |a-b| ≤ (a+b)*cap (Real.log a-Real.log b) := by
  have ab : 0<a+b := add_pos ha hb
  have lip := odds_lipschitz (Real.log a-Real.log b) 0
  rw [normalized_odds ha hb] at lip
  have half : gibbsOdds 0=1/2 := by norm_num [gibbsOdds]
  rw [half,sub_zero] at lip
  have rearrange : a/(a+b)-1/2 = (a-b)/(2*(a+b)) := by field_simp; ring
  rw [rearrange,abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) ab)] at lip
  have l := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) ab)).mp lip
  rw [cap,mul_min_of_nonneg _ _ ab.le,mul_one]
  exact le_min (abs_le.mpr ⟨by linarith,by linarith⟩) (l.trans_eq (by ring))

variable {X : Type*}

def cost (u v : X → ℝ) (z : X × X) : ℝ := u z.1*v z.2

def actionBill (u v r : X → ℝ) (z : X × X) : ℝ :=
  (cost u v z+cost v u z)*cap (r z.1-r z.2)

/-- The same kernel multiplies both laws. Arbitrary normalization constants
and all background-only pieces disappear from the action difference. -/
theorem centered_determinant (k a b r : X → ℝ) (kn : ∀x,0≤k x)
    (ap : ∀x,0<a x) (bp : ∀x,0<b x) (anchor : ℝ)
    (same : ∀x,Real.log (a x)-Real.log (b x)=r x+anchor) (z : X × X) :
    let u := fun x => k x*a x
    let v := fun x => k x*b x
    |cost u v z-cost v u z| ≤ actionBill u v r z := by
  intro u v
  let x := z.1; let y := z.2
  have d : Real.log (a x*b y)-Real.log (b x*a y)=r x-r y := by
    rw [Real.log_mul (ap x).ne' (bp y).ne',Real.log_mul (bp x).ne' (ap y).ne']
    linarith only [same x,same y]
  have L := capped_odds (mul_pos (ap x) (bp y)) (mul_pos (bp x) (ap y))
  rw [d] at L
  have scale : 0≤k x*k y := mul_nonneg (kn x) (kn y)
  change |k x*a x*(k y*b y)-k x*b x*(k y*a y)| ≤
    (k x*a x*(k y*b y)+k x*b x*(k y*a y))*cap (r x-r y)
  rw [show k x*a x*(k y*b y)-k x*b x*(k y*a y) = (k x*k y)*(a x*b y-b x*a y) by ring,abs_mul,abs_of_nonneg scale]
  exact (mul_le_mul_of_nonneg_left L scale).trans_eq (by ring)

variable [MeasurableSpace X] {μ : Measure X}

/-- The error bill is integrable for every measurable action residual if
both unnormalized densities have finite mass, independently of its size. -/
theorem integrable_bill {u v r : X → ℝ} (ui : Integrable u μ) (vi : Integrable v μ)
    (un : ∀x,0≤u x) (vn : ∀x,0≤v x) (rm : Measurable r) :
    Integrable (actionBill u v r) (μ.prod μ) := by
  have l : Integrable (cost u v) (μ.prod μ) := ui.mul_prod vi
  have h : Integrable (cost v u) (μ.prod μ) := vi.mul_prod ui
  have cm : Measurable (fun z:X×X => cap (r z.1-r z.2)) := by
    unfold cap; fun_prop
  apply (l.add h).mono' ((l.add h).aestronglyMeasurable.mul cm.aestronglyMeasurable)
  apply Eventually.of_forall; intro z
  have p : 0≤cost u v z+cost v u z := add_nonneg (mul_nonneg (un _) (vn _)) (mul_nonneg (vn _) (un _))
  change ‖(cost u v z+cost v u z)*cap (r z.1-r z.2)‖ ≤ cost u v z+cost v u z
  have cn : 0 ≤ cap (r z.1-r z.2) := le_min zero_le_one (by positivity)
  rw [Real.norm_of_nonneg (mul_nonneg p cn)]
  exact mul_le_of_le_one_right p (min_le_left ..)

end YM.Integration.FVA1Physical.Replica
