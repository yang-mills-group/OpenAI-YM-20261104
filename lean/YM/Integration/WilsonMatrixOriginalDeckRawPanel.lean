import YM.Integration.WilsonMacroscopicRichOriginalPortfolio
import YM.Integration.WilsonSeparatedOriginalSlabQArms
import YM.Integration.WilsonMatrixOriginalDeckFiledDebit

/-! The complete independently issued finite deck is measured on the very same
Wilson slice, with its own oil coefficients at every lower height. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawPanel
open PhysicalNext.Repeat.Legato Filter Finset MeasureTheory Lattice Wilson RG Source MS MS.Rake MS.Menus MS.Local.Physical
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)

def name (a:Glyph B h) : MS.Rake.Label B := ⟨a.size,a.2⟩

def mass (c:Glyph B h→ℂ) : ℝ := ∑a,‖c a‖

def registered (N per:ℕ) (c:Glyph B h→ℂ) (clock:ℝ) (k:ℕ) (o:Site (R.family.side N per)) (U:Config G (R.family.side N per)) : ℂ :=
  ∑a,c a*WilsonMacroscopicRichOriginalPortfolio.observation R Q N per (name h a) clock k o U

theorem dressed (N per:ℕ) (c:Glyph B h→ℂ) (clock:ℝ) (k:ℕ) (o:Site (R.family.side N per)) (U:Config G (R.family.side N per)) :
    registered R Q h N per c clock k o U=∑a,c a*ActualOriginalCalibratedColumns.weightedObservable
      R B Q (name h a) clock (R.family.side N per) o U k := by
  apply sum_congr rfl
  intro a _
  rw [WilsonMacroscopicRichOriginalPortfolio.observed]

/-- A single purchase precedes both physical cutoffs, each grade and all sites. -/
theorem purchased (K:ℕ) (μ:ℝ) : ∃C:ℝ,0<C ∧ ∃d:ℕ,∀(N per:ℕ)(c:Glyph B h→ℂ)(k:ℕ),k≤K→∀(t:ℝ) o U,
    ‖registered R Q h N per c (μ-t) k o U‖≤ mass h c*(C*(1+‖t‖)^d) := by
  obtain ⟨C,hC,d,all⟩:=WilsonSeparatedOriginalSlabQArms.fixed R Q (name (B:=B) h) K μ
  refine ⟨C,hC,d,?_⟩
  intro N per c k hk t o U
  rw [dressed]
  apply (norm_sum_le _ _).trans
  unfold mass
  rw [Finset.sum_mul]
  apply sum_le_sum
  intro a _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (all a k hk t _ o U) (norm_nonneg _)

variable {E:Type*} [MeasurableSpace E]

def connected (ν:Measure E) (a b:E→ℂ) : ℂ := (∫U,a U*b U ∂ν)-(∫U,a U ∂ν)*(∫U,b U ∂ν)

theorem charge (ν:Measure E) [IsProbabilityMeasure ν] (a b:E→ℂ) {A B:ℝ} (hA:0≤A)
    (left:∀U,‖a U‖≤A) (right:∀U,‖b U‖≤B) : ‖connected ν a b‖≤2*(A*B) := by
  have integrate (f:E→ℂ) (t:ℝ) (hf:∀U,‖f U‖≤t) : ‖∫U,f U ∂ν‖≤t := by
    simpa using norm_integral_le_of_norm_le_const (μ:=ν) (Filter.Eventually.of_forall hf)
  have joined:=integrate (fun U=>a U*b U) (A*B) (fun U=> by rw [norm_mul];exact mul_le_mul (left U) (right U) (norm_nonneg _) hA)
  have singles:=mul_le_mul (integrate a A left) (integrate b B right) (norm_nonneg _) hA
  unfold connected
  apply (norm_sub_le _ _).trans
  rw [norm_mul,two_mul]
  exact add_le_add joined singles

/-- This is the full signed empirical raw-to-raw comparison, including both means, at every positive old law. -/
theorem income (K:ℕ) (μ:ℝ) : ∃C:ℝ,0<C ∧ ∃d:ℕ,∀(N per:ℕ)(ν:Measure (Config G (R.family.side N per))) [IsProbabilityMeasure ν]
    (a b:Glyph B h→ℂ)(k l:ℕ),k≤K→l≤K→∀(t s:ℝ) o x,
    ‖connected ν (registered R Q h N per a (μ-t) k o) (registered R Q h N per b (μ-s) l x)‖ ≤
      2*((mass h a*(C*(1+‖t‖)^d))*(mass h b*(C*(1+‖s‖)^d))) := by
  obtain ⟨C,hC,d,all⟩:=purchased R Q h K μ
  refine ⟨C,hC,d,?_⟩
  intro N per ν _ a b k l hk hl t s o x
  apply charge ν
  · unfold mass;positivity
  · exact all N per a k hk t o
  · exact all N per b l hl s x

end YM.Integration.WilsonMatrixOriginalDeckRawPanel
