import YM.Integration.WilsonMatrixOriginalDeckRawPanel
import YM.Integration.WilsonExternalMeshMass
import YM.Integration.WilsonMatrixOriginalSignedReading

/-! The all-grade independent dressed covariance on the actual original signed spatial test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawGrid
open MS.Local.Physical Filter Finset MeasureTheory Table Spec Lattice RG Wilson RGComparison.Core16 MS MS.Rake MS.Menus
open PhysicalNext.Repeat.Legato Next.UVStress Extraction Extraction.Order Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalDeckRawPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)

def observed (T:Test 2) (N per:ℕ) (ν:Measure (Config G (R.family.side N per)))
    (a b:Glyph B h→ℂ) (t s:ℝ) (k l:ℕ) : ℂ :=
  ∑x:Var R.family.S 2 N per,WilsonExternalMeshMass.charge R.family T x*
    connected ν (registered R Q h N per a t k (x 0)) (registered R Q h N per b s l (x 1))

theorem funded (f:Extraction.Order) (K:ℕ) (μ:ℝ) : ∃C:ℝ,0<C ∧ ∃d:ℕ,∀(g:Test 2) {r:ℝ} (hr:0<r) (η:ℝ),0<η →
    ∀ᶠ z:ℕ×ℕ in f.fuse,∀(ν:Measure (Config G (R.family.side z.1 z.2))) [IsProbabilityMeasure ν]
      (a b:Glyph B h→ℂ) (k l:ℕ), k≤K→l≤K→∀t s:ℝ,
      ‖observed R Q h (dilate hr g) z.1 z.2 ν a b (μ-t) (μ-s) k l‖ ≤
        ((∫x,‖(dilate hr g) x‖)+η)*(2*((mass h a*(C*(1+‖t‖)^d))*(mass h b*(C*(1+‖s‖)^d)))) := by
  obtain ⟨C,hC,d,all⟩:=income R Q h K μ
  refine ⟨C,hC,d,?_⟩
  intro g r hr η hp
  let T:=dilate hr g
  filter_upwards [WilsonExternalMeshMass.funded R.family f T T.continuous T.hasCompactSupport hp] with z cash
  intro ν _ a b k l hk hl t s
  let A:=2*((mass h a*(C*(1+‖t‖)^d))*(mass h b*(C*(1+‖s‖)^d)))
  let charge:=fun x:Var R.family.S 2 z.1 z.2=>WilsonExternalMeshMass.charge R.family T x
  calc ‖observed R Q h T z.1 z.2 ν a b (μ-t) (μ-s) k l‖
       ≤ ∑x:Var R.family.S 2 z.1 z.2,‖charge x*connected ν
         (registered R Q h z.1 z.2 a (μ-t) k (x 0)) (registered R Q h z.1 z.2 b (μ-s) l (x 1))‖ := norm_sum_le _ _
       _ ≤ ∑x:Var R.family.S 2 z.1 z.2,‖charge x‖*A := by
         apply sum_le_sum; intro x _; rw [norm_mul]
         exact mul_le_mul_of_nonneg_left (all z.1 z.2 ν a b k l hk hl t s (x 0) (x 1)) (norm_nonneg _)
       _ ≤ ((∫x,‖T x‖)+η)*A := by
         rw [←sum_mul];apply mul_le_mul_of_nonneg_right cash
         unfold A mass;positivity

theorem original (f:Extraction.Order) (K:ℕ) (μ:ℝ) : ∃C:ℝ,0<C ∧ ∃d:ℕ,∀(g:Test 2) {r:ℝ} (hr:0<r),
    ∀ᶠ z:ℕ×ℕ in f.fuse,∀(a b:Glyph B h→ℂ) (k l:ℕ), k≤K→l≤K→∀t s:ℝ,
      ‖observed R Q h (dilate hr g) z.1 z.2 (scene R.family.path z.1 z.2 z.1) a b (μ-t) (μ-s) k l‖ ≤
        ((∫x,‖(dilate hr g) x‖)+1)*(2*((mass h a*(C*(1+‖t‖)^d))*(mass h b*(C*(1+‖s‖)^d)))) := by
  obtain ⟨C,hC,d,all⟩:=funded R Q h f K μ
  refine ⟨C,hC,d,?_⟩
  intro g r hr
  filter_upwards [all g hr 1 zero_lt_one] with z sale
  letI:IsProbabilityMeasure (scene R.family.path z.1 z.2 z.1):=probability R.makes.wilson le_rfl
  exact sale _

end YM.Integration.WilsonMatrixOriginalDeckRawGrid
