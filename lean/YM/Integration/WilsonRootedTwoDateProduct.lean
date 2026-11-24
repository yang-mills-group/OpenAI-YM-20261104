import YM.Integration.QLocalNormalizedQBirth
import YM.Integration.PhysicalWilsonHotAllowance

/-! The genuine two-date product on one physical lower gauge field. The old
complete OPE has been normalized and integrated on that field. The later signed OPE
uses independently prescribed positions and tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct
open Filter Finset MeasureTheory Lattice Wilson RG Marker Precision Exterior Tree Comparison.RG02
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open MergeProof MergeProof.Accent OPE.Therm Push
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G)
local notation "Γ₀" => Stock.census V

/-- Exact original input data at a specified date and periodic cutoff. The forest,
tags, colors and field direction are unrestricted. -/
structure Seed (B : MS.Local.Physical.Deck G) (V : Type) [DecidableEq V] [Fintype V] (N p m : ℕ) where
  below : m<N
  forest : Forest (R.family.path.levels.clock.op m p).ratio
  tag : (R.family.path.levels.clock.op m p).Choices
  colors : Bulk.Colors (Stock.census V) G (R.family.side (m+1) p)
  direction : fieldDir G (R.family.side m p) 1
  labels : V→MS.Rake.Label B
  request : Request V
  schedule : NumericSchedule R.family request
  prescription : MS.Land.Prescription B
  roots : V→Site (R.family.side (m+1) p)
  scale : ℝ
  degree : V→ℕ
  test : IndependentTests (ActualOriginalQPointSetup.request R labels request).tests

namespace Seed
variable {R} {N p m : ℕ} (a : Seed R B V N p m)

def datum : LocalFormal.Datum R.family (Γ₀) := ⟨N,p,m,a.below,a.forest,a.tag,a.colors,a.direction⟩

def numerator (hG : G.Simple) : Config G (R.family.side (m+1) p) → Poly (Γ₀) :=
  ((ActualOriginalQInitialPreparation.input R hG a.labels a.request a.schedule a.datum a.prescription a.roots
    a.scale a.degree).leaf (testInclusion _ a.test)).density

def response (hG : G.Simple) {k : ℕ} (hk : k ≤ m+1) : Config G (R.family.side k p) → Poly (Γ₀) :=
  actualSignedTransport R.family (N:=N) (a.numerator hG) hk

def cost : ℝ := MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R a.labels) (Fintype.card V) 1

def visible : Prop := ActualOriginalQLayout.referenceLevel R a.labels ≤ m+1

theorem point (hG : G.Simple) (ref : a.visible) (w : V→ℝ) (hw : ∀v,0<w v) (hu : ∀v,w v ≤ 1)
    {k : ℕ} (hk : k ≤ m+1) (U : Config G (R.family.side k p)) : Poly.price w (a.response hG hk U) ≤ a.cost :=
  QLocalNormalizedQBirth.transported R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale
    a.degree ref w hw hu a.test hk U

end Seed
variable {R} {N p m : ℕ} (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)

/-- The integrated old response is multiplied by the full fresh response as a
polynomial on this same lower gauge field before the field is integrated. -/
def integrand (U : Config G (R.family.side (m+1) p)) : Poly (Γ₀) :=
  old.response hG (Nat.le_succ (m+1)) U * fresh.response hG (le_refl (m+1)) U

theorem pointwise (ho : old.visible) (hf : fresh.visible) (w : V→ℝ) (hw : ∀v,0<w v) (hu : ∀v,w v ≤ 1)
    (U : Config G (R.family.side (m+1) p)) :
    Poly.price w (integrand old fresh hG U) ≤ old.cost*fresh.cost := by
  have a := old.point hG ho w hw hu (Nat.le_succ (m+1)) U
  have b := fresh.point hG hf w hw hu (le_refl (m+1)) U
  exact (Poly.multiplication hw _ _).trans (mul_le_mul a b (Poly.nonnegative hw _) ((Poly.nonnegative hw _).trans a))

/-- A measurable rough event has its genuine positive marginal probability as a
factor even though both tests in the integrand depend on the same gauge field. -/
theorem measured (ho : old.visible) (hf : fresh.visible) (w : V→ℝ) (hw : ∀v,0<w v) (hu : ∀v,w v ≤ 1)
    (A : Set (Config G (R.family.side (m+1) p))) :
    (∫ U in A, Poly.price w (integrand old fresh hG U) ∂(scene R.family.path N p (m+1))) ≤
      (scene R.family.path N p (m+1)).real A * (old.cost*fresh.cost) := by
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := OPE.Therm.probability (p:=p) R.makes.wilson fresh.below
  have hi : Integrable (fun _ : Config G (R.family.side (m+1) p) => old.cost*fresh.cost) (μ.restrict A) := integrable_const _
  have paid := integral_mono_of_nonneg (μ:=μ.restrict A)
    (ae_of_all _ fun U=>Poly.nonnegative hw (integrand old fresh hG U)) hi
    (ae_of_all _ fun U=>pointwise old fresh hG ho hf w hw hu U)
  exact paid.trans_eq (by rw [setIntegral_const]; rfl)

end YM.Integration.WilsonRootedTwoDateProduct
