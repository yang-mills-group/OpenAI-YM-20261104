import YM.Integration.WilsonRootedTwoDateProduct
import YM.Integration.WilsonRootedPhysicalPointAdmission

/-! Exact fresh Wilson input and true finite marginal moment for both signed sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Precision
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open MergeProof MergeProof.Accent OPE.Therm ActualPolynomialContraction
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
namespace Seed
variable (a : Seed R B V N p m) (hG : G.Simple)
local notation "Q₀" => ActualOriginalQInitialInput.packets R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree
local notation "Y₀" => R.family.path.rep N p (m+1)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p (m+1)
local notation "x₀" => testInclusion _ a.test

/-- The later insertion is exactly the actual unmasked marked Wilson field tested at U. -/
theorem fresh_read (h : a.visible) (U : Config G (R.family.side (m+1) p)) :
    a.response hG (le_refl (m+1)) U=Poly.pass ((Q₀).read (x₀) (g₀) U) := by
  have raw := QLocalNormalizedQBirth.source R hG a.labels a.request a.schedule a.datum a.prescription a.roots
    a.scale a.degree h (x₀) U
  have pos : 0<(Y₀).eval U := Multi.AxisShift.chosen_positive R.makes.wilson a.below U
  rw [response,actualSignedTransport,actualTransport_base R.family R.makes a.below]
  change ((Y₀).eval U)⁻¹ • a.numerator hG U=_
  rw [show a.numerator hG U=(Y₀).eval U • Poly.pass ((Q₀).read (x₀) (g₀) U) from raw,smul_smul,
    inv_mul_cancel₀ pos.ne',one_smul]

/-- The original finite signed numerator is genuinely Haar integrable, and so is
its normalized received density on each positive original marginal. -/
theorem integrable (h : a.visible) {k : ℕ} (hk : k ≤ m+1) :
    Integrable (a.response hG hk) (scene R.family.path N p k) := by
  apply actualSignedTransport_integrable R.family R.makes a.below _ hk
  let M := fun U=>Poly.pass ((Q₀).read (x₀) (g₀) U)
  have vac : Envelope (Y₀).eval := (Y₀).envelope (R.makes.wilson.represents N p (m+1) a.below).good
  have kit := QLocalNormalizedQBirth.unit R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree (g₀)
  have field : Envelope M := kit.multiplier_envelope (fun t U=>NativePaidPacketColors.read_summable kit
    (Currency.g_pos R.makes _ _ _ a.below).ne' t (g₀) U) (x₀)
  have raw : a.numerator hG=fun U=>(Y₀).eval U • M U := funext (QLocalNormalizedQBirth.source R hG a.labels a.request
    a.schedule a.datum a.prescription a.roots a.scale a.degree h (x₀))
  rw [raw]
  obtain ⟨L,bounded⟩ := field.cost
  obtain ⟨K,cap⟩ := vac.cost
  apply Integrable.of_bound (vac.meas.smul field.meas).aestronglyMeasurable (K*L)
  apply ae_of_all
  intro U
  change ‖(Y₀).eval U • M U‖ ≤ K*L
  rw [norm_smul]
  exact mul_le_mul (cap U) (bounded U) (norm_nonneg _) ((norm_nonneg _).trans (cap U))
end Seed

variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)
/-- The nonnegative price appearing in the two-date event bound is genuinely
integrable on the original marginal. -/
theorem price_integrable (ho : old.visible) (hf : fresh.visible) (w : V→ℝ) (hw : ∀v,0<w v) (hu : ∀v,w v ≤ 1) :
    Integrable (fun U=>Poly.price w (integrand old fresh hG U)) (scene R.family.path N p (m+1)) := by
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := OPE.Therm.probability (p:=p) R.makes.wilson fresh.below
  have hA := (old.integrable hG ho (Nat.le_succ (m+1))).aestronglyMeasurable
  have hB := (fresh.integrable hG hf (le_refl (m+1))).aestronglyMeasurable
  have meas : AEStronglyMeasurable (fun U=>Poly.price w (integrand old fresh hG U)) μ := by
    let f (q : (Stock.census V).Mode) (U : Config G (R.family.side (m+1) p)) : ℝ :=
      Poly.toll w q*‖(integrand old fresh hG U).part q‖
    change AEStronglyMeasurable (fun U=>∑q,f q U) μ
    rw [show (fun U=>∑q,f q U)=∑q,f q from funext (fun U=>by simp only [Finset.sum_apply])]
    apply Finset.aestronglyMeasurable_sum
    intro q _
    exact (((Poly.get q).continuous.comp_aestronglyMeasurable (hA.mul hB)).norm).const_mul _
  apply Integrable.of_bound meas (old.cost*fresh.cost)
  apply ae_of_all
  intro U
  rw [Real.norm_of_nonneg (Poly.nonnegative hw _)]
  exact pointwise old fresh hG ho hf w hw hu U

end YM.Integration.WilsonRootedTwoDateProduct
