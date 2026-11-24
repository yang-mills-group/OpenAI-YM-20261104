import YM.Integration.WilsonRetainedStencilTaylor
import YM.Integration.WilsonCoherentReportingPivot

/-! A single Taylor price, before field normalization or placement, on the
finite source label basis. It multiplies the original absolute coefficient mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedStencilMass
open Function Filter Finset Lattice Wilson Source Labels Dict06.Series Dict06.Wil
open PhysicalNext.Repeat.Legato WilsonRetainedStencilTaylor
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius NNReal
attribute [local instance] Gauge.frobInner

def error (f:ℝ→ℂ) (p:ℕ) (t:ℝ) := f t-∑j∈range (p+1),t^j • ordinary j f

private theorem error_sum {A:Type} [Fintype A] (f:A→ℝ→ℂ) (c:A→ℂ)
    (sm:∀a,ContDiffAt ℝ ω (f a) 0) (p:ℕ) (t:ℝ) :
    error (fun z=>∑a,c a*f a z) p t = ∑a,c a*error (f a) p t := by
  have pull (a:A) (j:ℕ) : ordinary j (fun z=>c a*f a z) = c a*ordinary j (f a) := by
    let L:ℂ→L[ℝ]ℂ:=c a • ContinuousLinearMap.id ℝ ℂ
    exact ordinary_map (f a) j ((sm a).of_le le_top) L
  have row (j:ℕ) : t^j • ordinary j (fun z=>∑ a,c a*f a z) =
      ∑ a,c a*(t^j • ordinary j (f a)) := by
    rw [ordinary_sum univ (fun a z=>c a*f a z) j (fun a _=>contDiffAt_const.mul ((sm a).of_le le_top)),smul_sum]
    apply sum_congr rfl
    intro a _
    rw [pull]
    simp only [Algebra.smul_def]
    ring
  unfold error
  simp_rw [row,mul_sub,mul_sum]
  rw [sum_sub_distrib,sum_comm (s:=range (p+1))]

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)
abbrev Index := WilsonCoherentReportingFrame.Axis R d
def basis (a:Index R d) (i:I) : R.family.label (d i) := Pi.single (a i) 1

private theorem linear {e:ℕ} {F:Frame G e} (S:SectionData F) (y:F.Coeff) (A:Panel S.stencil G) :
    echo S y A = ∑ k,y k*echo S (Pi.single k 1) A := by
  let L:F.Coeff →ₗ[ℂ] ℂ:=(MvPolynomial.aeval (lit A)).toLinearMap.comp S.evalC
  have expansion : y=∑ k,y k • Pi.single k (1:ℂ) := by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  change L y=∑ k,y k*L (Pi.single k 1)
  conv_lhs => rw [expansion,map_sum]
  simp only [map_smul,smul_eq_mul]

theorem expanded (y:∀i,R.family.label (d i)) (x:Fragment R d) :
    material R d y x = ∑ a:Index R d,(∏ i,y i (a i))*material R d (basis R d a) x := by
  unfold material
  rw [prod_congr rfl (fun i (_:i∈(univ:Finset I))=>linear (R.family.localSection (d i)) (y i) (x i)),
    Fintype.prod_sum]
  exact sum_congr rfl fun a _ => prod_mul_distrib

/-- One price buys every set of actual threshold-scaled labels and every
direction, even outside the Gaussian central window. -/
theorem purchased (p:ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ θ:ℝ, ∀ y:∀i,R.family.label (d i),
    ∀ a:Fragment R d, ∀ t:ℝ, 0<t →
      let l:=fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i)
      ‖error (fun u:ℝ=>material R d l (u•a)) p t‖≤
        WilsonCoherentReportingPivot.mass R d θ y*(C*(t*‖a‖)^(p+1)) := by
  classical
  choose fee nonneg bought using fun b:Index R d=> section_price R d (basis R d b) p
  let costs (b:Index R d):ℝ≥0:=⟨fee b,nonneg b⟩
  let C:ℝ:=(univ.sup costs:ℝ≥0)
  refine ⟨C,(univ.sup costs).property,?_⟩
  intro θ y a t ht l
  let f (b:Index R d) (u:ℝ):=material R d (basis R d b) (u•a)
  let c (b:Index R d) := ∏ i,l i (b i)
  have expand:(fun u:ℝ=>material R d l (u•a))=(fun u=>∑b,c b*f b u):=funext fun _=>expanded R d l _
  have sm (b:Index R d):ContDiffAt ℝ ω (f b) 0 :=
    ((smooth R d (basis R d b)).comp (contDiff_id.smul contDiff_const)).contDiffAt
  rw [expand,error_sum f c sm]
  change _≤(∑b,‖c b‖)*(C*(t*‖a‖)^(p+1))
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b _
  have cap : fee b≤C:=le_sup (f:=costs) (mem_univ b)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((bought b a t ht).trans
    (mul_le_mul_of_nonneg_right cap (pow_nonneg (mul_nonneg ht.le (norm_nonneg _)) _))) (norm_nonneg _)

end YM.Integration.WilsonRetainedStencilMass
