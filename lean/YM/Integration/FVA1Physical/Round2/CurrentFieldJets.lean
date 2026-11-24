import YM.Integration.FVA1Physical.Round2.SparseResponseJets
import YM.Integration.FVA1Physical.Round2.StencilExteriorTests

/-! Ordered coarse Lie derivatives of fields inserted at this step, with the
actual inherited interacting vacuum as denominator. Only moving bonds are
charged, and the positions of the field insertions may be independently chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open MeasureTheory Lattice RG YM.Wilson Push.Local Push.Local.Kernel
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Bulk
open scoped BigOperators Classical Topology
variable {G : Gauge} {c f : Side}

theorem current_reading_jets (S : StepData c f) (R : Rep G f) (φ : Config G f → ℝ)
    (branch : S.patch.Branches S.kernel G) (vac : Envelope R.eval)
    (pos : ∀ U, 0 < R.eval U) (field : Envelope φ) {a : ℝ} (cap : ∀ U, |φ U| ≤ a)
    (X : Edges c) (V : Config G c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (l : List (Directions G c)) (hl : l.length ≤ k)
    (support : ∀ v∈l, ∀ e∉X, v e=0) (test : ∀ v∈l, ∀ e∈X, ‖v e‖≤r) :
    ‖leftDerivs (fun W=>expect S R W φ) l V‖ ≤ responsePrice G (R.beta*S.kernel.penalty) k X.card r * a := by
  let T:=φ * R.eval
  let F:=fun U=>(T U:ℂ)
  let E:=fun W=>expect S R W φ
  have hi : Integrable T (prior G f) := (field.mul vac).integrable _
  have hd:=vac.integrable (prior G f)
  have hF : Integrable F (prior G f) := Complex.ofRealCLM.integrable_comp hi
  have bound (U) : ‖F U‖≤a*R.eval U := by
    change ‖((φ U*R.eval U:ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (pos U)]
    exact mul_le_mul_of_nonneg_right (cap U) (pos U).le
  have price:=sparse_response_jets S R.beta X V branch hd hF pos hr bound k l hl support test
  have chart : Chart k E V := by
    have numerator:=smooth_pass S R.beta Finset.univ branch hi V k
    have denominator:=smooth_pass S R.beta Finset.univ branch hd V k
    have positive:=pass_pos S R.beta Finset.univ branch V hd pos
    change ContDiffAt ℝ k ((fun W => S.push R.beta T W / S.push R.beta R.eval W) ∘ increment V) 0
    apply (show Chart k (S.push R.beta T) V from numerator).div
      (show Chart k (S.push R.beta R.eval) V from denominator)
    simpa [Work.G07.at_zero_increment] using (show 0 < S.push R.beta R.eval V from positive).ne'
  have identity : (fun W=> S.push R.beta F W / ((S.push R.beta R.eval W:ℝ):ℂ)) = Complex.ofRealCLM ∘ E := by
    funext W
    change S.push R.beta F W / ((S.push R.beta R.eval W:ℝ):ℂ) = ((S.push R.beta T W / S.push R.beta R.eval W:ℝ):ℂ)
    rw [Complex.ofReal_div]
    congr 1
    simp only [F,StepData.push,Complex.real_smul,← Complex.ofReal_mul,smul_eq_mul,integral_complex_ofReal]
  rw [identity,left_linear Complex.ofRealCLM l chart hl] at price
  simpa only [Complex.ofRealCLM_apply,Complex.norm_real] using price

theorem current_stencil_jets {ι : Type} [Fintype ι] (J : ι → Lamp G) (S : StepData c f)
    (R : Rep G f) (branch : S.patch.Branches S.kernel G) (vac : Envelope R.eval)
    (pos : ∀ U, 0 < R.eval U) (o : ι → Site f) (part : Bool)
    (X : Edges c) (V : Config G c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (l : List (Directions G c)) (hl : l.length ≤ k)
    (support : ∀ v∈l, ∀ e∉X, v e=0) (test : ∀ v∈l, ∀ e∈X, ‖v e‖≤r) :
    ‖leftDerivs (fun W=>expect S R W (fun U=>look part (tally J o U))) l V‖ ≤
      responsePrice G (R.beta*S.kernel.penalty) k X.card r * stencilBound J :=
  current_reading_jets S R _ branch vac pos (Lumen.Planet.havenreal
    ((look part).continuous.comp (Spool.tally_cont J o))) (stencil_bounded J o part)
    X V k hr l hl support test

end YM.Integration.FVA1Physical.Round2.Curvature
