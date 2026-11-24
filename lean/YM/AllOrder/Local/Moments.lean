import YM.AllOrder.Local.Reserve

/-!
# All orders canonical stationary moments (normalized Hessian)

*Before* cutoff: smear all legs and curvature fluctuations in this single full
Gaussian. Exchange with truncated real integral only through paid tail. In
particular, a tensor used on the correct path chart needn't know `D`.
Multilinear maps store mixed coupling/coordinate derivatives, no partitions
lost by testing only diagonal. Normalization when using `raw` is *after*
setting φ,ψ,ρ,M; these are diagram input functions on any voltage level, not
defined from the Wilson push. This file doesn't yet compare choices of charts
or levels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Vote
open Function Filter Set Finset Matrix Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Gauge Input Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll
open scoped Topology Classical ContDiff ENNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {φ ψ : E × Body ι → ℝ} {ρ : E → Body ι} {M : E → Matrix ι ι ℝ}
variable {j k : ℕ} {p c a u v D C : ℝ}

section tensors
variable (φ ψ ρ M)
/-- Full connected moment inputs, NO `D`. Use one `z` per expectation. -/
def probe (k:ℕ) (z:Body ι) := iteratedFDeriv ℝ k (Real.exp ∘ grace φ ψ ρ M z) 0

def raw (k:ℕ) : Tensor.T (ℝ×E) ℝ k := ∫ z, probe φ ψ ρ M k z ∂(sweep (M 0)⁻¹)

def moment (k:ℕ) : Tensor.T (ℝ×E) ℝ k := (k.factorial:ℝ)⁻¹ • raw φ ψ ρ M k
end tensors

omit [FiniteDimensional ℝ E] in
lemma cover_probe (z:Body ι) :
    JetF (ballots φ ψ ρ M D) k 0 z=(closedBall (0:Body ι) D).indicator (probe φ ψ ρ M k) z := by
  by_cases he:z∈closedBall (0:Body ι) D
  · simp_rw [JetF,ballots,indicator_of_mem he]; rfl
  simp_rw [JetF,ballots,indicator_of_notMem he]; simp

variable (h : Golf φ ψ ρ M j D u v p)
local notation "μ" => sweep (M 0)⁻¹
include h
lemma cut_probe (hk : k ≤ j) :
    let f:= (closedBall (0:Body ι) D).indicator (probe φ ψ ρ M k)
    Integrable f μ ∧ iteratedFDeriv ℝ k (ratify φ ψ ρ M D) 0 = ∫ z, f z ∂μ := by
  intro f; have hx : f= JetF (ballots φ ψ ρ M D) k 0 := funext fun z => (cover_probe z).symm
  rw [hx]; exact (bushes h μ).calls.2 k hk

omit [FiniteDimensional ℝ E] in
lemma m_origin : (M 0).PosDef := (h.gram 0 (norm_zero.trans_lt h.pos)).1

variable (hD : 1 ≤ D)
include hD
lemma probe_measure (hk : k ≤ j) : AEStronglyMeasurable (probe φ ψ ρ M k) μ := by
  let f := probe φ ψ ρ M k
  let Z (m:ℕ) := closedBall (0:Body ι) (D*(1+m))
  let g (m:ℕ):= (Z m).indicator f
  have hh (m:ℕ): Integrable (g m) μ := (cut_probe (golf_high h (show (1:ℝ) ≤ 1 + m from le_add_of_nonneg_right (by positivity))) hk).1
  refine aestronglyMeasurable_of_tendsto_ae (f:=g) atTop (fun n=> (hh n).1) (ae_of_all _ fun z=>?_)
  refine (show Tendsto (fun _:ℕ=> f z) atTop (𝓝 (f z)) from tendsto_const_nhds).congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop (R:=ℝ)|>.eventually_ge_atTop ‖z‖] with n hn
  exact (indicator_of_mem (mem_closedBall_zero_iff.mpr (le_trans hn (show (n:ℝ) ≤ D*(1+n) from (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (by positivity) hD)))) f).symm

variable (hh : ∀ z:ι → ℝ, dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z)
    (hv : (Fintype.card ι:ℝ) ≤ a) (he : Brush j C 1 Real.exp 0)
include hh hv he
lemma raw_h (hk : k ≤ j) : Integrable (probe φ ψ ρ M k) μ ∧
    ‖raw φ ψ ρ M k‖ ≤ clump j (fee j p D) C * volumeCost c ((j+2)*j) a :=
  average (m_origin h).inv hh (probe_measure h hD hk) hv fun z=> (Brush.offer.1 (at_origin_bound h hD C he z)).inside k hk

lemma raw_limit (hk : k ≤ j) (t:ℝ) (ht:0<t) :
    ‖raw φ ψ ρ M k-iteratedFDeriv ℝ k (ratify φ ψ ρ M D) 0‖ ≤ clump j (fee j p D) C *
      (t * (μ).real (closedBall (0:Body ι) D)ᶜ + volumeCost c (2*((j+2)*j)) a/t) := by
  let f:=probe φ ψ ρ M k
  let K:= μ; let Z:=closedBall (0:Body ι) D
  rw [raw,(cut_probe h hk).2, ← integral_sub']
  · have he : f-Z.indicator f=Zᶜ.indicator f:=by ext1 z; by_cases hz:z∈ Z <;> simp [hz]
    rw [he]
    exact lift_tail (m_origin h).inv hh (probe_measure h hD hk) hv (fun z=> (Brush.offer.1 (at_origin_bound h hD C ‹Brush j C 1 Real.exp 0› z)).inside k hk) _ t ht
  · exact (raw_h h hD hh hv he hk).1
  exact (cut_probe h hk).1

lemma moment_limit (hk : k ≤ j) (t:ℝ) (ht:0<t) :
    k.factorial * ‖moment φ ψ ρ M k-Tensor.coeff (ratify φ ψ ρ M D) k 0‖ ≤ clump j (fee j p D) C *
      (t * (μ).real (closedBall (0:Body ι) D)ᶜ + volumeCost c (2*((j+2)*j)) a/t) := by
  unfold moment Tensor.coeff; rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity),← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]; exact raw_limit h hD hh hv he hk _ ht

omit hh hv he h hD in
omit [FiniteDimensional ℝ E] in
@[simp] lemma moment0 [FiniteDimensional ℝ E] (x:ℝ×E) : Tensor.diagonal (moment φ ψ ρ M 0) x= (1:ℝ) := by
  have hh (z:Body ι) : probe φ ψ ρ M 0 z = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => ℝ×E) (1:ℝ) := by
    ext1 v; unfold probe; simp only [iteratedFDeriv_zero_apply, Function.comp_apply]; rw [show grace φ ψ ρ M z 0=0 from zeroC .., Real.exp_zero]; rfl
  unfold Tensor.diagonal moment raw; simp_rw [hh]; rw [integral_const]; simp

end YM.AllOrder.Local.Vote
