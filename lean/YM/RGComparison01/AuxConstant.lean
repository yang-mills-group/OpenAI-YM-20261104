import YM.RGComparison01.AuxGaussian
import YM.RGComparison01.AuxJets

/-!
# Poly-Gaussian cover coefficients vs finite cutoff Taylor jets

`mean` is *not* the Taylor truncation of an asserted uncut integral as a function,
which needn't even be defined in the presence of our local chart. Define polynomial
by integration of the genuine flat jets on all of `Y` with its uncut Gaussian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxConstant
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure Push.AbsoluteSums PhysicalNext.Repeat Lantern
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix Work.G05 AuxGaussian
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} {c P D ε K : ℝ} {k j : ℕ}
local notation "μ₀" => Poll.sweep Q
local notation "Y" => Poll.Body ι
local notation "S" => closedBall (0:Y) D

-- true on every fixed ball
variable (U : Poll.Body ι → E → F)
def truncate (U : Y → E → F) (r : ℝ) (x : E) := (closedBall (0:Y) r).indicator (fun z=> U z x)
omit [DecidableEq ι] in
lemma in_trunc (x : E) (z : Y) (D : ℝ) (i : ℕ) : JetF (truncate U D) i x z=
    (closedBall (0:Y) D).indicator (fun z=> iteratedFDeriv ℝ i (U z) x) z:= by
  by_cases h:z∈closedBall (0:Y) D
  · rw [indicator_of_mem h,JetF, show (fun y=> truncate U D y z)=U z from funext fun _=> indicator_of_mem h _]
  rw [indicator_of_notMem h,JetF, show (fun y=> truncate U D y z)=fun _=>0 from funext fun _=> indicator_of_notMem h _]; simp

abbrev moment (U : Y → E → F) (i : ℕ) (z : Y) := iteratedFDeriv ℝ i (U z) 0
variable [CompleteSpace F]
lemma covered {i : ℕ} (H : ∀ D : ℝ,0≤D → Meristem (truncate U D) 0 (Poll.sweep Q) k) (hi : i≤k) : AEStronglyMeasurable (moment U i) μ₀:= by
  let f (n:ℕ) := JetF (truncate U n) i 0
  have hp (n:ℕ) : AEStronglyMeasurable (f n) μ₀:= ((H n (by positivity)).calls.2 i hi).1.1
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ) hp
  filter_upwards with z
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ‖z‖] with n hn
  unfold f; rw [in_trunc,indicator_of_mem (mem_closedBall_zero_iff.mpr hn)]

-- polynomial in actual joint variables; also export actual integral form and exchange
variable (k)
def mean (Q : Matrix ι ι ℝ) (U : Y → E → F) : E → F :=
    ∑ i∈Finset.range (k+1), Tensor.diagonal (∫ z, Tensor.coeff (U z) i 0 ∂Poll.sweep Q)
omit [CompleteSpace F] in
lemma mean_contDiff (Q : Matrix ι ι ℝ) (p : WithTop ℕ∞) : ContDiff ℝ p (mean k Q U) := by
  rw [show mean k Q U=(fun y=> ∑ i∈Finset.range (k+1), Tensor.diagonal (∫ z, Tensor.coeff (U z) i 0 ∂Poll.sweep Q) y) from funext fun y=> Finset.sum_apply ..]
  exact ContDiff.sum fun i _=>Tensor.diag_smooth _ p
lemma mean_at (hi : ∀ i, i ≤ k → Integrable (moment U i) (Poll.sweep Q)) (x : E) :
    Integrable (fun z=> blockTaylor k (U z) x) μ₀ ∧ mean k Q U x=∫ z, blockTaylor k (U z) x ∂μ₀:= by
  let T (i:ℕ) (z:Y):= Tensor.coeff (U z) i 0
  let w i := ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>E) F (fun _=> x)
  have he i (h:i ≤ k): Integrable (T i) μ₀:= (hi i h).smul ((i.factorial:ℝ)⁻¹)
  have ht i (h:i ∈ Finset.range (k+1)): Integrable (fun z=> w i (T i z)) μ₀ := (w i).integrable_comp (he _ (Nat.le_of_lt_succ (Finset.mem_range.mp h)))
  unfold blockTaylor mean; simp_rw [Finset.sum_apply]; refine ⟨integrable_finsetSum _ ht,?_⟩
  change _ = ∫ z, ∑ i∈Finset.range (k+1),w i (T i z) ∂μ₀
  rw [integral_finsetSum _ ht]; exact Finset.sum_congr rfl (fun i hi=> ((w i).integral_comp_comm (he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))).symm)

section dim
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
lemma jet_reader (x : E) (i j : ℕ) : ∃ v : Tensor.T E F i→L[ℝ]Tensor.T E F j,
    ∀ f: Tensor.T E F i,v f = iteratedFDeriv ℝ j (Tensor.diagonal f) x:= by
  let L : Tensor.T E F i →ₗ[ℝ] Tensor.T E F j :=
    { toFun f := iteratedFDeriv ℝ j (Tensor.diagonal f) x
      map_add' a b:= by change iteratedFDeriv ℝ j (Tensor.diagonal a + Tensor.diagonal b) x=_; exact iteratedFDeriv_add_apply (Tensor.diag_smooth ..|>.contDiffAt) (Tensor.diag_smooth ..|>.contDiffAt)
      map_smul' c a:= by change iteratedFDeriv ℝ j (c • Tensor.diagonal a) x= c • _; exact iteratedFDeriv_const_smul_apply (hf:=(Tensor.diag_smooth a j|>.contDiffAt)) }
  exact ⟨L.toContinuousLinearMap,fun _=>rfl⟩
lemma exchange {j : ℕ} (hi : ∀ i, i ≤ k → Integrable (moment U i) (Poll.sweep Q)) (x : E) :
    iteratedFDeriv ℝ j (mean k Q U) x= ∫ z,iteratedFDeriv ℝ j (blockTaylor k (U z)) x ∂μ₀:= by
  choose L hL using fun i:ℕ=> jet_reader (F:=F) x i j
  let T i (z:Y):= Tensor.coeff (U z) i 0
  let vC:= Finset.range (k+1)
  have he i (h:i ∈ vC) : Integrable (T i) μ₀:= (hi i (Nat.le_of_lt_succ (Finset.mem_range.mp h))).smul ((i.factorial:ℝ)⁻¹)
  unfold mean; rw [iteratedFDeriv_sum_apply (fun _ _=> Tensor.diag_smooth ..|>.contDiffAt)]
  simp_rw [blockTaylor,iteratedFDeriv_sum_apply (x:=x) (fun _ _=> (Tensor.diag_smooth _ _).contDiffAt), ← hL]; change _ = ∫ z, ∑ i∈vC, L i (T i z) ∂μ₀
  rw [integral_finsetSum _ (fun i hi=>(L i).integrable_comp (he i hi))]; exact Finset.sum_congr rfl (fun i hi=> ((L i).integral_comp_comm (he i hi)).symm)
variable {k}
lemma reads {m : ℕ} (hi:m ≤ k) (hv : ∀ i, i ≤ k → Integrable (moment U i) (Poll.sweep Q)) (hh : ∀ z:Y, ContDiffAt ℝ (↑k) (U z) 0) :
    iteratedFDeriv ℝ m (mean k Q U) 0=∫ z,moment U m z ∂μ₀:= by
  rw [exchange k U hv]; exact integral_congr_ae (ae_of_all _ fun z=> blockTaylor_jets (hh z) _ hi)
lemma upgrades (hq : Q.PosDef) (hp : ∀ z : ι → ℝ, dotProduct z (Q*ᵥ z) ≤ c*dotProduct z z) (hK : 0 ≤ K)
    (HU : ∀ D : ℝ,0 ≤ D → Meristem (truncate U D) 0 (Poll.sweep Q) k)
    (HE : ∀ z:Y, Brush k (K*(1+‖z‖)^j) 1 (U z) 0)
    (he : ∫ z in (closedBall (0:Y) D)ᶜ,(1+‖z‖)^j ∂μ₀ ≤ ε) (hD : 0≤D) :
    (∀ i,i ≤ k → Integrable (moment U i) (Poll.sweep Q)) ∧
    Brush k (K*ε) 1 ((fun x=>∫ z, truncate U D x z ∂μ₀) - mean k Q U) 0:= by
  let T (z:Y):= K*(1+‖z‖)^j
  have ht : Integrable T μ₀ := (book j (le_refl (_:ℝ)) hq hp).1.const_mul K
  have hg i (hi:i ≤ k) : Integrable (moment U i) μ₀:= ht.mono' (covered U HU hi)
    (ae_of_all _ fun z=> (Brush.offer.1 (HE z)).2 _ hi)
  have hw:= (HU D hD).calls
  refine ⟨hg, Brush.offer.2 ⟨hw.1.sub (mean_contDiff k U Q k |>.contDiffAt), fun i hi=>?_⟩⟩
  unfold normJ; rw [iteratedFDeriv_sub_apply (hw.1.of_le (by exact_mod_cast hi))
    ((mean_contDiff k U Q i).contDiffAt), (hw.2 i hi).2, reads U hi hg (fun z=> (HE z).smooth),
    show JetF (truncate U D) i 0= _ from funext fun z=> in_trunc U 0 z _ _, integral_indicator measurableSet_closedBall]
  have hf := integral_add_compl (s:=S) measurableSet_closedBall (hg i hi)
  let s:= moment U i
  change ‖(∫ z in S,s z ∂μ₀)-∫ z,s z ∂μ₀‖ ≤ _
  rw [← hf,sub_add_eq_sub_sub, sub_self,zero_sub,norm_neg]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono (μ:=(μ₀).restrict Sᶜ) (hg i hi).norm.integrableOn ht.integrableOn (fun z=> (Brush.offer.1 (HE z)).2 _ hi)).trans ?_)
  rw [show (∫ z in Sᶜ,T z ∂μ₀)=_ from MeasureTheory.integral_const_mul ..]; exact mul_le_mul_of_nonneg_left he hK
end dim
end YM.RGComparison01.AuxConstant
