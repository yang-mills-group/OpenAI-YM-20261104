import YM.Integration.WilsonKernelCoupling

/-! The original block kernel tested on an arbitrary function of the observed links. -/
noncomputable section
namespace YM.Integration.WilsonKernelCoupling
open YM MeasureTheory Lattice Wilson RG Set
open scoped BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def readLinks (A : Finset (Edge (Site c))) (V : Config G c) (i : A) := V i.val

def branch (A : Finset (Edge (Site c))) (b : ℝ) (Q : Config G c) (x : (i : A) → G.El) : ℝ :=
  ∏ i : A, link S b (Q i.val) (x i)

/-- A local vector-valued mark may couple all retained links. The other links
integrate to exactly one even when the predicted configuration is nonconstant. -/
theorem noise_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Finset (Edge (Site c))) (b : ℝ) (Q : Config G c) (F : ((i : A) → G.El) → E) :
    (∫ V, S.noise b Q V • F (readLinks A V) ∂prior G c) =
      ∫ x, branch S A b Q x • F x ∂(Measure.pi fun _ : A => G.probHaar) := by
  classical
  let C := {i : Edge (Site c) // i ∉ A}
  let μ := Measure.pi fun _ : A => G.probHaar
  let ν := Measure.pi fun _ : C => G.probHaar
  let out (y : C → G.El) := ∏ i : C, link S b (Q i.val) (y i)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge (Site c) => G.El) (· ∈ A)
  have he : MeasurePreserving e (prior G c) (μ.prod ν) := by
    convert! measurePreserving_piEquivPiSubtypeProd
      (fun _ : Edge (Site c) => G.probHaar) (· ∈ A)
  have hl (z : (A → G.El) × (C → G.El)) (i : A) : e.symm z i.val = z.1 i := by
    change (Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ => G.El)).symm z i.val = _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.prop]
  have hr (z : (A → G.El) × (C → G.El)) (i : C) : e.symm z i.val = z.2 i := by
    change (Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ => G.El)).symm z i.val = _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.prop]
  have hnoise (V : Config G c) : S.noise b Q V = ∏ i, link S b (Q i) (V i) := by
    unfold StepData.noise link
    simp only [div_eq_mul_inv]
    exact Finset.prod_congr rfl fun _ _ => mul_comm _ _
  let T (V : Config G c) := S.noise b Q V • F (readLinks A V)
  have hT (z : (A → G.El) × (C → G.El)) :
      T (e.symm z) = out z.2 • (branch S A b Q z.1 • F z.1) := by
    have hread : readLinks A (e.symm z) = z.1 := funext (hl z)
    unfold T
    rw [hread, hnoise, ← Fintype.prod_subtype_mul_prod_subtype (· ∈ A)
      (fun i => link S b (Q i) (e.symm z i)), ← mul_smul]
    simp_rw [hl, hr]
    convert! congrArg (fun r : ℝ => r • F z.1)
      (mul_comm (branch S A b Q z.1) (out z.2)) using 3
    congr 2
    apply Subsingleton.elim
  have hmass : (∫ y, out y ∂ν) = 1 := by
    dsimp only [out, ν]
    rw [integral_fintype_prod_eq_prod]
    simp_rw [link_mass]
    simp
  change (∫ V, T V ∂prior G c) = _
  rw [← (MeasurePreserving.symm e he).integral_comp e.symm.measurableEmbedding T]
  simp_rw [hT]
  rw [← integral_prod_swap]
  change (∫ z, out z.1 • (branch S A b Q z.2 • F z.2) ∂ν.prod μ) = _
  have hx := integral_prod_smul (𝕜 := ℝ) (μ := ν) (ν := μ) out (fun x => branch S A b Q x • F x)
  rw [hmass, one_smul] at hx
  exact hx

private theorem link_cont (b : ℝ) (q : G.El) : Continuous (link S b q) :=
  ((S.penaltyWeight_cont b).comp (continuous_id.mul continuous_const)).div_const _

private theorem branch_cont (A : Finset (Edge (Site c))) (b : ℝ) (Q : Config G c) :
    Continuous (branch S A b Q) :=
  continuous_finsetProd _ fun i _ => (link_cont S b (Q i.val)).comp (continuous_apply i)

private theorem read_cont (A : Finset (Edge (Site c))) :
    Continuous (@readLinks c G A) := continuous_pi fun i => continuous_apply i.val

/-- The signed moment of the complete block kernel on the observed links,
with its original choice weights and true Haar prior. -/
theorem density_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Finset (Edge (Site c))) (b : ℝ) (U : Config G f)
    (F : ((i : A) → G.El) → E) (hF : Continuous F) :
    (∫ V, S.density b U V • F (readLinks A V) ∂prior G c) =
      ∫ x, marginal S A b U x • F x ∂(Measure.pi fun _ : A => G.probHaar) := by
  classical
  letI : IsFiniteMeasure (prior G c) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  let Q := S.prediction U
  have hi t : Integrable (fun V : Config G c => S.likelihood U t •
        (S.noise b (Q t) V • F (readLinks A V))) (prior G c) := by
    have hc : Continuous (fun V : Config G c => S.likelihood U t • (S.noise b (Q t) V • F (readLinks A V))) :=
      continuous_const.smul (((S.noise_cont b).comp (continuous_const.prodMk continuous_id)).smul (hF.comp (read_cont A)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj t : Integrable (fun x : A → G.El => S.likelihood U t •
        (branch S A b (Q t) x • F x)) (Measure.pi fun _ : A => G.probHaar) :=
    (continuous_const.smul ((branch_cont S A b (Q t)).smul hF)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold StepData.density marginal
  simp_rw [Finset.sum_smul, mul_smul]
  change (∫ V, ∑ t, S.likelihood U t • (S.noise b (Q t) V • F (readLinks A V)) ∂prior G c) =
    ∫ x, ∑ t, S.likelihood U t • (branch S A b (Q t) x • F x) ∂(Measure.pi fun _ : A => G.probHaar)
  rw [integral_finsetSum _ (fun t _ => hi t), integral_finsetSum _ (fun t _ => hj t)]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_smul, integral_smul, noise_pairing]

end YM.Integration.WilsonKernelCoupling
