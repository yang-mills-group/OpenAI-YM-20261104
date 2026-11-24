import YM.Integration.FVA1Physical.CommonCover.ReplicaRoster

/-! Compare different physical and Wilson source tables under different
original and Wilson vacua. The incoming physical sources need only be
integrable with their actual vacuum. This avoids imposing a uniform bound
on the inverse vacuum at a flagged field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory Filter RG Finset
open scoped Classical BigOperators
open private weighted from YM.Integration.FVA1Physical.CommonCover.ReplicaRead
variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

def discrepancy (s : Finset ι) (w : ι → ℝ) (X₀ Y : ι → X → ℂ) (x : X) : ℝ :=
  ∑ i ∈ s,w i*‖X₀ i x-Y i x‖

private theorem same_law {u : X → ℝ} (un : ∀x,0≤u x) (up : 0<∫x,u x ∂μ)
    {F G : X → ℂ} (fi : Integrable (fun x=>u x • F x) μ) (gi : Integrable (fun x=>u x • G x) μ) :
    Integrable (fun x=>u x*‖F x-G x‖) μ ∧
    (∫x,u x ∂μ)*‖FrozenRead.meanOn μ u F-FrozenRead.meanOn μ u G‖ ≤ ∫x,u x*‖F x-G x‖ ∂μ := by
  let d := fun x=>u x • F x-u x • G x
  have fee (x) : ‖d x‖=u x*‖F x-G x‖ := by
    dsimp only [d]; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (un x)]
  have di : Integrable d μ := fi.sub gi
  refine ⟨di.norm.congr (Eventually.of_forall fee),?_⟩
  have eqn : (∫x,d x ∂μ)=(∫x,u x ∂μ) • (FrozenRead.meanOn μ u F-FrozenRead.meanOn μ u G) := by
    dsimp only [d,FrozenRead.meanOn]
    rw [integral_sub fi gi,smul_sub,smul_smul,smul_smul,mul_inv_cancel₀ up.ne',one_smul,one_smul]
  have h := norm_integral_le_integral_norm (μ:=μ) d
  rw [eqn,norm_smul,Real.norm_of_nonneg up.le] at h
  simpa only [fee] using h

theorem different_readings [SFinite μ] (s : Finset ι) (w : ι → ℝ) (wn : ∀i,0≤w i)
    (F G : ι → X → ℂ) (env : ∀i,Envelope (G i)) {k a b r : X → ℝ}
    (kn : ∀x,0≤k x) (ap : ∀x,0<a x) (bp : ∀x,0<b x) (rm : Measurable r)
    (anchor : ℝ) (same : ∀x,Real.log (a x)-Real.log (b x)=r x+anchor) :
    let u := fun x=>k x*a x
    let v := fun x=>k x*b x
    let A := ∫x,u x ∂μ
    let B := ∫x,v x ∂μ
    Integrable u μ → Integrable v μ → 0<A → 0<B →
    (∀i, Integrable (fun x=>u x • F i x) μ) →
    2*A*B*(∑ i ∈ s,w i*‖FrozenRead.meanOn μ u (F i)-FrozenRead.meanOn μ v (G i)‖) ≤
      2*B*(∫x,u x*discrepancy s w F G x ∂μ) +
      ∫z,actionBill u v r z*diameter s w G z ∂μ.prod μ := by
  intro u v A B ui vi up vp fi
  let x := fun i=>FrozenRead.meanOn μ u (F i)
  let y := fun i=>FrozenRead.meanOn μ u (G i)
  let z := fun i=>FrozenRead.meanOn μ v (G i)
  let d := fun i x=>u x*‖F i x-G i x‖
  have one (i) : Integrable (d i) μ ∧ A*‖x i-y i‖≤∫q,d i q ∂μ :=
    same_law (fun q=>mul_nonneg (kn q) (ap q).le) up (fi i) (weighted ui (env i))
  have joint (q) : u q*discrepancy s w F G q=∑i∈s,w i*d i q := by
    rw [discrepancy,Finset.mul_sum];apply sum_congr rfl;intro i _;dsimp [d];ring
  have actual : A*(∑i∈s,w i*‖x i-y i‖) ≤ ∫q,u q*discrepancy s w F G q ∂μ := by
    simp_rw [joint];rw [Finset.mul_sum,integral_finsetSum _ (fun i _=>(one i).1.const_mul (w i))]
    apply sum_le_sum;intro i _;rw [mul_left_comm A,integral_const_mul]
    exact mul_le_mul_of_nonneg_left (one i).2 (wn i)
  have vac := reading_roster s w wn G env kn ap bp rm anchor same ui vi up vp
  have tri : (∑i∈s,w i*‖x i-z i‖) ≤ (∑i∈s,w i*‖x i-y i‖)+(∑i∈s,w i*‖y i-z i‖) := by
    rw [←Finset.sum_add_distrib];apply sum_le_sum;intro i _;rw [←mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub ..) (wn i)
  change 2*A*B*_ ≤ _
  have nonneg : 0≤2*A*B := by positivity
  apply (mul_le_mul_of_nonneg_left tri nonneg).trans
  rw [mul_add,show 2*A*B=2*B*A by ring, mul_assoc (2*B)]
  exact add_le_add (mul_le_mul_of_nonneg_left actual (by positivity)) (by simpa only [mul_right_comm (2:ℝ) B A] using vac)

end YM.Integration.FVA1Physical.Replica
